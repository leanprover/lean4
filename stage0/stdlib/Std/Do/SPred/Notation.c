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
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "exists"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__64 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__64_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65_value_aux_0),((lean_object*)&l_Std_Do_term_u231c___u231d___closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(162, 48, 62, 20, 172, 253, 5, 185)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__64_value),LEAN_SCALAR_PTR_LITERAL(119, 199, 194, 26, 176, 147, 16, 83)}};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65_value;
static const lean_string_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "explicitBinders"};
static const lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__66 = (const lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__66_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__67_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__66_value),LEAN_SCALAR_PTR_LITERAL(167, 149, 127, 13, 202, 239, 226, 94)}};
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
lean_object* v___x_496_; lean_object* v_x_498_; lean_object* v_xs_499_; lean_object* v_P_500_; lean_object* v___y_501_; lean_object* v___y_502_; lean_object* v_x_554_; lean_object* v_ty_555_; lean_object* v_xs_556_; lean_object* v_P_557_; lean_object* v___y_558_; lean_object* v___y_559_; lean_object* v_x_616_; lean_object* v_xs_617_; lean_object* v_ty_618_; lean_object* v_ys_619_; lean_object* v_P_620_; lean_object* v___y_621_; lean_object* v___y_622_; lean_object* v___y_685_; lean_object* v___y_686_; lean_object* v___y_687_; lean_object* v___y_688_; lean_object* v___y_689_; lean_object* v___y_690_; lean_object* v___y_691_; uint8_t v___y_692_; lean_object* v___y_693_; lean_object* v___y_694_; lean_object* v___y_695_; lean_object* v___y_696_; lean_object* v___y_697_; lean_object* v___y_707_; lean_object* v___y_708_; lean_object* v___y_709_; lean_object* v___y_710_; uint8_t v___y_711_; lean_object* v___y_712_; lean_object* v___y_713_; lean_object* v___y_714_; uint8_t v___y_715_; lean_object* v___y_716_; lean_object* v___y_717_; lean_object* v___y_718_; lean_object* v___y_719_; lean_object* v___y_728_; lean_object* v___y_729_; uint8_t v___y_730_; lean_object* v___y_731_; lean_object* v___y_732_; uint8_t v___y_733_; uint8_t v___y_734_; lean_object* v___y_735_; lean_object* v___y_736_; lean_object* v___y_737_; lean_object* v___y_738_; lean_object* v___y_739_; lean_object* v___y_740_; lean_object* v___y_747_; lean_object* v___y_748_; lean_object* v___y_749_; lean_object* v___y_750_; lean_object* v___y_751_; lean_object* v___y_752_; lean_object* v___y_753_; lean_object* v___y_754_; lean_object* v___y_755_; lean_object* v___y_756_; lean_object* v___y_757_; lean_object* v___y_758_; lean_object* v___y_759_; lean_object* v___y_770_; lean_object* v___y_771_; lean_object* v___y_772_; uint8_t v___y_773_; lean_object* v___y_774_; lean_object* v___y_775_; lean_object* v___y_776_; lean_object* v___y_777_; lean_object* v___y_778_; lean_object* v___y_779_; uint8_t v___y_780_; lean_object* v___y_789_; lean_object* v___y_790_; lean_object* v___y_791_; lean_object* v___y_792_; uint8_t v___y_793_; lean_object* v___y_794_; lean_object* v___y_795_; lean_object* v___y_796_; uint8_t v___y_797_; lean_object* v___y_798_; uint8_t v___y_799_; lean_object* v___y_807_; lean_object* v___y_808_; lean_object* v___y_809_; lean_object* v___y_810_; lean_object* v___y_811_; lean_object* v___y_812_; lean_object* v___y_813_; lean_object* v___y_814_; uint8_t v___y_815_; lean_object* v___y_816_; lean_object* v___y_817_; uint8_t v___x_826_; 
v___x_496_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__13));
lean_inc(v___x_483_);
v___x_826_ = l_Lean_Syntax_isOfKind(v___x_483_, v___x_496_);
if (v___x_826_ == 0)
{
lean_object* v___x_827_; lean_object* v___x_828_; 
lean_dec(v___x_483_);
v___x_827_ = lean_box(1);
v___x_828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v_a_472_);
return v___x_828_;
}
else
{
lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_829_ = l_Lean_Syntax_getArg(v___x_483_, v___x_482_);
lean_inc(v___x_829_);
v___x_830_ = l_Lean_Syntax_matchesNull(v___x_829_, v___x_482_);
if (v___x_830_ == 0)
{
lean_object* v___x_831_; uint8_t v___x_832_; 
v___x_831_ = l_Lean_Syntax_getNumArgs(v___x_829_);
v___x_832_ = lean_nat_dec_le(v___x_482_, v___x_831_);
if (v___x_832_ == 0)
{
lean_dec(v___x_831_);
lean_dec(v___x_829_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v_x_833_; 
v_x_833_ = l_Lean_Syntax_getArg(v___x_829_, v___x_481_);
if (v___x_830_ == 0)
{
lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_846_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_833_);
v___x_847_ = l_Lean_Syntax_isOfKind(v_x_833_, v___x_846_);
if (v___x_847_ == 0)
{
lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_848_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58));
lean_inc(v_x_833_);
v___x_849_ = l_Lean_Syntax_isOfKind(v_x_833_, v___x_848_);
if (v___x_849_ == 0)
{
lean_dec(v_x_833_);
lean_dec(v___x_831_);
lean_dec(v___x_829_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_850_; uint8_t v___x_851_; 
v___x_850_ = l_Lean_Syntax_getArg(v_x_833_, v___x_482_);
lean_inc(v___x_850_);
v___x_851_ = l_Lean_Syntax_matchesNull(v___x_850_, v___x_482_);
if (v___x_851_ == 0)
{
lean_object* v___x_852_; uint8_t v___x_853_; 
v___x_852_ = l_Lean_Syntax_getNumArgs(v___x_850_);
v___x_853_ = lean_nat_dec_le(v___x_482_, v___x_852_);
if (v___x_853_ == 0)
{
lean_dec(v___x_852_);
lean_dec(v___x_850_);
lean_dec(v_x_833_);
lean_dec(v___x_831_);
lean_dec(v___x_829_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v_x_854_; 
v_x_854_ = l_Lean_Syntax_getArg(v___x_850_, v___x_481_);
if (v___x_851_ == 0)
{
uint8_t v___x_877_; 
lean_inc(v_x_854_);
v___x_877_ = l_Lean_Syntax_isOfKind(v_x_854_, v___x_846_);
if (v___x_877_ == 0)
{
lean_dec(v_x_854_);
lean_dec(v___x_852_);
lean_dec(v___x_850_);
lean_dec(v_x_833_);
lean_dec(v___x_831_);
lean_dec(v___x_829_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
goto v___jp_855_;
}
}
else
{
goto v___jp_855_;
}
v___jp_855_:
{
lean_object* v___x_856_; lean_object* v___x_857_; uint8_t v___x_858_; 
v___x_856_ = lean_unsigned_to_nat(2u);
v___x_857_ = l_Lean_Syntax_getArg(v_x_833_, v___x_856_);
lean_inc(v___x_857_);
v___x_858_ = l_Lean_Syntax_matchesNull(v___x_857_, v___x_856_);
if (v___x_858_ == 0)
{
lean_dec(v___x_857_);
lean_dec(v_x_854_);
lean_dec(v___x_852_);
lean_dec(v___x_850_);
lean_dec(v_x_833_);
lean_dec(v___x_831_);
lean_dec(v___x_829_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_859_; lean_object* v___x_860_; uint8_t v___x_861_; 
v___x_859_ = lean_unsigned_to_nat(3u);
v___x_860_ = l_Lean_Syntax_getArg(v_x_833_, v___x_859_);
lean_dec(v_x_833_);
v___x_861_ = l_Lean_Syntax_matchesNull(v___x_860_, v___x_481_);
if (v___x_861_ == 0)
{
lean_dec(v___x_857_);
lean_dec(v_x_854_);
lean_dec(v___x_852_);
lean_dec(v___x_850_);
lean_dec(v___x_831_);
lean_dec(v___x_829_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_862_; uint8_t v___x_863_; 
v___x_862_ = l_Lean_Syntax_getArg(v___x_483_, v___x_856_);
v___x_863_ = l_Lean_Syntax_matchesNull(v___x_862_, v___x_481_);
if (v___x_863_ == 0)
{
lean_dec(v___x_857_);
lean_dec(v_x_854_);
lean_dec(v___x_852_);
lean_dec(v___x_850_);
lean_dec(v___x_831_);
lean_dec(v___x_829_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v_ty_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v_P_874_; lean_object* v_ys_875_; lean_object* v_xs_876_; 
v___x_864_ = l_Lean_Syntax_getArgs(v___x_850_);
lean_dec(v___x_850_);
v___x_865_ = l_Array_extract___redArg(v___x_864_, v___x_482_, v___x_852_);
lean_dec_ref(v___x_864_);
v_ty_866_ = l_Lean_Syntax_getArg(v___x_857_, v___x_482_);
lean_dec(v___x_857_);
v___x_867_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_868_ = lean_box(2);
v___x_869_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_869_, 0, v___x_868_);
lean_ctor_set(v___x_869_, 1, v___x_867_);
lean_ctor_set(v___x_869_, 2, v___x_865_);
v___x_870_ = lean_unsigned_to_nat(4u);
v___x_871_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_872_ = l_Array_extract___redArg(v___x_871_, v___x_482_, v___x_831_);
lean_dec_ref(v___x_871_);
v___x_873_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_873_, 0, v___x_868_);
lean_ctor_set(v___x_873_, 1, v___x_867_);
lean_ctor_set(v___x_873_, 2, v___x_872_);
v_P_874_ = l_Lean_Syntax_getArg(v___x_483_, v___x_870_);
lean_dec(v___x_483_);
v_ys_875_ = l_Lean_Syntax_getArgs(v___x_873_);
lean_dec_ref_known(v___x_873_, 3);
v_xs_876_ = l_Lean_Syntax_getArgs(v___x_869_);
lean_dec_ref_known(v___x_869_, 3);
v_x_616_ = v_x_854_;
v_xs_617_ = v_xs_876_;
v_ty_618_ = v_ty_866_;
v_ys_619_ = v_ys_875_;
v_P_620_ = v_P_874_;
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
lean_object* v_x_878_; lean_object* v___y_880_; lean_object* v___y_881_; uint8_t v___y_882_; lean_object* v___y_883_; lean_object* v___y_884_; lean_object* v___y_885_; lean_object* v___y_886_; lean_object* v___y_887_; lean_object* v___y_888_; lean_object* v___y_898_; uint8_t v___y_899_; lean_object* v___y_900_; lean_object* v___y_901_; lean_object* v___y_902_; lean_object* v___y_903_; lean_object* v___y_904_; uint8_t v___y_905_; lean_object* v___y_906_; uint8_t v___y_915_; lean_object* v___y_916_; lean_object* v___y_917_; lean_object* v___y_918_; uint8_t v___y_919_; uint8_t v___y_920_; lean_object* v___y_921_; lean_object* v___y_922_; lean_object* v___y_923_; 
v_x_878_ = l_Lean_Syntax_getArg(v___x_850_, v___x_481_);
if (v___x_830_ == 0)
{
uint8_t v___x_975_; 
lean_inc(v_x_878_);
v___x_975_ = l_Lean_Syntax_isOfKind(v_x_878_, v___x_846_);
if (v___x_975_ == 0)
{
lean_object* v___x_976_; uint8_t v___x_977_; 
v___x_976_ = l_Lean_Syntax_getNumArgs(v___x_850_);
v___x_977_ = lean_nat_dec_le(v___x_482_, v___x_976_);
if (v___x_977_ == 0)
{
lean_dec(v___x_976_);
lean_dec(v_x_878_);
lean_dec(v___x_850_);
lean_dec(v_x_833_);
lean_dec(v___x_831_);
lean_dec(v___x_829_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v_P_989_; 
v___x_978_ = lean_unsigned_to_nat(2u);
v___x_979_ = l_Lean_Syntax_getArg(v_x_833_, v___x_978_);
v___x_980_ = lean_unsigned_to_nat(3u);
v___x_981_ = l_Lean_Syntax_getArg(v_x_833_, v___x_980_);
lean_dec(v_x_833_);
v___x_982_ = lean_unsigned_to_nat(4u);
v___x_983_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_984_ = l_Array_extract___redArg(v___x_983_, v___x_482_, v___x_831_);
lean_dec_ref(v___x_983_);
v___x_985_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_986_ = lean_box(2);
v___x_987_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_987_, 0, v___x_986_);
lean_ctor_set(v___x_987_, 1, v___x_985_);
lean_ctor_set(v___x_987_, 2, v___x_984_);
v___x_988_ = l_Lean_Syntax_getArg(v___x_483_, v___x_978_);
v_P_989_ = l_Lean_Syntax_getArg(v___x_483_, v___x_982_);
lean_dec(v___x_483_);
if (v___x_830_ == 0)
{
if (v___x_975_ == 0)
{
lean_dec(v_P_989_);
lean_dec(v___x_988_);
lean_dec_ref_known(v___x_987_, 3);
lean_dec(v___x_981_);
lean_dec(v___x_979_);
lean_dec(v___x_976_);
lean_dec(v_x_878_);
lean_dec(v___x_850_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
goto v___jp_990_;
}
}
else
{
goto v___jp_990_;
}
v___jp_990_:
{
uint8_t v___x_991_; 
lean_inc(v___x_979_);
v___x_991_ = l_Lean_Syntax_matchesNull(v___x_979_, v___x_978_);
if (v___x_991_ == 0)
{
lean_dec(v_P_989_);
lean_dec(v___x_988_);
lean_dec_ref_known(v___x_987_, 3);
lean_dec(v___x_981_);
lean_dec(v___x_979_);
lean_dec(v___x_976_);
lean_dec(v_x_878_);
lean_dec(v___x_850_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
uint8_t v___x_992_; 
v___x_992_ = l_Lean_Syntax_matchesNull(v___x_981_, v___x_481_);
if (v___x_992_ == 0)
{
lean_dec(v_P_989_);
lean_dec(v___x_988_);
lean_dec_ref_known(v___x_987_, 3);
lean_dec(v___x_979_);
lean_dec(v___x_976_);
lean_dec(v_x_878_);
lean_dec(v___x_850_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
uint8_t v___x_993_; 
v___x_993_ = l_Lean_Syntax_matchesNull(v___x_988_, v___x_481_);
if (v___x_993_ == 0)
{
lean_dec(v_P_989_);
lean_dec_ref_known(v___x_987_, 3);
lean_dec(v___x_979_);
lean_dec(v___x_976_);
lean_dec(v_x_878_);
lean_dec(v___x_850_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v_ty_997_; lean_object* v_ys_998_; lean_object* v_xs_999_; 
v___x_994_ = l_Lean_Syntax_getArgs(v___x_850_);
lean_dec(v___x_850_);
v___x_995_ = l_Array_extract___redArg(v___x_994_, v___x_482_, v___x_976_);
lean_dec_ref(v___x_994_);
v___x_996_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_996_, 0, v___x_986_);
lean_ctor_set(v___x_996_, 1, v___x_985_);
lean_ctor_set(v___x_996_, 2, v___x_995_);
v_ty_997_ = l_Lean_Syntax_getArg(v___x_979_, v___x_482_);
lean_dec(v___x_979_);
v_ys_998_ = l_Lean_Syntax_getArgs(v___x_987_);
lean_dec_ref_known(v___x_987_, 3);
v_xs_999_ = l_Lean_Syntax_getArgs(v___x_996_);
lean_dec_ref_known(v___x_996_, 3);
v_x_616_ = v_x_878_;
v_xs_617_ = v_xs_999_;
v_ty_618_ = v_ty_997_;
v_ys_619_ = v_ys_998_;
v_P_620_ = v_P_989_;
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
goto v___jp_929_;
}
}
else
{
goto v___jp_929_;
}
v___jp_879_:
{
if (v___y_882_ == 0)
{
lean_dec(v___y_888_);
lean_dec(v___y_887_);
lean_dec(v___y_886_);
lean_dec(v___y_884_);
lean_dec(v___y_883_);
lean_dec(v___y_880_);
lean_dec(v_x_878_);
lean_dec(v___x_850_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
uint8_t v___x_889_; 
v___x_889_ = l_Lean_Syntax_matchesNull(v___y_880_, v___x_481_);
if (v___x_889_ == 0)
{
lean_dec(v___y_888_);
lean_dec(v___y_887_);
lean_dec(v___y_886_);
lean_dec(v___y_884_);
lean_dec(v___y_883_);
lean_dec(v_x_878_);
lean_dec(v___x_850_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
uint8_t v___x_890_; 
v___x_890_ = l_Lean_Syntax_matchesNull(v___y_888_, v___x_481_);
if (v___x_890_ == 0)
{
lean_dec(v___y_887_);
lean_dec(v___y_886_);
lean_dec(v___y_884_);
lean_dec(v___y_883_);
lean_dec(v_x_878_);
lean_dec(v___x_850_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v_ty_894_; lean_object* v_ys_895_; lean_object* v_xs_896_; 
v___x_891_ = l_Lean_Syntax_getArgs(v___x_850_);
lean_dec(v___x_850_);
v___x_892_ = l_Array_extract___redArg(v___x_891_, v___x_482_, v___y_887_);
lean_dec_ref(v___x_891_);
lean_inc(v___y_881_);
lean_inc(v___y_885_);
v___x_893_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_893_, 0, v___y_885_);
lean_ctor_set(v___x_893_, 1, v___y_881_);
lean_ctor_set(v___x_893_, 2, v___x_892_);
v_ty_894_ = l_Lean_Syntax_getArg(v___y_883_, v___x_482_);
lean_dec(v___y_883_);
v_ys_895_ = l_Lean_Syntax_getArgs(v___y_884_);
lean_dec(v___y_884_);
v_xs_896_ = l_Lean_Syntax_getArgs(v___x_893_);
lean_dec_ref_known(v___x_893_, 3);
v_x_616_ = v_x_878_;
v_xs_617_ = v_xs_896_;
v_ty_618_ = v_ty_894_;
v_ys_619_ = v_ys_895_;
v_P_620_ = v___y_886_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
v___jp_897_:
{
if (v___y_899_ == 0)
{
lean_dec(v___y_906_);
lean_dec(v___y_903_);
lean_dec(v___y_901_);
lean_dec(v___y_900_);
lean_dec(v___y_898_);
lean_dec(v_x_878_);
lean_dec(v___x_850_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___y_905_ == 0)
{
lean_dec(v___y_906_);
lean_dec(v___y_903_);
lean_dec(v___y_901_);
lean_dec(v___y_900_);
lean_dec(v___y_898_);
lean_dec(v_x_878_);
lean_dec(v___x_850_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
uint8_t v___x_907_; 
v___x_907_ = l_Lean_Syntax_matchesNull(v___y_903_, v___x_481_);
if (v___x_907_ == 0)
{
lean_dec(v___y_906_);
lean_dec(v___y_901_);
lean_dec(v___y_900_);
lean_dec(v___y_898_);
lean_dec(v_x_878_);
lean_dec(v___x_850_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v_ty_911_; lean_object* v_ys_912_; lean_object* v_xs_913_; 
v___x_908_ = l_Lean_Syntax_getArgs(v___x_850_);
lean_dec(v___x_850_);
v___x_909_ = l_Array_extract___redArg(v___x_908_, v___x_482_, v___y_901_);
lean_dec_ref(v___x_908_);
lean_inc(v___y_904_);
lean_inc(v___y_902_);
v___x_910_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_910_, 0, v___y_902_);
lean_ctor_set(v___x_910_, 1, v___y_904_);
lean_ctor_set(v___x_910_, 2, v___x_909_);
v_ty_911_ = l_Lean_Syntax_getArg(v___y_900_, v___x_482_);
lean_dec(v___y_900_);
v_ys_912_ = l_Lean_Syntax_getArgs(v___y_906_);
lean_dec(v___y_906_);
v_xs_913_ = l_Lean_Syntax_getArgs(v___x_910_);
lean_dec_ref_known(v___x_910_, 3);
v_x_616_ = v_x_878_;
v_xs_617_ = v_xs_913_;
v_ty_618_ = v_ty_911_;
v_ys_619_ = v_ys_912_;
v_P_620_ = v___y_898_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
v___jp_914_:
{
if (v___y_919_ == 0)
{
lean_dec(v___y_921_);
lean_dec(v___y_918_);
lean_dec(v___y_917_);
lean_dec(v___y_916_);
lean_dec(v_x_878_);
lean_dec(v___x_850_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___y_920_ == 0)
{
lean_dec(v___y_921_);
lean_dec(v___y_918_);
lean_dec(v___y_917_);
lean_dec(v___y_916_);
lean_dec(v_x_878_);
lean_dec(v___x_850_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___y_915_ == 0)
{
lean_dec(v___y_921_);
lean_dec(v___y_918_);
lean_dec(v___y_917_);
lean_dec(v___y_916_);
lean_dec(v_x_878_);
lean_dec(v___x_850_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v_ys_927_; lean_object* v_xs_928_; 
v___x_924_ = l_Lean_Syntax_getArgs(v___x_850_);
lean_dec(v___x_850_);
v___x_925_ = l_Array_extract___redArg(v___x_924_, v___x_482_, v___y_917_);
lean_dec_ref(v___x_924_);
lean_inc(v___y_922_);
lean_inc(v___y_923_);
v___x_926_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_926_, 0, v___y_923_);
lean_ctor_set(v___x_926_, 1, v___y_922_);
lean_ctor_set(v___x_926_, 2, v___x_925_);
v_ys_927_ = l_Lean_Syntax_getArgs(v___y_918_);
lean_dec(v___y_918_);
v_xs_928_ = l_Lean_Syntax_getArgs(v___x_926_);
lean_dec_ref_known(v___x_926_, 3);
v_x_616_ = v_x_878_;
v_xs_617_ = v_xs_928_;
v_ty_618_ = v___y_916_;
v_ys_619_ = v_ys_927_;
v_P_620_ = v___y_921_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
v___jp_929_:
{
lean_object* v___x_930_; lean_object* v___x_931_; uint8_t v___x_932_; 
v___x_930_ = lean_unsigned_to_nat(2u);
v___x_931_ = l_Lean_Syntax_getArg(v_x_833_, v___x_930_);
lean_inc(v___x_931_);
v___x_932_ = l_Lean_Syntax_matchesNull(v___x_931_, v___x_930_);
if (v___x_932_ == 0)
{
lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_933_ = l_Lean_Syntax_getNumArgs(v___x_850_);
v___x_934_ = lean_nat_dec_le(v___x_482_, v___x_933_);
if (v___x_934_ == 0)
{
lean_dec(v___x_933_);
lean_dec(v___x_931_);
lean_dec(v_x_878_);
lean_dec(v___x_850_);
lean_dec(v_x_833_);
lean_dec(v___x_831_);
lean_dec(v___x_829_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v_P_944_; 
v___x_935_ = lean_unsigned_to_nat(3u);
v___x_936_ = l_Lean_Syntax_getArg(v_x_833_, v___x_935_);
lean_dec(v_x_833_);
v___x_937_ = lean_unsigned_to_nat(4u);
v___x_938_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_939_ = l_Array_extract___redArg(v___x_938_, v___x_482_, v___x_831_);
lean_dec_ref(v___x_938_);
v___x_940_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_941_ = lean_box(2);
v___x_942_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_942_, 0, v___x_941_);
lean_ctor_set(v___x_942_, 1, v___x_940_);
lean_ctor_set(v___x_942_, 2, v___x_939_);
v___x_943_ = l_Lean_Syntax_getArg(v___x_483_, v___x_930_);
v_P_944_ = l_Lean_Syntax_getArg(v___x_483_, v___x_937_);
lean_dec(v___x_483_);
if (v___x_932_ == 0)
{
uint8_t v___x_945_; 
lean_inc(v_x_878_);
v___x_945_ = l_Lean_Syntax_isOfKind(v_x_878_, v___x_846_);
if (v___x_945_ == 0)
{
lean_dec(v_P_944_);
lean_dec(v___x_943_);
lean_dec_ref_known(v___x_942_, 3);
lean_dec(v___x_936_);
lean_dec(v___x_933_);
lean_dec(v___x_931_);
lean_dec(v_x_878_);
lean_dec(v___x_850_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
v___y_880_ = v___x_936_;
v___y_881_ = v___x_940_;
v___y_882_ = v___x_932_;
v___y_883_ = v___x_931_;
v___y_884_ = v___x_942_;
v___y_885_ = v___x_941_;
v___y_886_ = v_P_944_;
v___y_887_ = v___x_933_;
v___y_888_ = v___x_943_;
goto v___jp_879_;
}
}
else
{
v___y_880_ = v___x_936_;
v___y_881_ = v___x_940_;
v___y_882_ = v___x_932_;
v___y_883_ = v___x_931_;
v___y_884_ = v___x_942_;
v___y_885_ = v___x_941_;
v___y_886_ = v_P_944_;
v___y_887_ = v___x_933_;
v___y_888_ = v___x_943_;
goto v___jp_879_;
}
}
}
else
{
lean_object* v___x_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v___x_946_ = lean_unsigned_to_nat(3u);
v___x_947_ = l_Lean_Syntax_getArg(v_x_833_, v___x_946_);
lean_dec(v_x_833_);
v___x_948_ = l_Lean_Syntax_matchesNull(v___x_947_, v___x_481_);
if (v___x_948_ == 0)
{
lean_object* v___x_949_; uint8_t v___x_950_; 
v___x_949_ = l_Lean_Syntax_getNumArgs(v___x_850_);
v___x_950_ = lean_nat_dec_le(v___x_482_, v___x_949_);
if (v___x_950_ == 0)
{
lean_dec(v___x_949_);
lean_dec(v___x_931_);
lean_dec(v_x_878_);
lean_dec(v___x_850_);
lean_dec(v___x_831_);
lean_dec(v___x_829_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v_P_958_; 
v___x_951_ = lean_unsigned_to_nat(4u);
v___x_952_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_953_ = l_Array_extract___redArg(v___x_952_, v___x_482_, v___x_831_);
lean_dec_ref(v___x_952_);
v___x_954_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_955_ = lean_box(2);
v___x_956_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_956_, 0, v___x_955_);
lean_ctor_set(v___x_956_, 1, v___x_954_);
lean_ctor_set(v___x_956_, 2, v___x_953_);
v___x_957_ = l_Lean_Syntax_getArg(v___x_483_, v___x_930_);
v_P_958_ = l_Lean_Syntax_getArg(v___x_483_, v___x_951_);
lean_dec(v___x_483_);
if (v___x_948_ == 0)
{
uint8_t v___x_959_; 
lean_inc(v_x_878_);
v___x_959_ = l_Lean_Syntax_isOfKind(v_x_878_, v___x_846_);
if (v___x_959_ == 0)
{
lean_dec(v_P_958_);
lean_dec(v___x_957_);
lean_dec_ref_known(v___x_956_, 3);
lean_dec(v___x_949_);
lean_dec(v___x_931_);
lean_dec(v_x_878_);
lean_dec(v___x_850_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
v___y_898_ = v_P_958_;
v___y_899_ = v___x_932_;
v___y_900_ = v___x_931_;
v___y_901_ = v___x_949_;
v___y_902_ = v___x_955_;
v___y_903_ = v___x_957_;
v___y_904_ = v___x_954_;
v___y_905_ = v___x_948_;
v___y_906_ = v___x_956_;
goto v___jp_897_;
}
}
else
{
v___y_898_ = v_P_958_;
v___y_899_ = v___x_932_;
v___y_900_ = v___x_931_;
v___y_901_ = v___x_949_;
v___y_902_ = v___x_955_;
v___y_903_ = v___x_957_;
v___y_904_ = v___x_954_;
v___y_905_ = v___x_948_;
v___y_906_ = v___x_956_;
goto v___jp_897_;
}
}
}
else
{
lean_object* v_ty_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; uint8_t v___x_968_; 
v_ty_960_ = l_Lean_Syntax_getArg(v___x_931_, v___x_482_);
lean_dec(v___x_931_);
v___x_961_ = lean_unsigned_to_nat(4u);
v___x_962_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_963_ = l_Array_extract___redArg(v___x_962_, v___x_482_, v___x_831_);
lean_dec_ref(v___x_962_);
v___x_964_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_965_ = lean_box(2);
v___x_966_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_966_, 0, v___x_965_);
lean_ctor_set(v___x_966_, 1, v___x_964_);
lean_ctor_set(v___x_966_, 2, v___x_963_);
v___x_967_ = l_Lean_Syntax_getArg(v___x_483_, v___x_930_);
v___x_968_ = l_Lean_Syntax_matchesNull(v___x_967_, v___x_481_);
if (v___x_968_ == 0)
{
lean_object* v___x_969_; uint8_t v___x_970_; 
v___x_969_ = l_Lean_Syntax_getNumArgs(v___x_850_);
v___x_970_ = lean_nat_dec_le(v___x_482_, v___x_969_);
if (v___x_970_ == 0)
{
lean_dec(v___x_969_);
lean_dec_ref_known(v___x_966_, 3);
lean_dec(v_ty_960_);
lean_dec(v_x_878_);
lean_dec(v___x_850_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v_P_971_; 
v_P_971_ = l_Lean_Syntax_getArg(v___x_483_, v___x_961_);
lean_dec(v___x_483_);
if (v___x_968_ == 0)
{
uint8_t v___x_972_; 
lean_inc(v_x_878_);
v___x_972_ = l_Lean_Syntax_isOfKind(v_x_878_, v___x_846_);
if (v___x_972_ == 0)
{
lean_dec(v_P_971_);
lean_dec(v___x_969_);
lean_dec_ref_known(v___x_966_, 3);
lean_dec(v_ty_960_);
lean_dec(v_x_878_);
lean_dec(v___x_850_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
v___y_915_ = v___x_968_;
v___y_916_ = v_ty_960_;
v___y_917_ = v___x_969_;
v___y_918_ = v___x_966_;
v___y_919_ = v___x_932_;
v___y_920_ = v___x_948_;
v___y_921_ = v_P_971_;
v___y_922_ = v___x_964_;
v___y_923_ = v___x_965_;
goto v___jp_914_;
}
}
else
{
v___y_915_ = v___x_968_;
v___y_916_ = v_ty_960_;
v___y_917_ = v___x_969_;
v___y_918_ = v___x_966_;
v___y_919_ = v___x_932_;
v___y_920_ = v___x_948_;
v___y_921_ = v_P_971_;
v___y_922_ = v___x_964_;
v___y_923_ = v___x_965_;
goto v___jp_914_;
}
}
}
else
{
lean_object* v_P_973_; lean_object* v_xs_974_; 
lean_dec(v___x_850_);
v_P_973_ = l_Lean_Syntax_getArg(v___x_483_, v___x_961_);
lean_dec(v___x_483_);
v_xs_974_ = l_Lean_Syntax_getArgs(v___x_966_);
lean_dec_ref_known(v___x_966_, 3);
v_x_554_ = v_x_878_;
v_ty_555_ = v_ty_960_;
v_xs_556_ = v_xs_974_;
v_P_557_ = v_P_973_;
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
goto v___jp_834_;
}
}
else
{
goto v___jp_834_;
}
v___jp_834_:
{
lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_835_ = lean_unsigned_to_nat(2u);
v___x_836_ = l_Lean_Syntax_getArg(v___x_483_, v___x_835_);
v___x_837_ = l_Lean_Syntax_matchesNull(v___x_836_, v___x_481_);
if (v___x_837_ == 0)
{
lean_dec(v_x_833_);
lean_dec(v___x_831_);
lean_dec(v___x_829_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v_P_844_; lean_object* v_xs_845_; 
v___x_838_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_839_ = l_Array_extract___redArg(v___x_838_, v___x_482_, v___x_831_);
lean_dec_ref(v___x_838_);
v___x_840_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_841_ = lean_box(2);
v___x_842_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
lean_ctor_set(v___x_842_, 1, v___x_840_);
lean_ctor_set(v___x_842_, 2, v___x_839_);
v___x_843_ = lean_unsigned_to_nat(4u);
v_P_844_ = l_Lean_Syntax_getArg(v___x_483_, v___x_843_);
lean_dec(v___x_483_);
v_xs_845_ = l_Lean_Syntax_getArgs(v___x_842_);
lean_dec_ref_known(v___x_842_, 3);
v_x_498_ = v_x_833_;
v_xs_499_ = v_xs_845_;
v_P_500_ = v_P_844_;
v___y_501_ = v_a_471_;
v___y_502_ = v_a_472_;
goto v___jp_497_;
}
}
}
}
else
{
lean_object* v_x_1000_; lean_object* v___y_1002_; lean_object* v___y_1003_; lean_object* v___y_1004_; lean_object* v___y_1005_; lean_object* v___y_1006_; lean_object* v___y_1015_; lean_object* v___y_1016_; lean_object* v___y_1017_; lean_object* v___y_1018_; lean_object* v___y_1019_; lean_object* v___y_1020_; lean_object* v___y_1021_; lean_object* v___y_1022_; lean_object* v___y_1042_; lean_object* v___y_1043_; lean_object* v___y_1044_; lean_object* v___y_1045_; lean_object* v___y_1046_; lean_object* v___y_1047_; lean_object* v___y_1048_; lean_object* v___y_1049_; lean_object* v___y_1086_; lean_object* v___y_1087_; uint8_t v___y_1088_; lean_object* v___y_1096_; lean_object* v___y_1097_; lean_object* v___y_1098_; lean_object* v___y_1099_; lean_object* v___y_1100_; lean_object* v___y_1101_; uint8_t v___y_1102_; lean_object* v___y_1103_; lean_object* v___y_1120_; lean_object* v___y_1121_; lean_object* v___y_1122_; lean_object* v___y_1123_; lean_object* v___y_1124_; lean_object* v___y_1125_; uint8_t v___y_1126_; lean_object* v___y_1127_; lean_object* v___x_1156_; uint8_t v___x_1157_; lean_object* v_x_1159_; lean_object* v_ty_1160_; lean_object* v_P_1161_; lean_object* v___y_1162_; lean_object* v___y_1163_; 
v_x_1000_ = l_Lean_Syntax_getArg(v___x_829_, v___x_481_);
v___x_1156_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__62));
lean_inc(v_x_1000_);
v___x_1157_ = l_Lean_Syntax_isOfKind(v_x_1000_, v___x_1156_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1210_; lean_object* v_x_1212_; lean_object* v_xs_1213_; lean_object* v_ty_1214_; lean_object* v_P_1215_; lean_object* v___y_1216_; lean_object* v___y_1217_; lean_object* v_____discr_1277_; lean_object* v_____discr_1278_; lean_object* v___y_1279_; lean_object* v___y_1280_; uint8_t v___x_1305_; 
v___x_1210_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58));
lean_inc(v_x_1000_);
v___x_1305_ = l_Lean_Syntax_isOfKind(v_x_1000_, v___x_1210_);
if (v___x_1305_ == 0)
{
if (v___x_1305_ == 0)
{
lean_object* v___x_1379_; uint8_t v___x_1380_; 
v___x_1379_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1000_);
v___x_1380_ = l_Lean_Syntax_isOfKind(v_x_1000_, v___x_1379_);
if (v___x_1380_ == 0)
{
lean_object* v___x_1381_; uint8_t v___x_1382_; 
v___x_1381_ = l_Lean_Syntax_getNumArgs(v___x_829_);
v___x_1382_ = lean_nat_dec_le(v___x_482_, v___x_1381_);
if (v___x_1382_ == 0)
{
lean_dec(v___x_1381_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; lean_object* v_P_1386_; 
v___x_1383_ = lean_unsigned_to_nat(2u);
v___x_1384_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1383_);
v___x_1385_ = lean_unsigned_to_nat(4u);
v_P_1386_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1385_);
lean_dec(v___x_483_);
if (v___x_1305_ == 0)
{
if (v___x_1380_ == 0)
{
if (v___x_1305_ == 0)
{
lean_dec(v_P_1386_);
lean_dec(v___x_1384_);
lean_dec(v___x_1381_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1395_; lean_object* v___x_1396_; uint8_t v___x_1397_; 
v___x_1395_ = lean_unsigned_to_nat(3u);
v___x_1396_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_482_);
lean_inc(v___x_1396_);
v___x_1397_ = l_Lean_Syntax_matchesNull(v___x_1396_, v___x_482_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; uint8_t v___x_1399_; 
v___x_1398_ = l_Lean_Syntax_getNumArgs(v___x_1396_);
v___x_1399_ = lean_nat_dec_le(v___x_482_, v___x_1398_);
if (v___x_1399_ == 0)
{
lean_dec(v___x_1398_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
lean_dec(v___x_1384_);
lean_dec(v___x_1381_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v_x_1400_; 
v_x_1400_ = l_Lean_Syntax_getArg(v___x_1396_, v___x_481_);
if (v___x_1397_ == 0)
{
uint8_t v___x_1418_; 
lean_inc(v_x_1400_);
v___x_1418_ = l_Lean_Syntax_isOfKind(v_x_1400_, v___x_1379_);
if (v___x_1418_ == 0)
{
lean_dec(v_x_1400_);
lean_dec(v___x_1398_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
lean_dec(v___x_1384_);
lean_dec(v___x_1381_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
goto v___jp_1401_;
}
}
else
{
goto v___jp_1401_;
}
v___jp_1401_:
{
lean_object* v___x_1402_; uint8_t v___x_1403_; 
v___x_1402_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1383_);
lean_inc(v___x_1402_);
v___x_1403_ = l_Lean_Syntax_matchesNull(v___x_1402_, v___x_1383_);
if (v___x_1403_ == 0)
{
lean_dec(v___x_1402_);
lean_dec(v_x_1400_);
lean_dec(v___x_1398_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
lean_dec(v___x_1384_);
lean_dec(v___x_1381_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1404_; uint8_t v___x_1405_; 
v___x_1404_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1395_);
lean_dec(v_x_1000_);
v___x_1405_ = l_Lean_Syntax_matchesNull(v___x_1404_, v___x_481_);
if (v___x_1405_ == 0)
{
lean_dec(v___x_1402_);
lean_dec(v_x_1400_);
lean_dec(v___x_1398_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
lean_dec(v___x_1384_);
lean_dec(v___x_1381_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
uint8_t v___x_1406_; 
v___x_1406_ = l_Lean_Syntax_matchesNull(v___x_1384_, v___x_481_);
if (v___x_1406_ == 0)
{
lean_dec(v___x_1402_);
lean_dec(v_x_1400_);
lean_dec(v___x_1398_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
lean_dec(v___x_1381_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v_ty_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v_ys_1416_; lean_object* v_xs_1417_; 
v___x_1407_ = l_Lean_Syntax_getArgs(v___x_1396_);
lean_dec(v___x_1396_);
v___x_1408_ = l_Array_extract___redArg(v___x_1407_, v___x_482_, v___x_1398_);
lean_dec_ref(v___x_1407_);
v_ty_1409_ = l_Lean_Syntax_getArg(v___x_1402_, v___x_482_);
lean_dec(v___x_1402_);
v___x_1410_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1411_ = lean_box(2);
v___x_1412_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1412_, 0, v___x_1411_);
lean_ctor_set(v___x_1412_, 1, v___x_1410_);
lean_ctor_set(v___x_1412_, 2, v___x_1408_);
v___x_1413_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_1414_ = l_Array_extract___redArg(v___x_1413_, v___x_482_, v___x_1381_);
lean_dec_ref(v___x_1413_);
v___x_1415_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1411_);
lean_ctor_set(v___x_1415_, 1, v___x_1410_);
lean_ctor_set(v___x_1415_, 2, v___x_1414_);
v_ys_1416_ = l_Lean_Syntax_getArgs(v___x_1415_);
lean_dec_ref_known(v___x_1415_, 3);
v_xs_1417_ = l_Lean_Syntax_getArgs(v___x_1412_);
lean_dec_ref_known(v___x_1412_, 3);
v_x_616_ = v_x_1400_;
v_xs_617_ = v_xs_1417_;
v_ty_618_ = v_ty_1409_;
v_ys_619_ = v_ys_1416_;
v_P_620_ = v_P_1386_;
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
lean_object* v_x_1419_; lean_object* v___y_1421_; lean_object* v___y_1422_; uint8_t v___y_1423_; lean_object* v___y_1424_; lean_object* v___y_1425_; lean_object* v___y_1426_; lean_object* v___y_1427_; uint8_t v___y_1437_; lean_object* v___y_1438_; lean_object* v___y_1439_; lean_object* v___y_1440_; lean_object* v___y_1441_; uint8_t v___y_1442_; lean_object* v___y_1443_; uint8_t v___y_1452_; lean_object* v___y_1453_; lean_object* v___y_1454_; lean_object* v___y_1455_; lean_object* v___y_1456_; uint8_t v___y_1457_; uint8_t v___y_1458_; lean_object* v___y_1459_; 
v_x_1419_ = l_Lean_Syntax_getArg(v___x_1396_, v___x_481_);
if (v___x_1305_ == 0)
{
uint8_t v___x_1498_; 
lean_inc(v_x_1419_);
v___x_1498_ = l_Lean_Syntax_isOfKind(v_x_1419_, v___x_1379_);
if (v___x_1498_ == 0)
{
lean_object* v___x_1499_; uint8_t v___x_1500_; 
v___x_1499_ = l_Lean_Syntax_getNumArgs(v___x_1396_);
v___x_1500_ = lean_nat_dec_le(v___x_482_, v___x_1499_);
if (v___x_1500_ == 0)
{
lean_dec(v___x_1499_);
lean_dec(v_x_1419_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
lean_dec(v___x_1384_);
lean_dec(v___x_1381_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1501_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1383_);
v___x_1502_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1395_);
lean_dec(v_x_1000_);
v___x_1503_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_1504_ = l_Array_extract___redArg(v___x_1503_, v___x_482_, v___x_1381_);
lean_dec_ref(v___x_1503_);
v___x_1505_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1506_ = lean_box(2);
v___x_1507_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1506_);
lean_ctor_set(v___x_1507_, 1, v___x_1505_);
lean_ctor_set(v___x_1507_, 2, v___x_1504_);
if (v___x_1305_ == 0)
{
if (v___x_1498_ == 0)
{
lean_dec_ref_known(v___x_1507_, 3);
lean_dec(v___x_1502_);
lean_dec(v___x_1501_);
lean_dec(v___x_1499_);
lean_dec(v_x_1419_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
lean_dec(v___x_1384_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
goto v___jp_1508_;
}
}
else
{
goto v___jp_1508_;
}
v___jp_1508_:
{
uint8_t v___x_1509_; 
lean_inc(v___x_1501_);
v___x_1509_ = l_Lean_Syntax_matchesNull(v___x_1501_, v___x_1383_);
if (v___x_1509_ == 0)
{
lean_dec_ref_known(v___x_1507_, 3);
lean_dec(v___x_1502_);
lean_dec(v___x_1501_);
lean_dec(v___x_1499_);
lean_dec(v_x_1419_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
lean_dec(v___x_1384_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
uint8_t v___x_1510_; 
v___x_1510_ = l_Lean_Syntax_matchesNull(v___x_1502_, v___x_481_);
if (v___x_1510_ == 0)
{
lean_dec_ref_known(v___x_1507_, 3);
lean_dec(v___x_1501_);
lean_dec(v___x_1499_);
lean_dec(v_x_1419_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
lean_dec(v___x_1384_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
uint8_t v___x_1511_; 
v___x_1511_ = l_Lean_Syntax_matchesNull(v___x_1384_, v___x_481_);
if (v___x_1511_ == 0)
{
lean_dec_ref_known(v___x_1507_, 3);
lean_dec(v___x_1501_);
lean_dec(v___x_1499_);
lean_dec(v_x_1419_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; lean_object* v_ty_1515_; lean_object* v_ys_1516_; lean_object* v_xs_1517_; 
v___x_1512_ = l_Lean_Syntax_getArgs(v___x_1396_);
lean_dec(v___x_1396_);
v___x_1513_ = l_Array_extract___redArg(v___x_1512_, v___x_482_, v___x_1499_);
lean_dec_ref(v___x_1512_);
v___x_1514_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1514_, 0, v___x_1506_);
lean_ctor_set(v___x_1514_, 1, v___x_1505_);
lean_ctor_set(v___x_1514_, 2, v___x_1513_);
v_ty_1515_ = l_Lean_Syntax_getArg(v___x_1501_, v___x_482_);
lean_dec(v___x_1501_);
v_ys_1516_ = l_Lean_Syntax_getArgs(v___x_1507_);
lean_dec_ref_known(v___x_1507_, 3);
v_xs_1517_ = l_Lean_Syntax_getArgs(v___x_1514_);
lean_dec_ref_known(v___x_1514_, 3);
v_x_616_ = v_x_1419_;
v_xs_617_ = v_xs_1517_;
v_ty_618_ = v_ty_1515_;
v_ys_619_ = v_ys_1516_;
v_P_620_ = v_P_1386_;
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
goto v___jp_1465_;
}
}
else
{
goto v___jp_1465_;
}
v___jp_1420_:
{
if (v___y_1423_ == 0)
{
lean_dec(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec(v___y_1424_);
lean_dec(v___y_1422_);
lean_dec(v_x_1419_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
lean_dec(v___x_1384_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
uint8_t v___x_1428_; 
v___x_1428_ = l_Lean_Syntax_matchesNull(v___y_1424_, v___x_481_);
if (v___x_1428_ == 0)
{
lean_dec(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec(v___y_1422_);
lean_dec(v_x_1419_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
lean_dec(v___x_1384_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
uint8_t v___x_1429_; 
v___x_1429_ = l_Lean_Syntax_matchesNull(v___x_1384_, v___x_481_);
if (v___x_1429_ == 0)
{
lean_dec(v___y_1427_);
lean_dec(v___y_1426_);
lean_dec(v___y_1422_);
lean_dec(v_x_1419_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v_ty_1433_; lean_object* v_ys_1434_; lean_object* v_xs_1435_; 
v___x_1430_ = l_Lean_Syntax_getArgs(v___x_1396_);
lean_dec(v___x_1396_);
v___x_1431_ = l_Array_extract___redArg(v___x_1430_, v___x_482_, v___y_1427_);
lean_dec_ref(v___x_1430_);
lean_inc(v___y_1421_);
lean_inc(v___y_1425_);
v___x_1432_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1432_, 0, v___y_1425_);
lean_ctor_set(v___x_1432_, 1, v___y_1421_);
lean_ctor_set(v___x_1432_, 2, v___x_1431_);
v_ty_1433_ = l_Lean_Syntax_getArg(v___y_1426_, v___x_482_);
lean_dec(v___y_1426_);
v_ys_1434_ = l_Lean_Syntax_getArgs(v___y_1422_);
lean_dec(v___y_1422_);
v_xs_1435_ = l_Lean_Syntax_getArgs(v___x_1432_);
lean_dec_ref_known(v___x_1432_, 3);
v_x_616_ = v_x_1419_;
v_xs_617_ = v_xs_1435_;
v_ty_618_ = v_ty_1433_;
v_ys_619_ = v_ys_1434_;
v_P_620_ = v_P_1386_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
v___jp_1436_:
{
if (v___y_1442_ == 0)
{
lean_dec(v___y_1443_);
lean_dec(v___y_1441_);
lean_dec(v___y_1439_);
lean_dec(v_x_1419_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
lean_dec(v___x_1384_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___y_1437_ == 0)
{
lean_dec(v___y_1443_);
lean_dec(v___y_1441_);
lean_dec(v___y_1439_);
lean_dec(v_x_1419_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
lean_dec(v___x_1384_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
uint8_t v___x_1444_; 
v___x_1444_ = l_Lean_Syntax_matchesNull(v___x_1384_, v___x_481_);
if (v___x_1444_ == 0)
{
lean_dec(v___y_1443_);
lean_dec(v___y_1441_);
lean_dec(v___y_1439_);
lean_dec(v_x_1419_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; lean_object* v_ty_1448_; lean_object* v_ys_1449_; lean_object* v_xs_1450_; 
v___x_1445_ = l_Lean_Syntax_getArgs(v___x_1396_);
lean_dec(v___x_1396_);
v___x_1446_ = l_Array_extract___redArg(v___x_1445_, v___x_482_, v___y_1439_);
lean_dec_ref(v___x_1445_);
lean_inc(v___y_1440_);
lean_inc(v___y_1438_);
v___x_1447_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1447_, 0, v___y_1438_);
lean_ctor_set(v___x_1447_, 1, v___y_1440_);
lean_ctor_set(v___x_1447_, 2, v___x_1446_);
v_ty_1448_ = l_Lean_Syntax_getArg(v___y_1443_, v___x_482_);
lean_dec(v___y_1443_);
v_ys_1449_ = l_Lean_Syntax_getArgs(v___y_1441_);
lean_dec(v___y_1441_);
v_xs_1450_ = l_Lean_Syntax_getArgs(v___x_1447_);
lean_dec_ref_known(v___x_1447_, 3);
v_x_616_ = v_x_1419_;
v_xs_617_ = v_xs_1450_;
v_ty_618_ = v_ty_1448_;
v_ys_619_ = v_ys_1449_;
v_P_620_ = v_P_1386_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
v___jp_1451_:
{
if (v___y_1457_ == 0)
{
lean_dec(v___y_1459_);
lean_dec(v___y_1455_);
lean_dec(v___y_1453_);
lean_dec(v_x_1419_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___y_1452_ == 0)
{
lean_dec(v___y_1459_);
lean_dec(v___y_1455_);
lean_dec(v___y_1453_);
lean_dec(v_x_1419_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___y_1458_ == 0)
{
lean_dec(v___y_1459_);
lean_dec(v___y_1455_);
lean_dec(v___y_1453_);
lean_dec(v_x_1419_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v_ys_1463_; lean_object* v_xs_1464_; 
v___x_1460_ = l_Lean_Syntax_getArgs(v___x_1396_);
lean_dec(v___x_1396_);
v___x_1461_ = l_Array_extract___redArg(v___x_1460_, v___x_482_, v___y_1459_);
lean_dec_ref(v___x_1460_);
lean_inc(v___y_1456_);
lean_inc(v___y_1454_);
v___x_1462_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1462_, 0, v___y_1454_);
lean_ctor_set(v___x_1462_, 1, v___y_1456_);
lean_ctor_set(v___x_1462_, 2, v___x_1461_);
v_ys_1463_ = l_Lean_Syntax_getArgs(v___y_1455_);
lean_dec(v___y_1455_);
v_xs_1464_ = l_Lean_Syntax_getArgs(v___x_1462_);
lean_dec_ref_known(v___x_1462_, 3);
v_x_616_ = v_x_1419_;
v_xs_617_ = v_xs_1464_;
v_ty_618_ = v___y_1453_;
v_ys_619_ = v_ys_1463_;
v_P_620_ = v_P_1386_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
v___jp_1465_:
{
lean_object* v___x_1466_; uint8_t v___x_1467_; 
v___x_1466_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1383_);
lean_inc(v___x_1466_);
v___x_1467_ = l_Lean_Syntax_matchesNull(v___x_1466_, v___x_1383_);
if (v___x_1467_ == 0)
{
lean_object* v___x_1468_; uint8_t v___x_1469_; 
v___x_1468_ = l_Lean_Syntax_getNumArgs(v___x_1396_);
v___x_1469_ = lean_nat_dec_le(v___x_482_, v___x_1468_);
if (v___x_1469_ == 0)
{
lean_dec(v___x_1468_);
lean_dec(v___x_1466_);
lean_dec(v_x_1419_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
lean_dec(v___x_1384_);
lean_dec(v___x_1381_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1470_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1395_);
lean_dec(v_x_1000_);
v___x_1471_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_1472_ = l_Array_extract___redArg(v___x_1471_, v___x_482_, v___x_1381_);
lean_dec_ref(v___x_1471_);
v___x_1473_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1474_ = lean_box(2);
v___x_1475_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
lean_ctor_set(v___x_1475_, 1, v___x_1473_);
lean_ctor_set(v___x_1475_, 2, v___x_1472_);
if (v___x_1467_ == 0)
{
uint8_t v___x_1476_; 
lean_inc(v_x_1419_);
v___x_1476_ = l_Lean_Syntax_isOfKind(v_x_1419_, v___x_1379_);
if (v___x_1476_ == 0)
{
lean_dec_ref_known(v___x_1475_, 3);
lean_dec(v___x_1470_);
lean_dec(v___x_1468_);
lean_dec(v___x_1466_);
lean_dec(v_x_1419_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
lean_dec(v___x_1384_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
v___y_1421_ = v___x_1473_;
v___y_1422_ = v___x_1475_;
v___y_1423_ = v___x_1467_;
v___y_1424_ = v___x_1470_;
v___y_1425_ = v___x_1474_;
v___y_1426_ = v___x_1466_;
v___y_1427_ = v___x_1468_;
goto v___jp_1420_;
}
}
else
{
v___y_1421_ = v___x_1473_;
v___y_1422_ = v___x_1475_;
v___y_1423_ = v___x_1467_;
v___y_1424_ = v___x_1470_;
v___y_1425_ = v___x_1474_;
v___y_1426_ = v___x_1466_;
v___y_1427_ = v___x_1468_;
goto v___jp_1420_;
}
}
}
else
{
lean_object* v___x_1477_; uint8_t v___x_1478_; 
v___x_1477_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1395_);
lean_dec(v_x_1000_);
v___x_1478_ = l_Lean_Syntax_matchesNull(v___x_1477_, v___x_481_);
if (v___x_1478_ == 0)
{
lean_object* v___x_1479_; uint8_t v___x_1480_; 
v___x_1479_ = l_Lean_Syntax_getNumArgs(v___x_1396_);
v___x_1480_ = lean_nat_dec_le(v___x_482_, v___x_1479_);
if (v___x_1480_ == 0)
{
lean_dec(v___x_1479_);
lean_dec(v___x_1466_);
lean_dec(v_x_1419_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
lean_dec(v___x_1384_);
lean_dec(v___x_1381_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1481_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_1482_ = l_Array_extract___redArg(v___x_1481_, v___x_482_, v___x_1381_);
lean_dec_ref(v___x_1481_);
v___x_1483_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1484_ = lean_box(2);
v___x_1485_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
lean_ctor_set(v___x_1485_, 1, v___x_1483_);
lean_ctor_set(v___x_1485_, 2, v___x_1482_);
if (v___x_1478_ == 0)
{
uint8_t v___x_1486_; 
lean_inc(v_x_1419_);
v___x_1486_ = l_Lean_Syntax_isOfKind(v_x_1419_, v___x_1379_);
if (v___x_1486_ == 0)
{
lean_dec_ref_known(v___x_1485_, 3);
lean_dec(v___x_1479_);
lean_dec(v___x_1466_);
lean_dec(v_x_1419_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
lean_dec(v___x_1384_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
v___y_1437_ = v___x_1478_;
v___y_1438_ = v___x_1484_;
v___y_1439_ = v___x_1479_;
v___y_1440_ = v___x_1483_;
v___y_1441_ = v___x_1485_;
v___y_1442_ = v___x_1467_;
v___y_1443_ = v___x_1466_;
goto v___jp_1436_;
}
}
else
{
v___y_1437_ = v___x_1478_;
v___y_1438_ = v___x_1484_;
v___y_1439_ = v___x_1479_;
v___y_1440_ = v___x_1483_;
v___y_1441_ = v___x_1485_;
v___y_1442_ = v___x_1467_;
v___y_1443_ = v___x_1466_;
goto v___jp_1436_;
}
}
}
else
{
lean_object* v_ty_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1492_; uint8_t v___x_1493_; 
v_ty_1487_ = l_Lean_Syntax_getArg(v___x_1466_, v___x_482_);
lean_dec(v___x_1466_);
v___x_1488_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_1489_ = l_Array_extract___redArg(v___x_1488_, v___x_482_, v___x_1381_);
lean_dec_ref(v___x_1488_);
v___x_1490_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1491_ = lean_box(2);
v___x_1492_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1492_, 0, v___x_1491_);
lean_ctor_set(v___x_1492_, 1, v___x_1490_);
lean_ctor_set(v___x_1492_, 2, v___x_1489_);
v___x_1493_ = l_Lean_Syntax_matchesNull(v___x_1384_, v___x_481_);
if (v___x_1493_ == 0)
{
lean_object* v___x_1494_; uint8_t v___x_1495_; 
v___x_1494_ = l_Lean_Syntax_getNumArgs(v___x_1396_);
v___x_1495_ = lean_nat_dec_le(v___x_482_, v___x_1494_);
if (v___x_1495_ == 0)
{
lean_dec(v___x_1494_);
lean_dec_ref_known(v___x_1492_, 3);
lean_dec(v_ty_1487_);
lean_dec(v_x_1419_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1493_ == 0)
{
uint8_t v___x_1496_; 
lean_inc(v_x_1419_);
v___x_1496_ = l_Lean_Syntax_isOfKind(v_x_1419_, v___x_1379_);
if (v___x_1496_ == 0)
{
lean_dec(v___x_1494_);
lean_dec_ref_known(v___x_1492_, 3);
lean_dec(v_ty_1487_);
lean_dec(v_x_1419_);
lean_dec(v___x_1396_);
lean_dec(v_P_1386_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
v___y_1452_ = v___x_1478_;
v___y_1453_ = v_ty_1487_;
v___y_1454_ = v___x_1491_;
v___y_1455_ = v___x_1492_;
v___y_1456_ = v___x_1490_;
v___y_1457_ = v___x_1467_;
v___y_1458_ = v___x_1493_;
v___y_1459_ = v___x_1494_;
goto v___jp_1451_;
}
}
else
{
v___y_1452_ = v___x_1478_;
v___y_1453_ = v_ty_1487_;
v___y_1454_ = v___x_1491_;
v___y_1455_ = v___x_1492_;
v___y_1456_ = v___x_1490_;
v___y_1457_ = v___x_1467_;
v___y_1458_ = v___x_1493_;
v___y_1459_ = v___x_1494_;
goto v___jp_1451_;
}
}
}
else
{
lean_object* v_xs_1497_; 
lean_dec(v___x_1396_);
v_xs_1497_ = l_Lean_Syntax_getArgs(v___x_1492_);
lean_dec_ref_known(v___x_1492_, 3);
v_x_554_ = v_x_1419_;
v_ty_555_ = v_ty_1487_;
v_xs_556_ = v_xs_1497_;
v_P_557_ = v_P_1386_;
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
goto v___jp_1387_;
}
}
else
{
goto v___jp_1387_;
}
v___jp_1387_:
{
uint8_t v___x_1388_; 
v___x_1388_ = l_Lean_Syntax_matchesNull(v___x_1384_, v___x_481_);
if (v___x_1388_ == 0)
{
lean_dec(v_P_1386_);
lean_dec(v___x_1381_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v_xs_1394_; 
v___x_1389_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_1390_ = l_Array_extract___redArg(v___x_1389_, v___x_482_, v___x_1381_);
lean_dec_ref(v___x_1389_);
v___x_1391_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1392_ = lean_box(2);
v___x_1393_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1393_, 0, v___x_1392_);
lean_ctor_set(v___x_1393_, 1, v___x_1391_);
lean_ctor_set(v___x_1393_, 2, v___x_1390_);
v_xs_1394_ = l_Lean_Syntax_getArgs(v___x_1393_);
lean_dec_ref_known(v___x_1393_, 3);
v_x_498_ = v_x_1000_;
v_xs_499_ = v_xs_1394_;
v_P_500_ = v_P_1386_;
v___y_501_ = v_a_471_;
v___y_502_ = v_a_472_;
goto v___jp_497_;
}
}
}
}
else
{
goto v___jp_1306_;
}
}
else
{
goto v___jp_1306_;
}
}
else
{
lean_object* v___x_1518_; lean_object* v___x_1519_; uint8_t v___x_1520_; 
v___x_1518_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_482_);
v___x_1519_ = l_Lean_Syntax_getNumArgs(v___x_1518_);
v___x_1520_ = lean_nat_dec_le(v___x_482_, v___x_1519_);
if (v___x_1520_ == 0)
{
uint8_t v___x_1521_; 
lean_inc(v___x_1518_);
v___x_1521_ = l_Lean_Syntax_matchesNull(v___x_1518_, v___x_482_);
if (v___x_1521_ == 0)
{
lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; 
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v___x_1522_ = lean_unsigned_to_nat(2u);
v___x_1523_ = lean_unsigned_to_nat(4u);
v___x_1524_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1522_);
v___x_1525_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1523_);
lean_dec(v___x_483_);
v_____discr_1277_ = v___x_1524_;
v_____discr_1278_ = v___x_1525_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v_x_1526_; lean_object* v___x_1527_; uint8_t v___x_1528_; 
v_x_1526_ = l_Lean_Syntax_getArg(v___x_1518_, v___x_481_);
v___x_1527_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1526_);
v___x_1528_ = l_Lean_Syntax_isOfKind(v_x_1526_, v___x_1527_);
if (v___x_1528_ == 0)
{
lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v_P_1532_; 
v___x_1529_ = lean_unsigned_to_nat(2u);
v___x_1530_ = lean_unsigned_to_nat(4u);
v___x_1531_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1529_);
v_P_1532_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1530_);
lean_dec(v___x_483_);
if (v___x_1520_ == 0)
{
lean_dec(v_x_1526_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1531_;
v_____discr_1278_ = v_P_1532_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1528_ == 0)
{
lean_dec(v_x_1526_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1531_;
v_____discr_1278_ = v_P_1532_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1533_; uint8_t v___x_1534_; 
v___x_1533_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1529_);
lean_inc(v___x_1533_);
v___x_1534_ = l_Lean_Syntax_matchesNull(v___x_1533_, v___x_1529_);
if (v___x_1534_ == 0)
{
lean_dec(v___x_1533_);
lean_dec(v_x_1526_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1531_;
v_____discr_1278_ = v_P_1532_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; uint8_t v___x_1537_; 
v___x_1535_ = lean_unsigned_to_nat(3u);
v___x_1536_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1535_);
v___x_1537_ = l_Lean_Syntax_matchesNull(v___x_1536_, v___x_481_);
if (v___x_1537_ == 0)
{
lean_dec(v___x_1533_);
lean_dec(v_x_1526_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1531_;
v_____discr_1278_ = v_P_1532_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1538_; 
lean_inc(v___x_1531_);
v___x_1538_ = l_Lean_Syntax_matchesNull(v___x_1531_, v___x_481_);
if (v___x_1538_ == 0)
{
lean_dec(v___x_1533_);
lean_dec(v_x_1526_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1531_;
v_____discr_1278_ = v_P_1532_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v_ty_1544_; lean_object* v_xs_1545_; 
lean_dec(v___x_1531_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1539_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1540_ = l_Array_extract___redArg(v___x_1539_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1539_);
v___x_1541_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1542_ = lean_box(2);
v___x_1543_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1543_, 0, v___x_1542_);
lean_ctor_set(v___x_1543_, 1, v___x_1541_);
lean_ctor_set(v___x_1543_, 2, v___x_1540_);
v_ty_1544_ = l_Lean_Syntax_getArg(v___x_1533_, v___x_482_);
lean_dec(v___x_1533_);
v_xs_1545_ = l_Lean_Syntax_getArgs(v___x_1543_);
lean_dec_ref_known(v___x_1543_, 3);
v_x_1212_ = v_x_1526_;
v_xs_1213_ = v_xs_1545_;
v_ty_1214_ = v_ty_1544_;
v_P_1215_ = v_P_1532_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
}
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1546_ = lean_unsigned_to_nat(2u);
v___x_1547_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1546_);
lean_inc(v___x_1547_);
v___x_1548_ = l_Lean_Syntax_matchesNull(v___x_1547_, v___x_1546_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v_P_1551_; 
v___x_1549_ = lean_unsigned_to_nat(4u);
v___x_1550_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1546_);
v_P_1551_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1549_);
lean_dec(v___x_483_);
if (v___x_1520_ == 0)
{
lean_dec(v___x_1547_);
lean_dec(v_x_1526_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1550_;
v_____discr_1278_ = v_P_1551_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1552_ = lean_unsigned_to_nat(3u);
v___x_1553_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1552_);
if (v___x_1548_ == 0)
{
if (v___x_1528_ == 0)
{
lean_dec(v___x_1553_);
lean_dec(v___x_1547_);
lean_dec(v_x_1526_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1550_;
v_____discr_1278_ = v_P_1551_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
goto v___jp_1554_;
}
}
else
{
goto v___jp_1554_;
}
v___jp_1554_:
{
if (v___x_1548_ == 0)
{
lean_dec(v___x_1553_);
lean_dec(v___x_1547_);
lean_dec(v_x_1526_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1550_;
v_____discr_1278_ = v_P_1551_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1555_; 
v___x_1555_ = l_Lean_Syntax_matchesNull(v___x_1553_, v___x_481_);
if (v___x_1555_ == 0)
{
lean_dec(v___x_1547_);
lean_dec(v_x_1526_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1550_;
v_____discr_1278_ = v_P_1551_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1556_; 
lean_inc(v___x_1550_);
v___x_1556_ = l_Lean_Syntax_matchesNull(v___x_1550_, v___x_481_);
if (v___x_1556_ == 0)
{
lean_dec(v___x_1547_);
lean_dec(v_x_1526_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1550_;
v_____discr_1278_ = v_P_1551_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; lean_object* v_ty_1562_; lean_object* v_xs_1563_; 
lean_dec(v___x_1550_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1557_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1558_ = l_Array_extract___redArg(v___x_1557_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1557_);
v___x_1559_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1560_ = lean_box(2);
v___x_1561_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1561_, 0, v___x_1560_);
lean_ctor_set(v___x_1561_, 1, v___x_1559_);
lean_ctor_set(v___x_1561_, 2, v___x_1558_);
v_ty_1562_ = l_Lean_Syntax_getArg(v___x_1547_, v___x_482_);
lean_dec(v___x_1547_);
v_xs_1563_ = l_Lean_Syntax_getArgs(v___x_1561_);
lean_dec_ref_known(v___x_1561_, 3);
v_x_1212_ = v_x_1526_;
v_xs_1213_ = v_xs_1563_;
v_ty_1214_ = v_ty_1562_;
v_P_1215_ = v_P_1551_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
}
}
else
{
lean_object* v___x_1564_; lean_object* v___x_1565_; uint8_t v___x_1566_; 
v___x_1564_ = lean_unsigned_to_nat(3u);
v___x_1565_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1564_);
v___x_1566_ = l_Lean_Syntax_matchesNull(v___x_1565_, v___x_481_);
if (v___x_1566_ == 0)
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v_P_1569_; 
v___x_1567_ = lean_unsigned_to_nat(4u);
v___x_1568_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1546_);
v_P_1569_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1567_);
lean_dec(v___x_483_);
if (v___x_1520_ == 0)
{
lean_dec(v___x_1547_);
lean_dec(v_x_1526_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1568_;
v_____discr_1278_ = v_P_1569_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1566_ == 0)
{
if (v___x_1528_ == 0)
{
lean_dec(v___x_1547_);
lean_dec(v_x_1526_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1568_;
v_____discr_1278_ = v_P_1569_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
goto v___jp_1570_;
}
}
else
{
goto v___jp_1570_;
}
}
v___jp_1570_:
{
if (v___x_1548_ == 0)
{
lean_dec(v___x_1547_);
lean_dec(v_x_1526_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1568_;
v_____discr_1278_ = v_P_1569_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1566_ == 0)
{
lean_dec(v___x_1547_);
lean_dec(v_x_1526_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1568_;
v_____discr_1278_ = v_P_1569_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1571_; 
lean_inc(v___x_1568_);
v___x_1571_ = l_Lean_Syntax_matchesNull(v___x_1568_, v___x_481_);
if (v___x_1571_ == 0)
{
lean_dec(v___x_1547_);
lean_dec(v_x_1526_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1568_;
v_____discr_1278_ = v_P_1569_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v_ty_1577_; lean_object* v_xs_1578_; 
lean_dec(v___x_1568_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1572_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1573_ = l_Array_extract___redArg(v___x_1572_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1572_);
v___x_1574_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1575_ = lean_box(2);
v___x_1576_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1576_, 0, v___x_1575_);
lean_ctor_set(v___x_1576_, 1, v___x_1574_);
lean_ctor_set(v___x_1576_, 2, v___x_1573_);
v_ty_1577_ = l_Lean_Syntax_getArg(v___x_1547_, v___x_482_);
lean_dec(v___x_1547_);
v_xs_1578_ = l_Lean_Syntax_getArgs(v___x_1576_);
lean_dec_ref_known(v___x_1576_, 3);
v_x_1212_ = v_x_1526_;
v_xs_1213_ = v_xs_1578_;
v_ty_1214_ = v_ty_1577_;
v_P_1215_ = v_P_1569_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
}
else
{
lean_object* v___x_1579_; lean_object* v___x_1580_; uint8_t v___x_1581_; 
v___x_1579_ = lean_unsigned_to_nat(4u);
v___x_1580_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1546_);
lean_inc(v___x_1580_);
v___x_1581_ = l_Lean_Syntax_matchesNull(v___x_1580_, v___x_481_);
if (v___x_1581_ == 0)
{
lean_object* v_P_1582_; 
v_P_1582_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1579_);
lean_dec(v___x_483_);
if (v___x_1520_ == 0)
{
lean_dec(v___x_1547_);
lean_dec(v_x_1526_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1580_;
v_____discr_1278_ = v_P_1582_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1581_ == 0)
{
if (v___x_1528_ == 0)
{
lean_dec(v___x_1547_);
lean_dec(v_x_1526_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1580_;
v_____discr_1278_ = v_P_1582_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
goto v___jp_1583_;
}
}
else
{
goto v___jp_1583_;
}
}
v___jp_1583_:
{
if (v___x_1548_ == 0)
{
lean_dec(v___x_1547_);
lean_dec(v_x_1526_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1580_;
v_____discr_1278_ = v_P_1582_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1566_ == 0)
{
lean_dec(v___x_1547_);
lean_dec(v_x_1526_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1580_;
v_____discr_1278_ = v_P_1582_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1581_ == 0)
{
lean_dec(v___x_1547_);
lean_dec(v_x_1526_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1580_;
v_____discr_1278_ = v_P_1582_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v_ty_1589_; lean_object* v_xs_1590_; 
lean_dec(v___x_1580_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1584_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1585_ = l_Array_extract___redArg(v___x_1584_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1584_);
v___x_1586_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1587_ = lean_box(2);
v___x_1588_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1587_);
lean_ctor_set(v___x_1588_, 1, v___x_1586_);
lean_ctor_set(v___x_1588_, 2, v___x_1585_);
v_ty_1589_ = l_Lean_Syntax_getArg(v___x_1547_, v___x_482_);
lean_dec(v___x_1547_);
v_xs_1590_ = l_Lean_Syntax_getArgs(v___x_1588_);
lean_dec_ref_known(v___x_1588_, 3);
v_x_1212_ = v_x_1526_;
v_xs_1213_ = v_xs_1590_;
v_ty_1214_ = v_ty_1589_;
v_P_1215_ = v_P_1582_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
}
else
{
lean_object* v_ty_1591_; lean_object* v_P_1592_; 
lean_dec(v___x_1580_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v_ty_1591_ = l_Lean_Syntax_getArg(v___x_1547_, v___x_482_);
lean_dec(v___x_1547_);
v_P_1592_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1579_);
lean_dec(v___x_483_);
v_x_1159_ = v_x_1526_;
v_ty_1160_ = v_ty_1591_;
v_P_1161_ = v_P_1592_;
v___y_1162_ = v_a_471_;
v___y_1163_ = v_a_472_;
goto v___jp_1158_;
}
}
}
}
}
}
else
{
lean_object* v_x_1593_; uint8_t v___x_1594_; 
v_x_1593_ = l_Lean_Syntax_getArg(v___x_1518_, v___x_481_);
lean_inc(v_x_1593_);
v___x_1594_ = l_Lean_Syntax_isOfKind(v_x_1593_, v___x_1156_);
if (v___x_1594_ == 0)
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v_P_1601_; uint8_t v___y_1614_; uint8_t v___y_1625_; uint8_t v___y_1626_; uint8_t v___y_1636_; uint8_t v___y_1637_; uint8_t v___y_1638_; uint8_t v___x_1668_; 
v___x_1595_ = lean_unsigned_to_nat(2u);
v___x_1596_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1595_);
v___x_1597_ = lean_unsigned_to_nat(3u);
v___x_1598_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1597_);
v___x_1599_ = lean_unsigned_to_nat(4u);
v___x_1600_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1595_);
v_P_1601_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1599_);
lean_dec(v___x_483_);
lean_inc(v___x_1518_);
v___x_1668_ = l_Lean_Syntax_matchesNull(v___x_1518_, v___x_482_);
if (v___x_1668_ == 0)
{
if (v___x_1520_ == 0)
{
lean_dec(v___x_1598_);
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; uint8_t v___x_1670_; 
v___x_1669_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1593_);
v___x_1670_ = l_Lean_Syntax_isOfKind(v_x_1593_, v___x_1669_);
if (v___x_1670_ == 0)
{
lean_dec(v___x_1598_);
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
goto v___jp_1657_;
}
}
else
{
goto v___jp_1657_;
}
}
}
else
{
if (v___x_1594_ == 0)
{
lean_object* v___x_1671_; uint8_t v___x_1672_; 
v___x_1671_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1593_);
v___x_1672_ = l_Lean_Syntax_isOfKind(v_x_1593_, v___x_1671_);
if (v___x_1672_ == 0)
{
if (v___x_1520_ == 0)
{
lean_dec(v___x_1598_);
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1594_ == 0)
{
if (v___x_1672_ == 0)
{
lean_dec(v___x_1598_);
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
goto v___jp_1602_;
}
}
else
{
goto v___jp_1602_;
}
}
}
else
{
goto v___jp_1646_;
}
}
else
{
goto v___jp_1646_;
}
}
v___jp_1602_:
{
uint8_t v___x_1603_; 
lean_inc(v___x_1596_);
v___x_1603_ = l_Lean_Syntax_matchesNull(v___x_1596_, v___x_1595_);
if (v___x_1603_ == 0)
{
lean_dec(v___x_1598_);
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1604_; 
v___x_1604_ = l_Lean_Syntax_matchesNull(v___x_1598_, v___x_481_);
if (v___x_1604_ == 0)
{
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1605_; 
lean_inc(v___x_1600_);
v___x_1605_ = l_Lean_Syntax_matchesNull(v___x_1600_, v___x_481_);
if (v___x_1605_ == 0)
{
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v_ty_1611_; lean_object* v_xs_1612_; 
lean_dec(v___x_1600_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1606_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1607_ = l_Array_extract___redArg(v___x_1606_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1606_);
v___x_1608_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1609_ = lean_box(2);
v___x_1610_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1610_, 0, v___x_1609_);
lean_ctor_set(v___x_1610_, 1, v___x_1608_);
lean_ctor_set(v___x_1610_, 2, v___x_1607_);
v_ty_1611_ = l_Lean_Syntax_getArg(v___x_1596_, v___x_482_);
lean_dec(v___x_1596_);
v_xs_1612_ = l_Lean_Syntax_getArgs(v___x_1610_);
lean_dec_ref_known(v___x_1610_, 3);
v_x_1212_ = v_x_1593_;
v_xs_1213_ = v_xs_1612_;
v_ty_1214_ = v_ty_1611_;
v_P_1215_ = v_P_1601_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
v___jp_1613_:
{
if (v___y_1614_ == 0)
{
lean_dec(v___x_1598_);
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1615_; 
v___x_1615_ = l_Lean_Syntax_matchesNull(v___x_1598_, v___x_481_);
if (v___x_1615_ == 0)
{
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1616_; 
lean_inc(v___x_1600_);
v___x_1616_ = l_Lean_Syntax_matchesNull(v___x_1600_, v___x_481_);
if (v___x_1616_ == 0)
{
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v_ty_1622_; lean_object* v_xs_1623_; 
lean_dec(v___x_1600_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1617_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1618_ = l_Array_extract___redArg(v___x_1617_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1617_);
v___x_1619_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1620_ = lean_box(2);
v___x_1621_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1621_, 0, v___x_1620_);
lean_ctor_set(v___x_1621_, 1, v___x_1619_);
lean_ctor_set(v___x_1621_, 2, v___x_1618_);
v_ty_1622_ = l_Lean_Syntax_getArg(v___x_1596_, v___x_482_);
lean_dec(v___x_1596_);
v_xs_1623_ = l_Lean_Syntax_getArgs(v___x_1621_);
lean_dec_ref_known(v___x_1621_, 3);
v_x_1212_ = v_x_1593_;
v_xs_1213_ = v_xs_1623_;
v_ty_1214_ = v_ty_1622_;
v_P_1215_ = v_P_1601_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
v___jp_1624_:
{
if (v___y_1625_ == 0)
{
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___y_1626_ == 0)
{
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1627_; 
lean_inc(v___x_1600_);
v___x_1627_ = l_Lean_Syntax_matchesNull(v___x_1600_, v___x_481_);
if (v___x_1627_ == 0)
{
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v_ty_1633_; lean_object* v_xs_1634_; 
lean_dec(v___x_1600_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1628_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1629_ = l_Array_extract___redArg(v___x_1628_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1628_);
v___x_1630_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1631_ = lean_box(2);
v___x_1632_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1632_, 0, v___x_1631_);
lean_ctor_set(v___x_1632_, 1, v___x_1630_);
lean_ctor_set(v___x_1632_, 2, v___x_1629_);
v_ty_1633_ = l_Lean_Syntax_getArg(v___x_1596_, v___x_482_);
lean_dec(v___x_1596_);
v_xs_1634_ = l_Lean_Syntax_getArgs(v___x_1632_);
lean_dec_ref_known(v___x_1632_, 3);
v_x_1212_ = v_x_1593_;
v_xs_1213_ = v_xs_1634_;
v_ty_1214_ = v_ty_1633_;
v_P_1215_ = v_P_1601_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
v___jp_1635_:
{
if (v___y_1637_ == 0)
{
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___y_1638_ == 0)
{
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___y_1636_ == 0)
{
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v_ty_1644_; lean_object* v_xs_1645_; 
lean_dec(v___x_1600_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1639_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1640_ = l_Array_extract___redArg(v___x_1639_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1639_);
v___x_1641_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1642_ = lean_box(2);
v___x_1643_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1643_, 0, v___x_1642_);
lean_ctor_set(v___x_1643_, 1, v___x_1641_);
lean_ctor_set(v___x_1643_, 2, v___x_1640_);
v_ty_1644_ = l_Lean_Syntax_getArg(v___x_1596_, v___x_482_);
lean_dec(v___x_1596_);
v_xs_1645_ = l_Lean_Syntax_getArgs(v___x_1643_);
lean_dec_ref_known(v___x_1643_, 3);
v_x_1212_ = v_x_1593_;
v_xs_1213_ = v_xs_1645_;
v_ty_1214_ = v_ty_1644_;
v_P_1215_ = v_P_1601_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
v___jp_1646_:
{
uint8_t v___x_1647_; 
lean_inc(v___x_1596_);
v___x_1647_ = l_Lean_Syntax_matchesNull(v___x_1596_, v___x_1595_);
if (v___x_1647_ == 0)
{
if (v___x_1520_ == 0)
{
lean_dec(v___x_1598_);
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1647_ == 0)
{
lean_object* v___x_1648_; uint8_t v___x_1649_; 
v___x_1648_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1593_);
v___x_1649_ = l_Lean_Syntax_isOfKind(v_x_1593_, v___x_1648_);
if (v___x_1649_ == 0)
{
lean_dec(v___x_1598_);
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
v___y_1614_ = v___x_1647_;
goto v___jp_1613_;
}
}
else
{
v___y_1614_ = v___x_1647_;
goto v___jp_1613_;
}
}
}
else
{
uint8_t v___x_1650_; 
v___x_1650_ = l_Lean_Syntax_matchesNull(v___x_1598_, v___x_481_);
if (v___x_1650_ == 0)
{
if (v___x_1520_ == 0)
{
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1650_ == 0)
{
lean_object* v___x_1651_; uint8_t v___x_1652_; 
v___x_1651_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1593_);
v___x_1652_ = l_Lean_Syntax_isOfKind(v_x_1593_, v___x_1651_);
if (v___x_1652_ == 0)
{
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
v___y_1625_ = v___x_1647_;
v___y_1626_ = v___x_1650_;
goto v___jp_1624_;
}
}
else
{
v___y_1625_ = v___x_1647_;
v___y_1626_ = v___x_1650_;
goto v___jp_1624_;
}
}
}
else
{
uint8_t v___x_1653_; 
lean_inc(v___x_1600_);
v___x_1653_ = l_Lean_Syntax_matchesNull(v___x_1600_, v___x_481_);
if (v___x_1653_ == 0)
{
if (v___x_1520_ == 0)
{
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1653_ == 0)
{
lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1654_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1593_);
v___x_1655_ = l_Lean_Syntax_isOfKind(v_x_1593_, v___x_1654_);
if (v___x_1655_ == 0)
{
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
v___y_1636_ = v___x_1653_;
v___y_1637_ = v___x_1647_;
v___y_1638_ = v___x_1650_;
goto v___jp_1635_;
}
}
else
{
v___y_1636_ = v___x_1653_;
v___y_1637_ = v___x_1647_;
v___y_1638_ = v___x_1650_;
goto v___jp_1635_;
}
}
}
else
{
lean_object* v_ty_1656_; 
lean_dec(v___x_1600_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v_ty_1656_ = l_Lean_Syntax_getArg(v___x_1596_, v___x_482_);
lean_dec(v___x_1596_);
v_x_1159_ = v_x_1593_;
v_ty_1160_ = v_ty_1656_;
v_P_1161_ = v_P_1601_;
v___y_1162_ = v_a_471_;
v___y_1163_ = v_a_472_;
goto v___jp_1158_;
}
}
}
}
v___jp_1657_:
{
uint8_t v___x_1658_; 
lean_inc(v___x_1596_);
v___x_1658_ = l_Lean_Syntax_matchesNull(v___x_1596_, v___x_1595_);
if (v___x_1658_ == 0)
{
lean_dec(v___x_1598_);
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1659_; 
v___x_1659_ = l_Lean_Syntax_matchesNull(v___x_1598_, v___x_481_);
if (v___x_1659_ == 0)
{
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1660_; 
lean_inc(v___x_1600_);
v___x_1660_ = l_Lean_Syntax_matchesNull(v___x_1600_, v___x_481_);
if (v___x_1660_ == 0)
{
lean_dec(v___x_1596_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1600_;
v_____discr_1278_ = v_P_1601_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v_ty_1666_; lean_object* v_xs_1667_; 
lean_dec(v___x_1600_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1661_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1662_ = l_Array_extract___redArg(v___x_1661_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1661_);
v___x_1663_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1664_ = lean_box(2);
v___x_1665_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1665_, 0, v___x_1664_);
lean_ctor_set(v___x_1665_, 1, v___x_1663_);
lean_ctor_set(v___x_1665_, 2, v___x_1662_);
v_ty_1666_ = l_Lean_Syntax_getArg(v___x_1596_, v___x_482_);
lean_dec(v___x_1596_);
v_xs_1667_ = l_Lean_Syntax_getArgs(v___x_1665_);
lean_dec_ref_known(v___x_1665_, 3);
v_x_1212_ = v_x_1593_;
v_xs_1213_ = v_xs_1667_;
v_ty_1214_ = v_ty_1666_;
v_P_1215_ = v_P_1601_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
}
else
{
lean_object* v___x_1673_; lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1673_ = lean_unsigned_to_nat(2u);
v___x_1674_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1673_);
lean_inc(v___x_1674_);
v___x_1675_ = l_Lean_Syntax_matchesNull(v___x_1674_, v___x_1673_);
if (v___x_1675_ == 0)
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v_P_1680_; uint8_t v___y_1702_; uint8_t v___y_1712_; uint8_t v___y_1713_; uint8_t v___x_1741_; 
v___x_1676_ = lean_unsigned_to_nat(3u);
v___x_1677_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1676_);
v___x_1678_ = lean_unsigned_to_nat(4u);
v___x_1679_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1673_);
v_P_1680_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1678_);
lean_dec(v___x_483_);
lean_inc(v___x_1518_);
v___x_1741_ = l_Lean_Syntax_matchesNull(v___x_1518_, v___x_482_);
if (v___x_1741_ == 0)
{
if (v___x_1520_ == 0)
{
lean_dec(v___x_1677_);
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1741_ == 0)
{
lean_object* v___x_1742_; uint8_t v___x_1743_; 
v___x_1742_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1593_);
v___x_1743_ = l_Lean_Syntax_isOfKind(v_x_1593_, v___x_1742_);
if (v___x_1743_ == 0)
{
lean_dec(v___x_1677_);
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
goto v___jp_1731_;
}
}
else
{
goto v___jp_1731_;
}
}
}
else
{
if (v___x_1675_ == 0)
{
lean_object* v___x_1744_; uint8_t v___x_1745_; 
v___x_1744_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1593_);
v___x_1745_ = l_Lean_Syntax_isOfKind(v_x_1593_, v___x_1744_);
if (v___x_1745_ == 0)
{
if (v___x_1520_ == 0)
{
lean_dec(v___x_1677_);
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1675_ == 0)
{
if (v___x_1745_ == 0)
{
lean_dec(v___x_1677_);
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
goto v___jp_1681_;
}
}
else
{
goto v___jp_1681_;
}
}
}
else
{
goto v___jp_1721_;
}
}
else
{
goto v___jp_1721_;
}
}
v___jp_1681_:
{
if (v___x_1675_ == 0)
{
lean_dec(v___x_1677_);
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1682_; 
v___x_1682_ = l_Lean_Syntax_matchesNull(v___x_1677_, v___x_481_);
if (v___x_1682_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1683_; 
lean_inc(v___x_1679_);
v___x_1683_ = l_Lean_Syntax_matchesNull(v___x_1679_, v___x_481_);
if (v___x_1683_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v_ty_1689_; lean_object* v_xs_1690_; 
lean_dec(v___x_1679_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1684_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1685_ = l_Array_extract___redArg(v___x_1684_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1684_);
v___x_1686_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1687_ = lean_box(2);
v___x_1688_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
lean_ctor_set(v___x_1688_, 1, v___x_1686_);
lean_ctor_set(v___x_1688_, 2, v___x_1685_);
v_ty_1689_ = l_Lean_Syntax_getArg(v___x_1674_, v___x_482_);
lean_dec(v___x_1674_);
v_xs_1690_ = l_Lean_Syntax_getArgs(v___x_1688_);
lean_dec_ref_known(v___x_1688_, 3);
v_x_1212_ = v_x_1593_;
v_xs_1213_ = v_xs_1690_;
v_ty_1214_ = v_ty_1689_;
v_P_1215_ = v_P_1680_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
v___jp_1691_:
{
if (v___x_1675_ == 0)
{
lean_dec(v___x_1677_);
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1692_; 
v___x_1692_ = l_Lean_Syntax_matchesNull(v___x_1677_, v___x_481_);
if (v___x_1692_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1693_; 
lean_inc(v___x_1679_);
v___x_1693_ = l_Lean_Syntax_matchesNull(v___x_1679_, v___x_481_);
if (v___x_1693_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v_ty_1699_; lean_object* v_xs_1700_; 
lean_dec(v___x_1679_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1694_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1695_ = l_Array_extract___redArg(v___x_1694_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1694_);
v___x_1696_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1697_ = lean_box(2);
v___x_1698_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1697_);
lean_ctor_set(v___x_1698_, 1, v___x_1696_);
lean_ctor_set(v___x_1698_, 2, v___x_1695_);
v_ty_1699_ = l_Lean_Syntax_getArg(v___x_1674_, v___x_482_);
lean_dec(v___x_1674_);
v_xs_1700_ = l_Lean_Syntax_getArgs(v___x_1698_);
lean_dec_ref_known(v___x_1698_, 3);
v_x_1212_ = v_x_1593_;
v_xs_1213_ = v_xs_1700_;
v_ty_1214_ = v_ty_1699_;
v_P_1215_ = v_P_1680_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
v___jp_1701_:
{
if (v___x_1675_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___y_1702_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1703_; 
lean_inc(v___x_1679_);
v___x_1703_ = l_Lean_Syntax_matchesNull(v___x_1679_, v___x_481_);
if (v___x_1703_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1704_; lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; lean_object* v_ty_1709_; lean_object* v_xs_1710_; 
lean_dec(v___x_1679_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1704_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1705_ = l_Array_extract___redArg(v___x_1704_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1704_);
v___x_1706_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1707_ = lean_box(2);
v___x_1708_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1708_, 0, v___x_1707_);
lean_ctor_set(v___x_1708_, 1, v___x_1706_);
lean_ctor_set(v___x_1708_, 2, v___x_1705_);
v_ty_1709_ = l_Lean_Syntax_getArg(v___x_1674_, v___x_482_);
lean_dec(v___x_1674_);
v_xs_1710_ = l_Lean_Syntax_getArgs(v___x_1708_);
lean_dec_ref_known(v___x_1708_, 3);
v_x_1212_ = v_x_1593_;
v_xs_1213_ = v_xs_1710_;
v_ty_1214_ = v_ty_1709_;
v_P_1215_ = v_P_1680_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
v___jp_1711_:
{
if (v___x_1675_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___y_1713_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___y_1712_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1714_; lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v_ty_1719_; lean_object* v_xs_1720_; 
lean_dec(v___x_1679_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1714_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1715_ = l_Array_extract___redArg(v___x_1714_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1714_);
v___x_1716_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1717_ = lean_box(2);
v___x_1718_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1718_, 0, v___x_1717_);
lean_ctor_set(v___x_1718_, 1, v___x_1716_);
lean_ctor_set(v___x_1718_, 2, v___x_1715_);
v_ty_1719_ = l_Lean_Syntax_getArg(v___x_1674_, v___x_482_);
lean_dec(v___x_1674_);
v_xs_1720_ = l_Lean_Syntax_getArgs(v___x_1718_);
lean_dec_ref_known(v___x_1718_, 3);
v_x_1212_ = v_x_1593_;
v_xs_1213_ = v_xs_1720_;
v_ty_1214_ = v_ty_1719_;
v_P_1215_ = v_P_1680_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
v___jp_1721_:
{
if (v___x_1675_ == 0)
{
if (v___x_1520_ == 0)
{
lean_dec(v___x_1677_);
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1675_ == 0)
{
lean_object* v___x_1722_; uint8_t v___x_1723_; 
v___x_1722_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1593_);
v___x_1723_ = l_Lean_Syntax_isOfKind(v_x_1593_, v___x_1722_);
if (v___x_1723_ == 0)
{
lean_dec(v___x_1677_);
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
goto v___jp_1691_;
}
}
else
{
goto v___jp_1691_;
}
}
}
else
{
uint8_t v___x_1724_; 
v___x_1724_ = l_Lean_Syntax_matchesNull(v___x_1677_, v___x_481_);
if (v___x_1724_ == 0)
{
if (v___x_1520_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1724_ == 0)
{
lean_object* v___x_1725_; uint8_t v___x_1726_; 
v___x_1725_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1593_);
v___x_1726_ = l_Lean_Syntax_isOfKind(v_x_1593_, v___x_1725_);
if (v___x_1726_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
v___y_1702_ = v___x_1724_;
goto v___jp_1701_;
}
}
else
{
v___y_1702_ = v___x_1724_;
goto v___jp_1701_;
}
}
}
else
{
uint8_t v___x_1727_; 
lean_inc(v___x_1679_);
v___x_1727_ = l_Lean_Syntax_matchesNull(v___x_1679_, v___x_481_);
if (v___x_1727_ == 0)
{
if (v___x_1520_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1727_ == 0)
{
lean_object* v___x_1728_; uint8_t v___x_1729_; 
v___x_1728_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1593_);
v___x_1729_ = l_Lean_Syntax_isOfKind(v_x_1593_, v___x_1728_);
if (v___x_1729_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
v___y_1712_ = v___x_1727_;
v___y_1713_ = v___x_1724_;
goto v___jp_1711_;
}
}
else
{
v___y_1712_ = v___x_1727_;
v___y_1713_ = v___x_1724_;
goto v___jp_1711_;
}
}
}
else
{
lean_object* v_ty_1730_; 
lean_dec(v___x_1679_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v_ty_1730_ = l_Lean_Syntax_getArg(v___x_1674_, v___x_482_);
lean_dec(v___x_1674_);
v_x_1159_ = v_x_1593_;
v_ty_1160_ = v_ty_1730_;
v_P_1161_ = v_P_1680_;
v___y_1162_ = v_a_471_;
v___y_1163_ = v_a_472_;
goto v___jp_1158_;
}
}
}
}
v___jp_1731_:
{
if (v___x_1675_ == 0)
{
lean_dec(v___x_1677_);
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1732_; 
v___x_1732_ = l_Lean_Syntax_matchesNull(v___x_1677_, v___x_481_);
if (v___x_1732_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1733_; 
lean_inc(v___x_1679_);
v___x_1733_ = l_Lean_Syntax_matchesNull(v___x_1679_, v___x_481_);
if (v___x_1733_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1679_;
v_____discr_1278_ = v_P_1680_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v_ty_1739_; lean_object* v_xs_1740_; 
lean_dec(v___x_1679_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1734_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1735_ = l_Array_extract___redArg(v___x_1734_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1734_);
v___x_1736_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1737_ = lean_box(2);
v___x_1738_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1738_, 0, v___x_1737_);
lean_ctor_set(v___x_1738_, 1, v___x_1736_);
lean_ctor_set(v___x_1738_, 2, v___x_1735_);
v_ty_1739_ = l_Lean_Syntax_getArg(v___x_1674_, v___x_482_);
lean_dec(v___x_1674_);
v_xs_1740_ = l_Lean_Syntax_getArgs(v___x_1738_);
lean_dec_ref_known(v___x_1738_, 3);
v_x_1212_ = v_x_1593_;
v_xs_1213_ = v_xs_1740_;
v_ty_1214_ = v_ty_1739_;
v_P_1215_ = v_P_1680_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
}
else
{
lean_object* v___x_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v___x_1746_ = lean_unsigned_to_nat(3u);
v___x_1747_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1746_);
v___x_1748_ = l_Lean_Syntax_matchesNull(v___x_1747_, v___x_481_);
if (v___x_1748_ == 0)
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v_P_1751_; uint8_t v___y_1780_; uint8_t v___x_1806_; 
v___x_1749_ = lean_unsigned_to_nat(4u);
v___x_1750_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1673_);
v_P_1751_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1749_);
lean_dec(v___x_483_);
lean_inc(v___x_1518_);
v___x_1806_ = l_Lean_Syntax_matchesNull(v___x_1518_, v___x_482_);
if (v___x_1806_ == 0)
{
if (v___x_1520_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1806_ == 0)
{
lean_object* v___x_1807_; uint8_t v___x_1808_; 
v___x_1807_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1593_);
v___x_1808_ = l_Lean_Syntax_isOfKind(v_x_1593_, v___x_1807_);
if (v___x_1808_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
goto v___jp_1797_;
}
}
else
{
goto v___jp_1797_;
}
}
}
else
{
if (v___x_1748_ == 0)
{
lean_object* v___x_1809_; uint8_t v___x_1810_; 
v___x_1809_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1593_);
v___x_1810_ = l_Lean_Syntax_isOfKind(v_x_1593_, v___x_1809_);
if (v___x_1810_ == 0)
{
if (v___x_1520_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1748_ == 0)
{
if (v___x_1810_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
goto v___jp_1752_;
}
}
else
{
goto v___jp_1752_;
}
}
}
else
{
goto v___jp_1788_;
}
}
else
{
goto v___jp_1788_;
}
}
v___jp_1752_:
{
if (v___x_1675_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1748_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1753_; 
lean_inc(v___x_1750_);
v___x_1753_ = l_Lean_Syntax_matchesNull(v___x_1750_, v___x_481_);
if (v___x_1753_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v_ty_1759_; lean_object* v_xs_1760_; 
lean_dec(v___x_1750_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1754_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1755_ = l_Array_extract___redArg(v___x_1754_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1754_);
v___x_1756_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1757_ = lean_box(2);
v___x_1758_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
lean_ctor_set(v___x_1758_, 1, v___x_1756_);
lean_ctor_set(v___x_1758_, 2, v___x_1755_);
v_ty_1759_ = l_Lean_Syntax_getArg(v___x_1674_, v___x_482_);
lean_dec(v___x_1674_);
v_xs_1760_ = l_Lean_Syntax_getArgs(v___x_1758_);
lean_dec_ref_known(v___x_1758_, 3);
v_x_1212_ = v_x_1593_;
v_xs_1213_ = v_xs_1760_;
v_ty_1214_ = v_ty_1759_;
v_P_1215_ = v_P_1751_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
v___jp_1761_:
{
if (v___x_1675_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1748_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1762_; 
lean_inc(v___x_1750_);
v___x_1762_ = l_Lean_Syntax_matchesNull(v___x_1750_, v___x_481_);
if (v___x_1762_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; lean_object* v___x_1767_; lean_object* v_ty_1768_; lean_object* v_xs_1769_; 
lean_dec(v___x_1750_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1763_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1764_ = l_Array_extract___redArg(v___x_1763_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1763_);
v___x_1765_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1766_ = lean_box(2);
v___x_1767_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1767_, 0, v___x_1766_);
lean_ctor_set(v___x_1767_, 1, v___x_1765_);
lean_ctor_set(v___x_1767_, 2, v___x_1764_);
v_ty_1768_ = l_Lean_Syntax_getArg(v___x_1674_, v___x_482_);
lean_dec(v___x_1674_);
v_xs_1769_ = l_Lean_Syntax_getArgs(v___x_1767_);
lean_dec_ref_known(v___x_1767_, 3);
v_x_1212_ = v_x_1593_;
v_xs_1213_ = v_xs_1769_;
v_ty_1214_ = v_ty_1768_;
v_P_1215_ = v_P_1751_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
v___jp_1770_:
{
if (v___x_1675_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1748_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1771_; 
lean_inc(v___x_1750_);
v___x_1771_ = l_Lean_Syntax_matchesNull(v___x_1750_, v___x_481_);
if (v___x_1771_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v_ty_1777_; lean_object* v_xs_1778_; 
lean_dec(v___x_1750_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1772_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1773_ = l_Array_extract___redArg(v___x_1772_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1772_);
v___x_1774_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1775_ = lean_box(2);
v___x_1776_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1775_);
lean_ctor_set(v___x_1776_, 1, v___x_1774_);
lean_ctor_set(v___x_1776_, 2, v___x_1773_);
v_ty_1777_ = l_Lean_Syntax_getArg(v___x_1674_, v___x_482_);
lean_dec(v___x_1674_);
v_xs_1778_ = l_Lean_Syntax_getArgs(v___x_1776_);
lean_dec_ref_known(v___x_1776_, 3);
v_x_1212_ = v_x_1593_;
v_xs_1213_ = v_xs_1778_;
v_ty_1214_ = v_ty_1777_;
v_P_1215_ = v_P_1751_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
v___jp_1779_:
{
if (v___x_1675_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1748_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___y_1780_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v_ty_1786_; lean_object* v_xs_1787_; 
lean_dec(v___x_1750_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1781_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1782_ = l_Array_extract___redArg(v___x_1781_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1781_);
v___x_1783_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1784_ = lean_box(2);
v___x_1785_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
lean_ctor_set(v___x_1785_, 1, v___x_1783_);
lean_ctor_set(v___x_1785_, 2, v___x_1782_);
v_ty_1786_ = l_Lean_Syntax_getArg(v___x_1674_, v___x_482_);
lean_dec(v___x_1674_);
v_xs_1787_ = l_Lean_Syntax_getArgs(v___x_1785_);
lean_dec_ref_known(v___x_1785_, 3);
v_x_1212_ = v_x_1593_;
v_xs_1213_ = v_xs_1787_;
v_ty_1214_ = v_ty_1786_;
v_P_1215_ = v_P_1751_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
v___jp_1788_:
{
if (v___x_1675_ == 0)
{
if (v___x_1520_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1675_ == 0)
{
lean_object* v___x_1789_; uint8_t v___x_1790_; 
v___x_1789_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1593_);
v___x_1790_ = l_Lean_Syntax_isOfKind(v_x_1593_, v___x_1789_);
if (v___x_1790_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
goto v___jp_1761_;
}
}
else
{
goto v___jp_1761_;
}
}
}
else
{
if (v___x_1748_ == 0)
{
if (v___x_1520_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1748_ == 0)
{
lean_object* v___x_1791_; uint8_t v___x_1792_; 
v___x_1791_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1593_);
v___x_1792_ = l_Lean_Syntax_isOfKind(v_x_1593_, v___x_1791_);
if (v___x_1792_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
goto v___jp_1770_;
}
}
else
{
goto v___jp_1770_;
}
}
}
else
{
uint8_t v___x_1793_; 
lean_inc(v___x_1750_);
v___x_1793_ = l_Lean_Syntax_matchesNull(v___x_1750_, v___x_481_);
if (v___x_1793_ == 0)
{
if (v___x_1520_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1793_ == 0)
{
lean_object* v___x_1794_; uint8_t v___x_1795_; 
v___x_1794_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1593_);
v___x_1795_ = l_Lean_Syntax_isOfKind(v_x_1593_, v___x_1794_);
if (v___x_1795_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
v___y_1780_ = v___x_1793_;
goto v___jp_1779_;
}
}
else
{
v___y_1780_ = v___x_1793_;
goto v___jp_1779_;
}
}
}
else
{
lean_object* v_ty_1796_; 
lean_dec(v___x_1750_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v_ty_1796_ = l_Lean_Syntax_getArg(v___x_1674_, v___x_482_);
lean_dec(v___x_1674_);
v_x_1159_ = v_x_1593_;
v_ty_1160_ = v_ty_1796_;
v_P_1161_ = v_P_1751_;
v___y_1162_ = v_a_471_;
v___y_1163_ = v_a_472_;
goto v___jp_1158_;
}
}
}
}
v___jp_1797_:
{
if (v___x_1675_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1748_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
uint8_t v___x_1798_; 
lean_inc(v___x_1750_);
v___x_1798_ = l_Lean_Syntax_matchesNull(v___x_1750_, v___x_481_);
if (v___x_1798_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1750_;
v_____discr_1278_ = v_P_1751_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v_ty_1804_; lean_object* v_xs_1805_; 
lean_dec(v___x_1750_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1799_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1800_ = l_Array_extract___redArg(v___x_1799_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1799_);
v___x_1801_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1802_ = lean_box(2);
v___x_1803_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1803_, 0, v___x_1802_);
lean_ctor_set(v___x_1803_, 1, v___x_1801_);
lean_ctor_set(v___x_1803_, 2, v___x_1800_);
v_ty_1804_ = l_Lean_Syntax_getArg(v___x_1674_, v___x_482_);
lean_dec(v___x_1674_);
v_xs_1805_ = l_Lean_Syntax_getArgs(v___x_1803_);
lean_dec_ref_known(v___x_1803_, 3);
v_x_1212_ = v_x_1593_;
v_xs_1213_ = v_xs_1805_;
v_ty_1214_ = v_ty_1804_;
v_P_1215_ = v_P_1751_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
}
else
{
lean_object* v___x_1811_; lean_object* v___x_1812_; uint8_t v___x_1813_; 
v___x_1811_ = lean_unsigned_to_nat(4u);
v___x_1812_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1673_);
lean_inc(v___x_1812_);
v___x_1813_ = l_Lean_Syntax_matchesNull(v___x_1812_, v___x_481_);
if (v___x_1813_ == 0)
{
lean_object* v_P_1814_; uint8_t v___x_1863_; 
v_P_1814_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1811_);
lean_dec(v___x_483_);
lean_inc(v___x_1518_);
v___x_1863_ = l_Lean_Syntax_matchesNull(v___x_1518_, v___x_482_);
if (v___x_1863_ == 0)
{
if (v___x_1520_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1863_ == 0)
{
lean_object* v___x_1864_; uint8_t v___x_1865_; 
v___x_1864_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1593_);
v___x_1865_ = l_Lean_Syntax_isOfKind(v_x_1593_, v___x_1864_);
if (v___x_1865_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
goto v___jp_1855_;
}
}
else
{
goto v___jp_1855_;
}
}
}
else
{
if (v___x_1813_ == 0)
{
lean_object* v___x_1866_; uint8_t v___x_1867_; 
v___x_1866_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1593_);
v___x_1867_ = l_Lean_Syntax_isOfKind(v_x_1593_, v___x_1866_);
if (v___x_1867_ == 0)
{
if (v___x_1520_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1813_ == 0)
{
if (v___x_1867_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
goto v___jp_1815_;
}
}
else
{
goto v___jp_1815_;
}
}
}
else
{
goto v___jp_1847_;
}
}
else
{
goto v___jp_1847_;
}
}
v___jp_1815_:
{
if (v___x_1675_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1748_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1813_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v_ty_1821_; lean_object* v_xs_1822_; 
lean_dec(v___x_1812_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1816_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1817_ = l_Array_extract___redArg(v___x_1816_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1816_);
v___x_1818_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1819_ = lean_box(2);
v___x_1820_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1820_, 0, v___x_1819_);
lean_ctor_set(v___x_1820_, 1, v___x_1818_);
lean_ctor_set(v___x_1820_, 2, v___x_1817_);
v_ty_1821_ = l_Lean_Syntax_getArg(v___x_1674_, v___x_482_);
lean_dec(v___x_1674_);
v_xs_1822_ = l_Lean_Syntax_getArgs(v___x_1820_);
lean_dec_ref_known(v___x_1820_, 3);
v_x_1212_ = v_x_1593_;
v_xs_1213_ = v_xs_1822_;
v_ty_1214_ = v_ty_1821_;
v_P_1215_ = v_P_1814_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
v___jp_1823_:
{
if (v___x_1675_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1748_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1813_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; lean_object* v___x_1828_; lean_object* v_ty_1829_; lean_object* v_xs_1830_; 
lean_dec(v___x_1812_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1824_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1825_ = l_Array_extract___redArg(v___x_1824_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1824_);
v___x_1826_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1827_ = lean_box(2);
v___x_1828_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1828_, 0, v___x_1827_);
lean_ctor_set(v___x_1828_, 1, v___x_1826_);
lean_ctor_set(v___x_1828_, 2, v___x_1825_);
v_ty_1829_ = l_Lean_Syntax_getArg(v___x_1674_, v___x_482_);
lean_dec(v___x_1674_);
v_xs_1830_ = l_Lean_Syntax_getArgs(v___x_1828_);
lean_dec_ref_known(v___x_1828_, 3);
v_x_1212_ = v_x_1593_;
v_xs_1213_ = v_xs_1830_;
v_ty_1214_ = v_ty_1829_;
v_P_1215_ = v_P_1814_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
v___jp_1831_:
{
if (v___x_1675_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1748_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1813_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1832_; lean_object* v___x_1833_; lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v_ty_1837_; lean_object* v_xs_1838_; 
lean_dec(v___x_1812_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1832_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1833_ = l_Array_extract___redArg(v___x_1832_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1832_);
v___x_1834_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1835_ = lean_box(2);
v___x_1836_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1836_, 0, v___x_1835_);
lean_ctor_set(v___x_1836_, 1, v___x_1834_);
lean_ctor_set(v___x_1836_, 2, v___x_1833_);
v_ty_1837_ = l_Lean_Syntax_getArg(v___x_1674_, v___x_482_);
lean_dec(v___x_1674_);
v_xs_1838_ = l_Lean_Syntax_getArgs(v___x_1836_);
lean_dec_ref_known(v___x_1836_, 3);
v_x_1212_ = v_x_1593_;
v_xs_1213_ = v_xs_1838_;
v_ty_1214_ = v_ty_1837_;
v_P_1215_ = v_P_1814_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
v___jp_1839_:
{
if (v___x_1675_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1748_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1813_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v_ty_1845_; lean_object* v_xs_1846_; 
lean_dec(v___x_1812_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1840_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1841_ = l_Array_extract___redArg(v___x_1840_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1840_);
v___x_1842_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1843_ = lean_box(2);
v___x_1844_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1844_, 0, v___x_1843_);
lean_ctor_set(v___x_1844_, 1, v___x_1842_);
lean_ctor_set(v___x_1844_, 2, v___x_1841_);
v_ty_1845_ = l_Lean_Syntax_getArg(v___x_1674_, v___x_482_);
lean_dec(v___x_1674_);
v_xs_1846_ = l_Lean_Syntax_getArgs(v___x_1844_);
lean_dec_ref_known(v___x_1844_, 3);
v_x_1212_ = v_x_1593_;
v_xs_1213_ = v_xs_1846_;
v_ty_1214_ = v_ty_1845_;
v_P_1215_ = v_P_1814_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
v___jp_1847_:
{
if (v___x_1675_ == 0)
{
if (v___x_1520_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1675_ == 0)
{
lean_object* v___x_1848_; uint8_t v___x_1849_; 
v___x_1848_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1593_);
v___x_1849_ = l_Lean_Syntax_isOfKind(v_x_1593_, v___x_1848_);
if (v___x_1849_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
goto v___jp_1823_;
}
}
else
{
goto v___jp_1823_;
}
}
}
else
{
if (v___x_1748_ == 0)
{
if (v___x_1520_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1748_ == 0)
{
lean_object* v___x_1850_; uint8_t v___x_1851_; 
v___x_1850_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1593_);
v___x_1851_ = l_Lean_Syntax_isOfKind(v_x_1593_, v___x_1850_);
if (v___x_1851_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
goto v___jp_1831_;
}
}
else
{
goto v___jp_1831_;
}
}
}
else
{
if (v___x_1813_ == 0)
{
if (v___x_1520_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1813_ == 0)
{
lean_object* v___x_1852_; uint8_t v___x_1853_; 
v___x_1852_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1593_);
v___x_1853_ = l_Lean_Syntax_isOfKind(v_x_1593_, v___x_1852_);
if (v___x_1853_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
goto v___jp_1839_;
}
}
else
{
goto v___jp_1839_;
}
}
}
else
{
lean_object* v_ty_1854_; 
lean_dec(v___x_1812_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v_ty_1854_ = l_Lean_Syntax_getArg(v___x_1674_, v___x_482_);
lean_dec(v___x_1674_);
v_x_1159_ = v_x_1593_;
v_ty_1160_ = v_ty_1854_;
v_P_1161_ = v_P_1814_;
v___y_1162_ = v_a_471_;
v___y_1163_ = v_a_472_;
goto v___jp_1158_;
}
}
}
}
v___jp_1855_:
{
if (v___x_1675_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1748_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
if (v___x_1813_ == 0)
{
lean_dec(v___x_1674_);
lean_dec(v_x_1593_);
lean_dec(v___x_1519_);
lean_dec(v___x_1518_);
v_____discr_1277_ = v___x_1812_;
v_____discr_1278_ = v_P_1814_;
v___y_1279_ = v_a_471_;
v___y_1280_ = v_a_472_;
goto v___jp_1276_;
}
else
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v_ty_1861_; lean_object* v_xs_1862_; 
lean_dec(v___x_1812_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___x_1856_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1857_ = l_Array_extract___redArg(v___x_1856_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1856_);
v___x_1858_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1859_ = lean_box(2);
v___x_1860_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1860_, 0, v___x_1859_);
lean_ctor_set(v___x_1860_, 1, v___x_1858_);
lean_ctor_set(v___x_1860_, 2, v___x_1857_);
v_ty_1861_ = l_Lean_Syntax_getArg(v___x_1674_, v___x_482_);
lean_dec(v___x_1674_);
v_xs_1862_ = l_Lean_Syntax_getArgs(v___x_1860_);
lean_dec_ref_known(v___x_1860_, 3);
v_x_1212_ = v_x_1593_;
v_xs_1213_ = v_xs_1862_;
v_ty_1214_ = v_ty_1861_;
v_P_1215_ = v_P_1814_;
v___y_1216_ = v_a_471_;
v___y_1217_ = v_a_472_;
goto v___jp_1211_;
}
}
}
}
}
else
{
lean_object* v_quotContext_1868_; lean_object* v_currMacroScope_1869_; lean_object* v_ref_1870_; lean_object* v_tk_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v_xs_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; lean_object* v___x_1937_; 
lean_dec(v___x_1812_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v_quotContext_1868_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_1869_ = lean_ctor_get(v_a_471_, 2);
v_ref_1870_ = lean_ctor_get(v_a_471_, 5);
v_tk_1871_ = l_Lean_Syntax_getArg(v_x_1593_, v___x_481_);
lean_dec(v_x_1593_);
v___x_1872_ = l_Lean_Syntax_getArgs(v___x_1518_);
lean_dec(v___x_1518_);
v___x_1873_ = l_Array_extract___redArg(v___x_1872_, v___x_482_, v___x_1519_);
lean_dec_ref(v___x_1872_);
v___x_1874_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1875_ = lean_box(2);
v___x_1876_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1876_, 0, v___x_1875_);
lean_ctor_set(v___x_1876_, 1, v___x_1874_);
lean_ctor_set(v___x_1876_, 2, v___x_1873_);
v___x_1877_ = l_Lean_Syntax_getArg(v___x_1674_, v___x_482_);
lean_dec(v___x_1674_);
v___x_1878_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1811_);
lean_dec(v___x_483_);
v_xs_1879_ = l_Lean_Syntax_getArgs(v___x_1876_);
lean_dec_ref_known(v___x_1876_, 3);
v___x_1880_ = l_Lean_SourceInfo_fromRef(v_ref_1870_, v___x_1157_);
v___x_1881_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_1882_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_1883_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc_n(v_currMacroScope_1869_, 2);
lean_inc_n(v_quotContext_1868_, 2);
v___x_1884_ = l_Lean_addMacroScope(v_quotContext_1868_, v___x_1883_, v_currMacroScope_1869_);
v___x_1885_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc_n(v___x_1880_, 27);
v___x_1886_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1886_, 0, v___x_1880_);
lean_ctor_set(v___x_1886_, 1, v___x_1882_);
lean_ctor_set(v___x_1886_, 2, v___x_1884_);
lean_ctor_set(v___x_1886_, 3, v___x_1885_);
v___x_1887_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_1888_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_1889_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
v___x_1890_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1890_, 0, v___x_1880_);
lean_ctor_set(v___x_1890_, 1, v___x_1889_);
v___x_1891_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_1892_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_1893_ = lean_box(0);
v___x_1894_ = l_Lean_addMacroScope(v_quotContext_1868_, v___x_1893_, v_currMacroScope_1869_);
v___x_1895_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
v___x_1896_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1896_, 0, v___x_1880_);
lean_ctor_set(v___x_1896_, 1, v___x_1892_);
lean_ctor_set(v___x_1896_, 2, v___x_1894_);
lean_ctor_set(v___x_1896_, 3, v___x_1895_);
v___x_1897_ = l_Lean_Syntax_node1(v___x_1880_, v___x_1891_, v___x_1896_);
lean_inc_ref(v___x_1890_);
v___x_1898_ = l_Lean_Syntax_node2(v___x_1880_, v___x_1888_, v___x_1890_, v___x_1897_);
v___x_1899_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_1900_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
v___x_1901_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1901_, 0, v___x_1880_);
lean_ctor_set(v___x_1901_, 1, v___x_1899_);
v___x_1902_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_1903_ = l_Lean_SourceInfo_fromRef(v_tk_1871_, v___x_830_);
lean_dec(v_tk_1871_);
v___x_1904_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__63));
v___x_1905_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1905_, 0, v___x_1903_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = l_Lean_Syntax_node1(v___x_1880_, v___x_1156_, v___x_1905_);
v___x_1907_ = l_Lean_Syntax_node1(v___x_1880_, v___x_1874_, v___x_1906_);
v___x_1908_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55));
v___x_1909_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
v___x_1910_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1910_, 0, v___x_1880_);
lean_ctor_set(v___x_1910_, 1, v___x_1909_);
lean_inc(v___x_1877_);
lean_inc_ref(v___x_1910_);
v___x_1911_ = l_Lean_Syntax_node2(v___x_1880_, v___x_1908_, v___x_1910_, v___x_1877_);
v___x_1912_ = l_Lean_Syntax_node1(v___x_1880_, v___x_1874_, v___x_1911_);
v___x_1913_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_1914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1880_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_1916_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1916_, 0, v___x_1880_);
lean_ctor_set(v___x_1916_, 1, v___x_1915_);
v___x_1917_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_1918_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1918_, 0, v___x_1880_);
lean_ctor_set(v___x_1918_, 1, v___x_1917_);
v___x_1919_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_1920_ = l_Array_append___redArg(v___x_1919_, v_xs_1879_);
lean_dec_ref(v_xs_1879_);
v___x_1921_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1921_, 0, v___x_1880_);
lean_ctor_set(v___x_1921_, 1, v___x_1874_);
lean_ctor_set(v___x_1921_, 2, v___x_1920_);
v___x_1922_ = l_Lean_Syntax_node2(v___x_1880_, v___x_1874_, v___x_1910_, v___x_1877_);
v___x_1923_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1923_, 0, v___x_1880_);
lean_ctor_set(v___x_1923_, 1, v___x_1874_);
lean_ctor_set(v___x_1923_, 2, v___x_1919_);
v___x_1924_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1925_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1925_, 0, v___x_1880_);
lean_ctor_set(v___x_1925_, 1, v___x_1924_);
lean_inc_ref_n(v___x_1925_, 2);
lean_inc_ref(v___x_1923_);
v___x_1926_ = l_Lean_Syntax_node5(v___x_1880_, v___x_1210_, v___x_1890_, v___x_1921_, v___x_1922_, v___x_1923_, v___x_1925_);
v___x_1927_ = l_Lean_Syntax_node1(v___x_1880_, v___x_1874_, v___x_1926_);
v___x_1928_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_1929_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1929_, 0, v___x_1880_);
lean_ctor_set(v___x_1929_, 1, v___x_1928_);
v___x_1930_ = l_Lean_Syntax_node5(v___x_1880_, v___x_496_, v___x_1918_, v___x_1927_, v___x_1923_, v___x_1929_, v___x_1878_);
v___x_1931_ = l_Lean_Syntax_node3(v___x_1880_, v___x_477_, v___x_1916_, v___x_1930_, v___x_1925_);
v___x_1932_ = l_Lean_Syntax_node4(v___x_1880_, v___x_1902_, v___x_1907_, v___x_1912_, v___x_1914_, v___x_1931_);
v___x_1933_ = l_Lean_Syntax_node2(v___x_1880_, v___x_1900_, v___x_1901_, v___x_1932_);
v___x_1934_ = l_Lean_Syntax_node3(v___x_1880_, v___x_1887_, v___x_1898_, v___x_1933_, v___x_1925_);
v___x_1935_ = l_Lean_Syntax_node1(v___x_1880_, v___x_1874_, v___x_1934_);
v___x_1936_ = l_Lean_Syntax_node2(v___x_1880_, v___x_1881_, v___x_1886_, v___x_1935_);
v___x_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1937_, 0, v___x_1936_);
lean_ctor_set(v___x_1937_, 1, v_a_472_);
return v___x_1937_;
}
}
}
}
}
}
v___jp_1211_:
{
lean_object* v_quotContext_1218_; lean_object* v_currMacroScope_1219_; lean_object* v_ref_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; 
v_quotContext_1218_ = lean_ctor_get(v___y_1216_, 1);
v_currMacroScope_1219_ = lean_ctor_get(v___y_1216_, 2);
v_ref_1220_ = lean_ctor_get(v___y_1216_, 5);
v___x_1221_ = l_Lean_SourceInfo_fromRef(v_ref_1220_, v___x_1157_);
v___x_1222_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_1223_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_1224_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc_n(v_currMacroScope_1219_, 2);
lean_inc_n(v_quotContext_1218_, 2);
v___x_1225_ = l_Lean_addMacroScope(v_quotContext_1218_, v___x_1224_, v_currMacroScope_1219_);
v___x_1226_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc_n(v___x_1221_, 26);
v___x_1227_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1227_, 0, v___x_1221_);
lean_ctor_set(v___x_1227_, 1, v___x_1223_);
lean_ctor_set(v___x_1227_, 2, v___x_1225_);
lean_ctor_set(v___x_1227_, 3, v___x_1226_);
v___x_1228_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1229_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_1230_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_1231_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
v___x_1232_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1232_, 0, v___x_1221_);
lean_ctor_set(v___x_1232_, 1, v___x_1231_);
v___x_1233_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_1234_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_1235_ = lean_box(0);
v___x_1236_ = l_Lean_addMacroScope(v_quotContext_1218_, v___x_1235_, v_currMacroScope_1219_);
v___x_1237_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
v___x_1238_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1238_, 0, v___x_1221_);
lean_ctor_set(v___x_1238_, 1, v___x_1234_);
lean_ctor_set(v___x_1238_, 2, v___x_1236_);
lean_ctor_set(v___x_1238_, 3, v___x_1237_);
v___x_1239_ = l_Lean_Syntax_node1(v___x_1221_, v___x_1233_, v___x_1238_);
lean_inc_ref(v___x_1232_);
v___x_1240_ = l_Lean_Syntax_node2(v___x_1221_, v___x_1230_, v___x_1232_, v___x_1239_);
v___x_1241_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_1242_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
v___x_1243_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1221_);
lean_ctor_set(v___x_1243_, 1, v___x_1241_);
v___x_1244_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_1245_ = l_Lean_Syntax_node1(v___x_1221_, v___x_1228_, v_x_1212_);
v___x_1246_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55));
v___x_1247_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
v___x_1248_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1248_, 0, v___x_1221_);
lean_ctor_set(v___x_1248_, 1, v___x_1247_);
lean_inc(v_ty_1214_);
lean_inc_ref(v___x_1248_);
v___x_1249_ = l_Lean_Syntax_node2(v___x_1221_, v___x_1246_, v___x_1248_, v_ty_1214_);
v___x_1250_ = l_Lean_Syntax_node1(v___x_1221_, v___x_1228_, v___x_1249_);
v___x_1251_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_1252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1221_);
lean_ctor_set(v___x_1252_, 1, v___x_1251_);
v___x_1253_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_1254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1221_);
lean_ctor_set(v___x_1254_, 1, v___x_1253_);
v___x_1255_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_1256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1256_, 0, v___x_1221_);
lean_ctor_set(v___x_1256_, 1, v___x_1255_);
v___x_1257_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_1258_ = l_Array_append___redArg(v___x_1257_, v_xs_1213_);
lean_dec_ref(v_xs_1213_);
v___x_1259_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1259_, 0, v___x_1221_);
lean_ctor_set(v___x_1259_, 1, v___x_1228_);
lean_ctor_set(v___x_1259_, 2, v___x_1258_);
v___x_1260_ = l_Lean_Syntax_node2(v___x_1221_, v___x_1228_, v___x_1248_, v_ty_1214_);
v___x_1261_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1221_);
lean_ctor_set(v___x_1261_, 1, v___x_1228_);
lean_ctor_set(v___x_1261_, 2, v___x_1257_);
v___x_1262_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1263_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1221_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
lean_inc_ref_n(v___x_1263_, 2);
lean_inc_ref(v___x_1261_);
v___x_1264_ = l_Lean_Syntax_node5(v___x_1221_, v___x_1210_, v___x_1232_, v___x_1259_, v___x_1260_, v___x_1261_, v___x_1263_);
v___x_1265_ = l_Lean_Syntax_node1(v___x_1221_, v___x_1228_, v___x_1264_);
v___x_1266_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_1267_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1267_, 0, v___x_1221_);
lean_ctor_set(v___x_1267_, 1, v___x_1266_);
v___x_1268_ = l_Lean_Syntax_node5(v___x_1221_, v___x_496_, v___x_1256_, v___x_1265_, v___x_1261_, v___x_1267_, v_P_1215_);
v___x_1269_ = l_Lean_Syntax_node3(v___x_1221_, v___x_477_, v___x_1254_, v___x_1268_, v___x_1263_);
v___x_1270_ = l_Lean_Syntax_node4(v___x_1221_, v___x_1244_, v___x_1245_, v___x_1250_, v___x_1252_, v___x_1269_);
v___x_1271_ = l_Lean_Syntax_node2(v___x_1221_, v___x_1242_, v___x_1243_, v___x_1270_);
v___x_1272_ = l_Lean_Syntax_node3(v___x_1221_, v___x_1229_, v___x_1240_, v___x_1271_, v___x_1263_);
v___x_1273_ = l_Lean_Syntax_node1(v___x_1221_, v___x_1228_, v___x_1272_);
v___x_1274_ = l_Lean_Syntax_node2(v___x_1221_, v___x_1222_, v___x_1227_, v___x_1273_);
v___x_1275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1275_, 0, v___x_1274_);
lean_ctor_set(v___x_1275_, 1, v___y_1217_);
return v___x_1275_;
}
v___jp_1276_:
{
lean_object* v___x_1281_; uint8_t v___x_1282_; 
v___x_1281_ = l_Lean_Syntax_getNumArgs(v___x_829_);
v___x_1282_ = lean_nat_dec_le(v___x_482_, v___x_1281_);
if (v___x_1282_ == 0)
{
lean_dec(v___x_1281_);
lean_dec(v_____discr_1278_);
lean_dec(v_____discr_1277_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v___y_1280_;
goto v___jp_473_;
}
else
{
if (v___x_1157_ == 0)
{
lean_object* v___x_1283_; uint8_t v___x_1284_; 
v___x_1283_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1000_);
v___x_1284_ = l_Lean_Syntax_isOfKind(v_x_1000_, v___x_1283_);
if (v___x_1284_ == 0)
{
uint8_t v___x_1285_; 
lean_inc(v_x_1000_);
v___x_1285_ = l_Lean_Syntax_isOfKind(v_x_1000_, v___x_1210_);
if (v___x_1285_ == 0)
{
lean_dec(v___x_1281_);
lean_dec(v_____discr_1278_);
lean_dec(v_____discr_1277_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v___y_1280_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1286_; uint8_t v___x_1287_; 
v___x_1286_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_482_);
lean_inc(v___x_1286_);
v___x_1287_ = l_Lean_Syntax_matchesNull(v___x_1286_, v___x_482_);
if (v___x_1287_ == 0)
{
lean_object* v___x_1288_; uint8_t v___x_1289_; 
v___x_1288_ = l_Lean_Syntax_getNumArgs(v___x_1286_);
v___x_1289_ = lean_nat_dec_le(v___x_482_, v___x_1288_);
if (v___x_1289_ == 0)
{
lean_dec(v___x_1288_);
lean_dec(v___x_1286_);
lean_dec(v___x_1281_);
lean_dec(v_____discr_1278_);
lean_dec(v_____discr_1277_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v___y_1280_;
goto v___jp_473_;
}
else
{
lean_object* v_x_1290_; 
v_x_1290_ = l_Lean_Syntax_getArg(v___x_1286_, v___x_481_);
if (v___x_1287_ == 0)
{
uint8_t v___x_1291_; 
lean_inc(v_x_1290_);
v___x_1291_ = l_Lean_Syntax_isOfKind(v_x_1290_, v___x_1283_);
if (v___x_1291_ == 0)
{
lean_dec(v_x_1290_);
lean_dec(v___x_1288_);
lean_dec(v___x_1286_);
lean_dec(v___x_1281_);
lean_dec(v_____discr_1278_);
lean_dec(v_____discr_1277_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v___y_1280_;
goto v___jp_473_;
}
else
{
v___y_1015_ = v_x_1290_;
v___y_1016_ = v_____discr_1277_;
v___y_1017_ = v___y_1279_;
v___y_1018_ = v___x_1281_;
v___y_1019_ = v___x_1286_;
v___y_1020_ = v___y_1280_;
v___y_1021_ = v_____discr_1278_;
v___y_1022_ = v___x_1288_;
goto v___jp_1014_;
}
}
else
{
v___y_1015_ = v_x_1290_;
v___y_1016_ = v_____discr_1277_;
v___y_1017_ = v___y_1279_;
v___y_1018_ = v___x_1281_;
v___y_1019_ = v___x_1286_;
v___y_1020_ = v___y_1280_;
v___y_1021_ = v_____discr_1278_;
v___y_1022_ = v___x_1288_;
goto v___jp_1014_;
}
}
}
else
{
lean_object* v_x_1292_; 
v_x_1292_ = l_Lean_Syntax_getArg(v___x_1286_, v___x_481_);
if (v___x_1157_ == 0)
{
uint8_t v___x_1293_; 
lean_inc(v_x_1292_);
v___x_1293_ = l_Lean_Syntax_isOfKind(v_x_1292_, v___x_1283_);
if (v___x_1293_ == 0)
{
lean_object* v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = l_Lean_Syntax_getNumArgs(v___x_1286_);
v___x_1295_ = lean_nat_dec_le(v___x_482_, v___x_1294_);
if (v___x_1295_ == 0)
{
lean_dec(v___x_1294_);
lean_dec(v_x_1292_);
lean_dec(v___x_1286_);
lean_dec(v___x_1281_);
lean_dec(v_____discr_1278_);
lean_dec(v_____discr_1277_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v___y_1280_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1296_ = lean_unsigned_to_nat(2u);
v___x_1297_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1296_);
v___x_1298_ = lean_unsigned_to_nat(3u);
v___x_1299_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1298_);
lean_dec(v_x_1000_);
v___x_1300_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_1301_ = l_Array_extract___redArg(v___x_1300_, v___x_482_, v___x_1281_);
lean_dec_ref(v___x_1300_);
v___x_1302_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1303_ = lean_box(2);
v___x_1304_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1304_, 0, v___x_1303_);
lean_ctor_set(v___x_1304_, 1, v___x_1302_);
lean_ctor_set(v___x_1304_, 2, v___x_1301_);
if (v___x_1157_ == 0)
{
if (v___x_1293_ == 0)
{
lean_dec_ref_known(v___x_1304_, 3);
lean_dec(v___x_1299_);
lean_dec(v___x_1297_);
lean_dec(v___x_1294_);
lean_dec(v_x_1292_);
lean_dec(v___x_1286_);
lean_dec(v_____discr_1278_);
lean_dec(v_____discr_1277_);
v___y_474_ = v___y_1280_;
goto v___jp_473_;
}
else
{
v___y_747_ = v___x_1294_;
v___y_748_ = v___x_1303_;
v___y_749_ = v___x_1299_;
v___y_750_ = v___x_1304_;
v___y_751_ = v_x_1292_;
v___y_752_ = v___x_1296_;
v___y_753_ = v_____discr_1278_;
v___y_754_ = v___x_1297_;
v___y_755_ = v_____discr_1277_;
v___y_756_ = v___y_1279_;
v___y_757_ = v___x_1302_;
v___y_758_ = v___x_1286_;
v___y_759_ = v___y_1280_;
goto v___jp_746_;
}
}
else
{
v___y_747_ = v___x_1294_;
v___y_748_ = v___x_1303_;
v___y_749_ = v___x_1299_;
v___y_750_ = v___x_1304_;
v___y_751_ = v_x_1292_;
v___y_752_ = v___x_1296_;
v___y_753_ = v_____discr_1278_;
v___y_754_ = v___x_1297_;
v___y_755_ = v_____discr_1277_;
v___y_756_ = v___y_1279_;
v___y_757_ = v___x_1302_;
v___y_758_ = v___x_1286_;
v___y_759_ = v___y_1280_;
goto v___jp_746_;
}
}
}
else
{
v___y_1042_ = v_____discr_1277_;
v___y_1043_ = v___y_1279_;
v___y_1044_ = v___x_1283_;
v___y_1045_ = v___x_1281_;
v___y_1046_ = v___x_1286_;
v___y_1047_ = v_x_1292_;
v___y_1048_ = v___y_1280_;
v___y_1049_ = v_____discr_1278_;
goto v___jp_1041_;
}
}
else
{
v___y_1042_ = v_____discr_1277_;
v___y_1043_ = v___y_1279_;
v___y_1044_ = v___x_1283_;
v___y_1045_ = v___x_1281_;
v___y_1046_ = v___x_1286_;
v___y_1047_ = v_x_1292_;
v___y_1048_ = v___y_1280_;
v___y_1049_ = v_____discr_1278_;
goto v___jp_1041_;
}
}
}
}
else
{
v___y_1002_ = v_____discr_1277_;
v___y_1003_ = v___y_1279_;
v___y_1004_ = v___x_1281_;
v___y_1005_ = v___y_1280_;
v___y_1006_ = v_____discr_1278_;
goto v___jp_1001_;
}
}
else
{
v___y_1002_ = v_____discr_1277_;
v___y_1003_ = v___y_1279_;
v___y_1004_ = v___x_1281_;
v___y_1005_ = v___y_1280_;
v___y_1006_ = v_____discr_1278_;
goto v___jp_1001_;
}
}
}
v___jp_1306_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; uint8_t v___x_1309_; 
v___x_1307_ = lean_unsigned_to_nat(2u);
v___x_1308_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1307_);
v___x_1309_ = l_Lean_Syntax_matchesNull(v___x_1308_, v___x_481_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1310_; uint8_t v___x_1311_; 
v___x_1310_ = l_Lean_Syntax_getNumArgs(v___x_829_);
v___x_1311_ = lean_nat_dec_le(v___x_482_, v___x_1310_);
if (v___x_1311_ == 0)
{
lean_dec(v___x_1310_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1312_; lean_object* v_P_1313_; 
v___x_1312_ = lean_unsigned_to_nat(4u);
v_P_1313_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1312_);
lean_dec(v___x_483_);
if (v___x_1309_ == 0)
{
lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1314_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1000_);
v___x_1315_ = l_Lean_Syntax_isOfKind(v_x_1000_, v___x_1314_);
if (v___x_1315_ == 0)
{
if (v___x_1305_ == 0)
{
lean_dec(v_P_1313_);
lean_dec(v___x_1310_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1316_; lean_object* v___x_1317_; uint8_t v___x_1318_; 
v___x_1316_ = lean_unsigned_to_nat(3u);
v___x_1317_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_482_);
lean_inc(v___x_1317_);
v___x_1318_ = l_Lean_Syntax_matchesNull(v___x_1317_, v___x_482_);
if (v___x_1318_ == 0)
{
lean_object* v___x_1319_; uint8_t v___x_1320_; 
v___x_1319_ = l_Lean_Syntax_getNumArgs(v___x_1317_);
v___x_1320_ = lean_nat_dec_le(v___x_482_, v___x_1319_);
if (v___x_1320_ == 0)
{
lean_dec(v___x_1319_);
lean_dec(v___x_1317_);
lean_dec(v_P_1313_);
lean_dec(v___x_1310_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v_x_1321_; 
v_x_1321_ = l_Lean_Syntax_getArg(v___x_1317_, v___x_481_);
if (v___x_1318_ == 0)
{
uint8_t v___x_1322_; 
lean_inc(v_x_1321_);
v___x_1322_ = l_Lean_Syntax_isOfKind(v_x_1321_, v___x_1314_);
if (v___x_1322_ == 0)
{
lean_dec(v_x_1321_);
lean_dec(v___x_1319_);
lean_dec(v___x_1317_);
lean_dec(v_P_1313_);
lean_dec(v___x_1310_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
v___y_1096_ = v___x_1310_;
v___y_1097_ = v___x_1319_;
v___y_1098_ = v_P_1313_;
v___y_1099_ = v_x_1321_;
v___y_1100_ = v___x_1317_;
v___y_1101_ = v___x_1316_;
v___y_1102_ = v___x_1309_;
v___y_1103_ = v___x_1307_;
goto v___jp_1095_;
}
}
else
{
v___y_1096_ = v___x_1310_;
v___y_1097_ = v___x_1319_;
v___y_1098_ = v_P_1313_;
v___y_1099_ = v_x_1321_;
v___y_1100_ = v___x_1317_;
v___y_1101_ = v___x_1316_;
v___y_1102_ = v___x_1309_;
v___y_1103_ = v___x_1307_;
goto v___jp_1095_;
}
}
}
else
{
lean_object* v_x_1323_; 
v_x_1323_ = l_Lean_Syntax_getArg(v___x_1317_, v___x_481_);
if (v___x_1309_ == 0)
{
uint8_t v___x_1324_; 
lean_inc(v_x_1323_);
v___x_1324_ = l_Lean_Syntax_isOfKind(v_x_1323_, v___x_1314_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; uint8_t v___x_1326_; 
v___x_1325_ = l_Lean_Syntax_getNumArgs(v___x_1317_);
v___x_1326_ = lean_nat_dec_le(v___x_482_, v___x_1325_);
if (v___x_1326_ == 0)
{
lean_dec(v___x_1325_);
lean_dec(v_x_1323_);
lean_dec(v___x_1317_);
lean_dec(v_P_1313_);
lean_dec(v___x_1310_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; 
v___x_1327_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1307_);
v___x_1328_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1316_);
lean_dec(v_x_1000_);
v___x_1329_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_1330_ = l_Array_extract___redArg(v___x_1329_, v___x_482_, v___x_1310_);
lean_dec_ref(v___x_1329_);
v___x_1331_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1332_ = lean_box(2);
v___x_1333_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1333_, 0, v___x_1332_);
lean_ctor_set(v___x_1333_, 1, v___x_1331_);
lean_ctor_set(v___x_1333_, 2, v___x_1330_);
if (v___x_1309_ == 0)
{
if (v___x_1324_ == 0)
{
lean_dec_ref_known(v___x_1333_, 3);
lean_dec(v___x_1328_);
lean_dec(v___x_1327_);
lean_dec(v___x_1325_);
lean_dec(v_x_1323_);
lean_dec(v___x_1317_);
lean_dec(v_P_1313_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
v___y_807_ = v_P_1313_;
v___y_808_ = v_x_1323_;
v___y_809_ = v___x_1327_;
v___y_810_ = v___x_1331_;
v___y_811_ = v___x_1317_;
v___y_812_ = v___x_1332_;
v___y_813_ = v___x_1325_;
v___y_814_ = v___x_1333_;
v___y_815_ = v___x_1309_;
v___y_816_ = v___x_1328_;
v___y_817_ = v___x_1307_;
goto v___jp_806_;
}
}
else
{
v___y_807_ = v_P_1313_;
v___y_808_ = v_x_1323_;
v___y_809_ = v___x_1327_;
v___y_810_ = v___x_1331_;
v___y_811_ = v___x_1317_;
v___y_812_ = v___x_1332_;
v___y_813_ = v___x_1325_;
v___y_814_ = v___x_1333_;
v___y_815_ = v___x_1309_;
v___y_816_ = v___x_1328_;
v___y_817_ = v___x_1307_;
goto v___jp_806_;
}
}
}
else
{
v___y_1120_ = v___x_1314_;
v___y_1121_ = v___x_1310_;
v___y_1122_ = v_x_1323_;
v___y_1123_ = v_P_1313_;
v___y_1124_ = v___x_1317_;
v___y_1125_ = v___x_1316_;
v___y_1126_ = v___x_1309_;
v___y_1127_ = v___x_1307_;
goto v___jp_1119_;
}
}
else
{
v___y_1120_ = v___x_1314_;
v___y_1121_ = v___x_1310_;
v___y_1122_ = v_x_1323_;
v___y_1123_ = v_P_1313_;
v___y_1124_ = v___x_1317_;
v___y_1125_ = v___x_1316_;
v___y_1126_ = v___x_1309_;
v___y_1127_ = v___x_1307_;
goto v___jp_1119_;
}
}
}
}
else
{
v___y_1086_ = v___x_1310_;
v___y_1087_ = v_P_1313_;
v___y_1088_ = v___x_1309_;
goto v___jp_1085_;
}
}
else
{
v___y_1086_ = v___x_1310_;
v___y_1087_ = v_P_1313_;
v___y_1088_ = v___x_1309_;
goto v___jp_1085_;
}
}
}
else
{
lean_object* v_quotContext_1334_; lean_object* v_currMacroScope_1335_; lean_object* v_ref_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; 
lean_dec(v___x_829_);
v_quotContext_1334_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_1335_ = lean_ctor_get(v_a_471_, 2);
v_ref_1336_ = lean_ctor_get(v_a_471_, 5);
v___x_1337_ = lean_unsigned_to_nat(4u);
v___x_1338_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1337_);
lean_dec(v___x_483_);
v___x_1339_ = l_Lean_SourceInfo_fromRef(v_ref_1336_, v___x_1305_);
v___x_1340_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_1341_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_1342_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc_n(v_currMacroScope_1335_, 2);
lean_inc_n(v_quotContext_1334_, 2);
v___x_1343_ = l_Lean_addMacroScope(v_quotContext_1334_, v___x_1342_, v_currMacroScope_1335_);
v___x_1344_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc_n(v___x_1339_, 16);
v___x_1345_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1345_, 0, v___x_1339_);
lean_ctor_set(v___x_1345_, 1, v___x_1341_);
lean_ctor_set(v___x_1345_, 2, v___x_1343_);
lean_ctor_set(v___x_1345_, 3, v___x_1344_);
v___x_1346_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1347_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_1348_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_1349_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
v___x_1350_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1350_, 0, v___x_1339_);
lean_ctor_set(v___x_1350_, 1, v___x_1349_);
v___x_1351_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_1352_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_1353_ = lean_box(0);
v___x_1354_ = l_Lean_addMacroScope(v_quotContext_1334_, v___x_1353_, v_currMacroScope_1335_);
v___x_1355_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
v___x_1356_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1356_, 0, v___x_1339_);
lean_ctor_set(v___x_1356_, 1, v___x_1352_);
lean_ctor_set(v___x_1356_, 2, v___x_1354_);
lean_ctor_set(v___x_1356_, 3, v___x_1355_);
v___x_1357_ = l_Lean_Syntax_node1(v___x_1339_, v___x_1351_, v___x_1356_);
v___x_1358_ = l_Lean_Syntax_node2(v___x_1339_, v___x_1348_, v___x_1350_, v___x_1357_);
v___x_1359_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_1360_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
v___x_1361_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1361_, 0, v___x_1339_);
lean_ctor_set(v___x_1361_, 1, v___x_1359_);
v___x_1362_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_1363_ = l_Lean_Syntax_node1(v___x_1339_, v___x_1346_, v_x_1000_);
v___x_1364_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_1365_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1339_);
lean_ctor_set(v___x_1365_, 1, v___x_1346_);
lean_ctor_set(v___x_1365_, 2, v___x_1364_);
v___x_1366_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_1367_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1367_, 0, v___x_1339_);
lean_ctor_set(v___x_1367_, 1, v___x_1366_);
v___x_1368_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_1369_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1369_, 0, v___x_1339_);
lean_ctor_set(v___x_1369_, 1, v___x_1368_);
v___x_1370_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1371_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1371_, 0, v___x_1339_);
lean_ctor_set(v___x_1371_, 1, v___x_1370_);
lean_inc_ref(v___x_1371_);
v___x_1372_ = l_Lean_Syntax_node3(v___x_1339_, v___x_477_, v___x_1369_, v___x_1338_, v___x_1371_);
v___x_1373_ = l_Lean_Syntax_node4(v___x_1339_, v___x_1362_, v___x_1363_, v___x_1365_, v___x_1367_, v___x_1372_);
v___x_1374_ = l_Lean_Syntax_node2(v___x_1339_, v___x_1360_, v___x_1361_, v___x_1373_);
v___x_1375_ = l_Lean_Syntax_node3(v___x_1339_, v___x_1347_, v___x_1358_, v___x_1374_, v___x_1371_);
v___x_1376_ = l_Lean_Syntax_node1(v___x_1339_, v___x_1346_, v___x_1375_);
v___x_1377_ = l_Lean_Syntax_node2(v___x_1339_, v___x_1340_, v___x_1345_, v___x_1376_);
v___x_1378_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1378_, 0, v___x_1377_);
lean_ctor_set(v___x_1378_, 1, v_a_472_);
return v___x_1378_;
}
}
}
else
{
lean_object* v_tk_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; uint8_t v___x_1941_; 
v_tk_1938_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_481_);
v___x_1939_ = lean_unsigned_to_nat(2u);
v___x_1940_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1939_);
lean_inc(v___x_1940_);
v___x_1941_ = l_Lean_Syntax_matchesNull(v___x_1940_, v___x_481_);
if (v___x_1941_ == 0)
{
uint8_t v___x_1942_; 
lean_inc(v___x_1940_);
v___x_1942_ = l_Lean_Syntax_matchesNull(v___x_1940_, v___x_482_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; uint8_t v___x_1944_; 
lean_dec(v___x_1940_);
lean_dec(v_tk_1938_);
v___x_1943_ = l_Lean_Syntax_getNumArgs(v___x_829_);
v___x_1944_ = lean_nat_dec_le(v___x_482_, v___x_1943_);
if (v___x_1944_ == 0)
{
lean_dec(v___x_1943_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1945_; lean_object* v_P_1946_; 
v___x_1945_ = lean_unsigned_to_nat(4u);
v_P_1946_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1945_);
lean_dec(v___x_483_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1954_; uint8_t v___x_1955_; 
v___x_1954_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1000_);
v___x_1955_ = l_Lean_Syntax_isOfKind(v_x_1000_, v___x_1954_);
if (v___x_1955_ == 0)
{
lean_object* v___x_1956_; uint8_t v___x_1957_; 
v___x_1956_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58));
lean_inc(v_x_1000_);
v___x_1957_ = l_Lean_Syntax_isOfKind(v_x_1000_, v___x_1956_);
if (v___x_1957_ == 0)
{
lean_dec(v_P_1946_);
lean_dec(v___x_1943_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1958_; lean_object* v___x_1959_; uint8_t v___x_1960_; 
v___x_1958_ = lean_unsigned_to_nat(3u);
v___x_1959_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_482_);
lean_inc(v___x_1959_);
v___x_1960_ = l_Lean_Syntax_matchesNull(v___x_1959_, v___x_482_);
if (v___x_1960_ == 0)
{
lean_object* v___x_1961_; uint8_t v___x_1962_; 
v___x_1961_ = l_Lean_Syntax_getNumArgs(v___x_1959_);
v___x_1962_ = lean_nat_dec_le(v___x_482_, v___x_1961_);
if (v___x_1962_ == 0)
{
lean_dec(v___x_1961_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
lean_dec(v___x_1943_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v_x_1963_; 
v_x_1963_ = l_Lean_Syntax_getArg(v___x_1959_, v___x_481_);
if (v___x_1960_ == 0)
{
uint8_t v___x_1980_; 
lean_inc(v_x_1963_);
v___x_1980_ = l_Lean_Syntax_isOfKind(v_x_1963_, v___x_1954_);
if (v___x_1980_ == 0)
{
lean_dec(v_x_1963_);
lean_dec(v___x_1961_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
lean_dec(v___x_1943_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
goto v___jp_1964_;
}
}
else
{
goto v___jp_1964_;
}
v___jp_1964_:
{
lean_object* v___x_1965_; uint8_t v___x_1966_; 
v___x_1965_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1939_);
lean_inc(v___x_1965_);
v___x_1966_ = l_Lean_Syntax_matchesNull(v___x_1965_, v___x_1939_);
if (v___x_1966_ == 0)
{
lean_dec(v___x_1965_);
lean_dec(v_x_1963_);
lean_dec(v___x_1961_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
lean_dec(v___x_1943_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1967_; uint8_t v___x_1968_; 
v___x_1967_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1958_);
lean_dec(v_x_1000_);
v___x_1968_ = l_Lean_Syntax_matchesNull(v___x_1967_, v___x_481_);
if (v___x_1968_ == 0)
{
lean_dec(v___x_1965_);
lean_dec(v_x_1963_);
lean_dec(v___x_1961_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
lean_dec(v___x_1943_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1941_ == 0)
{
lean_dec(v___x_1965_);
lean_dec(v_x_1963_);
lean_dec(v___x_1961_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
lean_dec(v___x_1943_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v_ty_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v_ys_1978_; lean_object* v_xs_1979_; 
v___x_1969_ = l_Lean_Syntax_getArgs(v___x_1959_);
lean_dec(v___x_1959_);
v___x_1970_ = l_Array_extract___redArg(v___x_1969_, v___x_482_, v___x_1961_);
lean_dec_ref(v___x_1969_);
v_ty_1971_ = l_Lean_Syntax_getArg(v___x_1965_, v___x_482_);
lean_dec(v___x_1965_);
v___x_1972_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1973_ = lean_box(2);
v___x_1974_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1974_, 0, v___x_1973_);
lean_ctor_set(v___x_1974_, 1, v___x_1972_);
lean_ctor_set(v___x_1974_, 2, v___x_1970_);
v___x_1975_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_1976_ = l_Array_extract___redArg(v___x_1975_, v___x_482_, v___x_1943_);
lean_dec_ref(v___x_1975_);
v___x_1977_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1973_);
lean_ctor_set(v___x_1977_, 1, v___x_1972_);
lean_ctor_set(v___x_1977_, 2, v___x_1976_);
v_ys_1978_ = l_Lean_Syntax_getArgs(v___x_1977_);
lean_dec_ref_known(v___x_1977_, 3);
v_xs_1979_ = l_Lean_Syntax_getArgs(v___x_1974_);
lean_dec_ref_known(v___x_1974_, 3);
v_x_616_ = v_x_1963_;
v_xs_617_ = v_xs_1979_;
v_ty_618_ = v_ty_1971_;
v_ys_619_ = v_ys_1978_;
v_P_620_ = v_P_1946_;
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
lean_object* v_x_1981_; lean_object* v___y_1983_; uint8_t v___y_1984_; lean_object* v___y_1985_; lean_object* v___y_1986_; lean_object* v___y_1987_; lean_object* v___y_1988_; lean_object* v___y_1989_; uint8_t v___y_1998_; lean_object* v___y_1999_; lean_object* v___y_2000_; uint8_t v___y_2001_; lean_object* v___y_2002_; lean_object* v___y_2003_; lean_object* v___y_2004_; lean_object* v___y_2012_; uint8_t v___y_2013_; lean_object* v___y_2014_; uint8_t v___y_2015_; lean_object* v___y_2016_; lean_object* v___y_2017_; lean_object* v___y_2018_; 
v_x_1981_ = l_Lean_Syntax_getArg(v___x_1959_, v___x_481_);
if (v___x_1942_ == 0)
{
uint8_t v___x_2056_; 
lean_inc(v_x_1981_);
v___x_2056_ = l_Lean_Syntax_isOfKind(v_x_1981_, v___x_1954_);
if (v___x_2056_ == 0)
{
lean_object* v___x_2057_; uint8_t v___x_2058_; 
v___x_2057_ = l_Lean_Syntax_getNumArgs(v___x_1959_);
v___x_2058_ = lean_nat_dec_le(v___x_482_, v___x_2057_);
if (v___x_2058_ == 0)
{
lean_dec(v___x_2057_);
lean_dec(v_x_1981_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
lean_dec(v___x_1943_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2059_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1939_);
v___x_2060_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1958_);
lean_dec(v_x_1000_);
v___x_2061_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_2062_ = l_Array_extract___redArg(v___x_2061_, v___x_482_, v___x_1943_);
lean_dec_ref(v___x_2061_);
v___x_2063_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2064_ = lean_box(2);
v___x_2065_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2065_, 0, v___x_2064_);
lean_ctor_set(v___x_2065_, 1, v___x_2063_);
lean_ctor_set(v___x_2065_, 2, v___x_2062_);
if (v___x_1942_ == 0)
{
if (v___x_2056_ == 0)
{
lean_dec_ref_known(v___x_2065_, 3);
lean_dec(v___x_2060_);
lean_dec(v___x_2059_);
lean_dec(v___x_2057_);
lean_dec(v_x_1981_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
goto v___jp_2066_;
}
}
else
{
goto v___jp_2066_;
}
v___jp_2066_:
{
uint8_t v___x_2067_; 
lean_inc(v___x_2059_);
v___x_2067_ = l_Lean_Syntax_matchesNull(v___x_2059_, v___x_1939_);
if (v___x_2067_ == 0)
{
lean_dec_ref_known(v___x_2065_, 3);
lean_dec(v___x_2060_);
lean_dec(v___x_2059_);
lean_dec(v___x_2057_);
lean_dec(v_x_1981_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
uint8_t v___x_2068_; 
v___x_2068_ = l_Lean_Syntax_matchesNull(v___x_2060_, v___x_481_);
if (v___x_2068_ == 0)
{
lean_dec_ref_known(v___x_2065_, 3);
lean_dec(v___x_2059_);
lean_dec(v___x_2057_);
lean_dec(v_x_1981_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1941_ == 0)
{
lean_dec_ref_known(v___x_2065_, 3);
lean_dec(v___x_2059_);
lean_dec(v___x_2057_);
lean_dec(v_x_1981_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v_ty_2072_; lean_object* v_ys_2073_; lean_object* v_xs_2074_; 
v___x_2069_ = l_Lean_Syntax_getArgs(v___x_1959_);
lean_dec(v___x_1959_);
v___x_2070_ = l_Array_extract___redArg(v___x_2069_, v___x_482_, v___x_2057_);
lean_dec_ref(v___x_2069_);
v___x_2071_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2071_, 0, v___x_2064_);
lean_ctor_set(v___x_2071_, 1, v___x_2063_);
lean_ctor_set(v___x_2071_, 2, v___x_2070_);
v_ty_2072_ = l_Lean_Syntax_getArg(v___x_2059_, v___x_482_);
lean_dec(v___x_2059_);
v_ys_2073_ = l_Lean_Syntax_getArgs(v___x_2065_);
lean_dec_ref_known(v___x_2065_, 3);
v_xs_2074_ = l_Lean_Syntax_getArgs(v___x_2071_);
lean_dec_ref_known(v___x_2071_, 3);
v_x_616_ = v_x_1981_;
v_xs_617_ = v_xs_2074_;
v_ty_618_ = v_ty_2072_;
v_ys_619_ = v_ys_2073_;
v_P_620_ = v_P_1946_;
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
goto v___jp_2024_;
}
}
else
{
goto v___jp_2024_;
}
v___jp_1982_:
{
if (v___y_1984_ == 0)
{
lean_dec(v___y_1989_);
lean_dec(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec(v___y_1985_);
lean_dec(v_x_1981_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
uint8_t v___x_1990_; 
v___x_1990_ = l_Lean_Syntax_matchesNull(v___y_1989_, v___x_481_);
if (v___x_1990_ == 0)
{
lean_dec(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec(v___y_1985_);
lean_dec(v_x_1981_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1941_ == 0)
{
lean_dec(v___y_1988_);
lean_dec(v___y_1987_);
lean_dec(v___y_1985_);
lean_dec(v_x_1981_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; lean_object* v_ty_1994_; lean_object* v_ys_1995_; lean_object* v_xs_1996_; 
v___x_1991_ = l_Lean_Syntax_getArgs(v___x_1959_);
lean_dec(v___x_1959_);
v___x_1992_ = l_Array_extract___redArg(v___x_1991_, v___x_482_, v___y_1988_);
lean_dec_ref(v___x_1991_);
lean_inc(v___y_1986_);
lean_inc(v___y_1983_);
v___x_1993_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1993_, 0, v___y_1983_);
lean_ctor_set(v___x_1993_, 1, v___y_1986_);
lean_ctor_set(v___x_1993_, 2, v___x_1992_);
v_ty_1994_ = l_Lean_Syntax_getArg(v___y_1987_, v___x_482_);
lean_dec(v___y_1987_);
v_ys_1995_ = l_Lean_Syntax_getArgs(v___y_1985_);
lean_dec(v___y_1985_);
v_xs_1996_ = l_Lean_Syntax_getArgs(v___x_1993_);
lean_dec_ref_known(v___x_1993_, 3);
v_x_616_ = v_x_1981_;
v_xs_617_ = v_xs_1996_;
v_ty_618_ = v_ty_1994_;
v_ys_619_ = v_ys_1995_;
v_P_620_ = v_P_1946_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
v___jp_1997_:
{
if (v___y_1998_ == 0)
{
lean_dec(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec(v___y_2000_);
lean_dec(v_x_1981_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___y_2001_ == 0)
{
lean_dec(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec(v___y_2000_);
lean_dec(v_x_1981_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1941_ == 0)
{
lean_dec(v___y_2004_);
lean_dec(v___y_2003_);
lean_dec(v___y_2000_);
lean_dec(v_x_1981_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v_ty_2008_; lean_object* v_ys_2009_; lean_object* v_xs_2010_; 
v___x_2005_ = l_Lean_Syntax_getArgs(v___x_1959_);
lean_dec(v___x_1959_);
v___x_2006_ = l_Array_extract___redArg(v___x_2005_, v___x_482_, v___y_2003_);
lean_dec_ref(v___x_2005_);
lean_inc(v___y_1999_);
lean_inc(v___y_2002_);
v___x_2007_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2007_, 0, v___y_2002_);
lean_ctor_set(v___x_2007_, 1, v___y_1999_);
lean_ctor_set(v___x_2007_, 2, v___x_2006_);
v_ty_2008_ = l_Lean_Syntax_getArg(v___y_2000_, v___x_482_);
lean_dec(v___y_2000_);
v_ys_2009_ = l_Lean_Syntax_getArgs(v___y_2004_);
lean_dec(v___y_2004_);
v_xs_2010_ = l_Lean_Syntax_getArgs(v___x_2007_);
lean_dec_ref_known(v___x_2007_, 3);
v_x_616_ = v_x_1981_;
v_xs_617_ = v_xs_2010_;
v_ty_618_ = v_ty_2008_;
v_ys_619_ = v_ys_2009_;
v_P_620_ = v_P_1946_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
v___jp_2011_:
{
if (v___y_2013_ == 0)
{
lean_dec(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec(v___y_2014_);
lean_dec(v_x_1981_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___y_2015_ == 0)
{
lean_dec(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec(v___y_2014_);
lean_dec(v_x_1981_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1941_ == 0)
{
lean_dec(v___y_2017_);
lean_dec(v___y_2016_);
lean_dec(v___y_2014_);
lean_dec(v_x_1981_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v_ys_2022_; lean_object* v_xs_2023_; 
v___x_2019_ = l_Lean_Syntax_getArgs(v___x_1959_);
lean_dec(v___x_1959_);
v___x_2020_ = l_Array_extract___redArg(v___x_2019_, v___x_482_, v___y_2016_);
lean_dec_ref(v___x_2019_);
lean_inc(v___y_2012_);
lean_inc(v___y_2018_);
v___x_2021_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2021_, 0, v___y_2018_);
lean_ctor_set(v___x_2021_, 1, v___y_2012_);
lean_ctor_set(v___x_2021_, 2, v___x_2020_);
v_ys_2022_ = l_Lean_Syntax_getArgs(v___y_2017_);
lean_dec(v___y_2017_);
v_xs_2023_ = l_Lean_Syntax_getArgs(v___x_2021_);
lean_dec_ref_known(v___x_2021_, 3);
v_x_616_ = v_x_1981_;
v_xs_617_ = v_xs_2023_;
v_ty_618_ = v___y_2014_;
v_ys_619_ = v_ys_2022_;
v_P_620_ = v_P_1946_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
v___jp_2024_:
{
lean_object* v___x_2025_; uint8_t v___x_2026_; 
v___x_2025_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1939_);
lean_inc(v___x_2025_);
v___x_2026_ = l_Lean_Syntax_matchesNull(v___x_2025_, v___x_1939_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; uint8_t v___x_2028_; 
v___x_2027_ = l_Lean_Syntax_getNumArgs(v___x_1959_);
v___x_2028_ = lean_nat_dec_le(v___x_482_, v___x_2027_);
if (v___x_2028_ == 0)
{
lean_dec(v___x_2027_);
lean_dec(v___x_2025_);
lean_dec(v_x_1981_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
lean_dec(v___x_1943_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2029_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1958_);
lean_dec(v_x_1000_);
v___x_2030_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_2031_ = l_Array_extract___redArg(v___x_2030_, v___x_482_, v___x_1943_);
lean_dec_ref(v___x_2030_);
v___x_2032_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2033_ = lean_box(2);
v___x_2034_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
lean_ctor_set(v___x_2034_, 1, v___x_2032_);
lean_ctor_set(v___x_2034_, 2, v___x_2031_);
if (v___x_2026_ == 0)
{
uint8_t v___x_2035_; 
lean_inc(v_x_1981_);
v___x_2035_ = l_Lean_Syntax_isOfKind(v_x_1981_, v___x_1954_);
if (v___x_2035_ == 0)
{
lean_dec_ref_known(v___x_2034_, 3);
lean_dec(v___x_2029_);
lean_dec(v___x_2027_);
lean_dec(v___x_2025_);
lean_dec(v_x_1981_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
v___y_1983_ = v___x_2033_;
v___y_1984_ = v___x_2026_;
v___y_1985_ = v___x_2034_;
v___y_1986_ = v___x_2032_;
v___y_1987_ = v___x_2025_;
v___y_1988_ = v___x_2027_;
v___y_1989_ = v___x_2029_;
goto v___jp_1982_;
}
}
else
{
v___y_1983_ = v___x_2033_;
v___y_1984_ = v___x_2026_;
v___y_1985_ = v___x_2034_;
v___y_1986_ = v___x_2032_;
v___y_1987_ = v___x_2025_;
v___y_1988_ = v___x_2027_;
v___y_1989_ = v___x_2029_;
goto v___jp_1982_;
}
}
}
else
{
lean_object* v___x_2036_; uint8_t v___x_2037_; 
v___x_2036_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1958_);
lean_dec(v_x_1000_);
v___x_2037_ = l_Lean_Syntax_matchesNull(v___x_2036_, v___x_481_);
if (v___x_2037_ == 0)
{
lean_object* v___x_2038_; uint8_t v___x_2039_; 
v___x_2038_ = l_Lean_Syntax_getNumArgs(v___x_1959_);
v___x_2039_ = lean_nat_dec_le(v___x_482_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_dec(v___x_2038_);
lean_dec(v___x_2025_);
lean_dec(v_x_1981_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
lean_dec(v___x_1943_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2040_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_2041_ = l_Array_extract___redArg(v___x_2040_, v___x_482_, v___x_1943_);
lean_dec_ref(v___x_2040_);
v___x_2042_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2043_ = lean_box(2);
v___x_2044_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2044_, 0, v___x_2043_);
lean_ctor_set(v___x_2044_, 1, v___x_2042_);
lean_ctor_set(v___x_2044_, 2, v___x_2041_);
if (v___x_2037_ == 0)
{
uint8_t v___x_2045_; 
lean_inc(v_x_1981_);
v___x_2045_ = l_Lean_Syntax_isOfKind(v_x_1981_, v___x_1954_);
if (v___x_2045_ == 0)
{
lean_dec_ref_known(v___x_2044_, 3);
lean_dec(v___x_2038_);
lean_dec(v___x_2025_);
lean_dec(v_x_1981_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
v___y_1998_ = v___x_2026_;
v___y_1999_ = v___x_2042_;
v___y_2000_ = v___x_2025_;
v___y_2001_ = v___x_2037_;
v___y_2002_ = v___x_2043_;
v___y_2003_ = v___x_2038_;
v___y_2004_ = v___x_2044_;
goto v___jp_1997_;
}
}
else
{
v___y_1998_ = v___x_2026_;
v___y_1999_ = v___x_2042_;
v___y_2000_ = v___x_2025_;
v___y_2001_ = v___x_2037_;
v___y_2002_ = v___x_2043_;
v___y_2003_ = v___x_2038_;
v___y_2004_ = v___x_2044_;
goto v___jp_1997_;
}
}
}
else
{
lean_object* v_ty_2046_; lean_object* v___x_2047_; lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; 
v_ty_2046_ = l_Lean_Syntax_getArg(v___x_2025_, v___x_482_);
lean_dec(v___x_2025_);
v___x_2047_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_2048_ = l_Array_extract___redArg(v___x_2047_, v___x_482_, v___x_1943_);
lean_dec_ref(v___x_2047_);
v___x_2049_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2050_ = lean_box(2);
v___x_2051_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2051_, 0, v___x_2050_);
lean_ctor_set(v___x_2051_, 1, v___x_2049_);
lean_ctor_set(v___x_2051_, 2, v___x_2048_);
if (v___x_1941_ == 0)
{
lean_object* v___x_2052_; uint8_t v___x_2053_; 
v___x_2052_ = l_Lean_Syntax_getNumArgs(v___x_1959_);
v___x_2053_ = lean_nat_dec_le(v___x_482_, v___x_2052_);
if (v___x_2053_ == 0)
{
lean_dec(v___x_2052_);
lean_dec_ref_known(v___x_2051_, 3);
lean_dec(v_ty_2046_);
lean_dec(v_x_1981_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1941_ == 0)
{
uint8_t v___x_2054_; 
lean_inc(v_x_1981_);
v___x_2054_ = l_Lean_Syntax_isOfKind(v_x_1981_, v___x_1954_);
if (v___x_2054_ == 0)
{
lean_dec(v___x_2052_);
lean_dec_ref_known(v___x_2051_, 3);
lean_dec(v_ty_2046_);
lean_dec(v_x_1981_);
lean_dec(v___x_1959_);
lean_dec(v_P_1946_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
v___y_2012_ = v___x_2049_;
v___y_2013_ = v___x_2026_;
v___y_2014_ = v_ty_2046_;
v___y_2015_ = v___x_2037_;
v___y_2016_ = v___x_2052_;
v___y_2017_ = v___x_2051_;
v___y_2018_ = v___x_2050_;
goto v___jp_2011_;
}
}
else
{
v___y_2012_ = v___x_2049_;
v___y_2013_ = v___x_2026_;
v___y_2014_ = v_ty_2046_;
v___y_2015_ = v___x_2037_;
v___y_2016_ = v___x_2052_;
v___y_2017_ = v___x_2051_;
v___y_2018_ = v___x_2050_;
goto v___jp_2011_;
}
}
}
else
{
lean_object* v_xs_2055_; 
lean_dec(v___x_1959_);
v_xs_2055_ = l_Lean_Syntax_getArgs(v___x_2051_);
lean_dec_ref_known(v___x_2051_, 3);
v_x_554_ = v_x_1981_;
v_ty_555_ = v_ty_2046_;
v_xs_556_ = v_xs_2055_;
v_P_557_ = v_P_1946_;
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
goto v___jp_1947_;
}
}
else
{
goto v___jp_1947_;
}
v___jp_1947_:
{
if (v___x_1941_ == 0)
{
lean_dec(v_P_1946_);
lean_dec(v___x_1943_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v_xs_1953_; 
v___x_1948_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_1949_ = l_Array_extract___redArg(v___x_1948_, v___x_482_, v___x_1943_);
lean_dec_ref(v___x_1948_);
v___x_1950_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1951_ = lean_box(2);
v___x_1952_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1952_, 0, v___x_1951_);
lean_ctor_set(v___x_1952_, 1, v___x_1950_);
lean_ctor_set(v___x_1952_, 2, v___x_1949_);
v_xs_1953_ = l_Lean_Syntax_getArgs(v___x_1952_);
lean_dec_ref_known(v___x_1952_, 3);
v_x_498_ = v_x_1000_;
v_xs_499_ = v_xs_1953_;
v_P_500_ = v_P_1946_;
v___y_501_ = v_a_471_;
v___y_502_ = v_a_472_;
goto v___jp_497_;
}
}
}
}
else
{
lean_object* v___x_2075_; lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2075_ = l_Lean_Syntax_getArg(v___x_1940_, v___x_481_);
lean_dec(v___x_1940_);
v___x_2076_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55));
lean_inc(v___x_2075_);
v___x_2077_ = l_Lean_Syntax_isOfKind(v___x_2075_, v___x_2076_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; uint8_t v___x_2079_; 
lean_dec(v___x_2075_);
lean_dec(v_tk_1938_);
v___x_2078_ = l_Lean_Syntax_getNumArgs(v___x_829_);
v___x_2079_ = lean_nat_dec_le(v___x_482_, v___x_2078_);
if (v___x_2079_ == 0)
{
lean_dec(v___x_2078_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_2080_; lean_object* v_P_2081_; 
v___x_2080_ = lean_unsigned_to_nat(4u);
v_P_2081_ = l_Lean_Syntax_getArg(v___x_483_, v___x_2080_);
lean_dec(v___x_483_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2089_; uint8_t v___x_2090_; 
v___x_2089_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_1000_);
v___x_2090_ = l_Lean_Syntax_isOfKind(v_x_1000_, v___x_2089_);
if (v___x_2090_ == 0)
{
lean_object* v___x_2091_; uint8_t v___x_2092_; 
v___x_2091_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58));
lean_inc(v_x_1000_);
v___x_2092_ = l_Lean_Syntax_isOfKind(v_x_1000_, v___x_2091_);
if (v___x_2092_ == 0)
{
lean_dec(v_P_2081_);
lean_dec(v___x_2078_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_2093_; lean_object* v___x_2094_; uint8_t v___x_2095_; 
v___x_2093_ = lean_unsigned_to_nat(3u);
v___x_2094_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_482_);
lean_inc(v___x_2094_);
v___x_2095_ = l_Lean_Syntax_matchesNull(v___x_2094_, v___x_482_);
if (v___x_2095_ == 0)
{
lean_object* v___x_2096_; uint8_t v___x_2097_; 
v___x_2096_ = l_Lean_Syntax_getNumArgs(v___x_2094_);
v___x_2097_ = lean_nat_dec_le(v___x_482_, v___x_2096_);
if (v___x_2097_ == 0)
{
lean_dec(v___x_2096_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
lean_dec(v___x_2078_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v_x_2098_; 
v_x_2098_ = l_Lean_Syntax_getArg(v___x_2094_, v___x_481_);
if (v___x_2095_ == 0)
{
uint8_t v___x_2115_; 
lean_inc(v_x_2098_);
v___x_2115_ = l_Lean_Syntax_isOfKind(v_x_2098_, v___x_2089_);
if (v___x_2115_ == 0)
{
lean_dec(v_x_2098_);
lean_dec(v___x_2096_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
lean_dec(v___x_2078_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
goto v___jp_2099_;
}
}
else
{
goto v___jp_2099_;
}
v___jp_2099_:
{
lean_object* v___x_2100_; uint8_t v___x_2101_; 
v___x_2100_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1939_);
lean_inc(v___x_2100_);
v___x_2101_ = l_Lean_Syntax_matchesNull(v___x_2100_, v___x_1939_);
if (v___x_2101_ == 0)
{
lean_dec(v___x_2100_);
lean_dec(v_x_2098_);
lean_dec(v___x_2096_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
lean_dec(v___x_2078_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_2102_; uint8_t v___x_2103_; 
v___x_2102_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_2093_);
lean_dec(v_x_1000_);
v___x_2103_ = l_Lean_Syntax_matchesNull(v___x_2102_, v___x_481_);
if (v___x_2103_ == 0)
{
lean_dec(v___x_2100_);
lean_dec(v_x_2098_);
lean_dec(v___x_2096_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
lean_dec(v___x_2078_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1941_ == 0)
{
lean_dec(v___x_2100_);
lean_dec(v_x_2098_);
lean_dec(v___x_2096_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
lean_dec(v___x_2078_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v_ty_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v_ys_2113_; lean_object* v_xs_2114_; 
v___x_2104_ = l_Lean_Syntax_getArgs(v___x_2094_);
lean_dec(v___x_2094_);
v___x_2105_ = l_Array_extract___redArg(v___x_2104_, v___x_482_, v___x_2096_);
lean_dec_ref(v___x_2104_);
v_ty_2106_ = l_Lean_Syntax_getArg(v___x_2100_, v___x_482_);
lean_dec(v___x_2100_);
v___x_2107_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2108_ = lean_box(2);
v___x_2109_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2108_);
lean_ctor_set(v___x_2109_, 1, v___x_2107_);
lean_ctor_set(v___x_2109_, 2, v___x_2105_);
v___x_2110_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_2111_ = l_Array_extract___redArg(v___x_2110_, v___x_482_, v___x_2078_);
lean_dec_ref(v___x_2110_);
v___x_2112_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2108_);
lean_ctor_set(v___x_2112_, 1, v___x_2107_);
lean_ctor_set(v___x_2112_, 2, v___x_2111_);
v_ys_2113_ = l_Lean_Syntax_getArgs(v___x_2112_);
lean_dec_ref_known(v___x_2112_, 3);
v_xs_2114_ = l_Lean_Syntax_getArgs(v___x_2109_);
lean_dec_ref_known(v___x_2109_, 3);
v_x_616_ = v_x_2098_;
v_xs_617_ = v_xs_2114_;
v_ty_618_ = v_ty_2106_;
v_ys_619_ = v_ys_2113_;
v_P_620_ = v_P_2081_;
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
lean_object* v_x_2116_; lean_object* v___y_2118_; lean_object* v___y_2119_; lean_object* v___y_2120_; lean_object* v___y_2121_; lean_object* v___y_2122_; uint8_t v___y_2123_; lean_object* v___y_2124_; lean_object* v___y_2133_; lean_object* v___y_2134_; lean_object* v___y_2135_; uint8_t v___y_2136_; lean_object* v___y_2137_; lean_object* v___y_2138_; uint8_t v___y_2139_; uint8_t v___y_2147_; lean_object* v___y_2148_; lean_object* v___y_2149_; lean_object* v___y_2150_; lean_object* v___y_2151_; lean_object* v___y_2152_; uint8_t v___y_2153_; 
v_x_2116_ = l_Lean_Syntax_getArg(v___x_2094_, v___x_481_);
if (v___x_2077_ == 0)
{
uint8_t v___x_2191_; 
lean_inc(v_x_2116_);
v___x_2191_ = l_Lean_Syntax_isOfKind(v_x_2116_, v___x_2089_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; uint8_t v___x_2193_; 
v___x_2192_ = l_Lean_Syntax_getNumArgs(v___x_2094_);
v___x_2193_ = lean_nat_dec_le(v___x_482_, v___x_2192_);
if (v___x_2193_ == 0)
{
lean_dec(v___x_2192_);
lean_dec(v_x_2116_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
lean_dec(v___x_2078_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2194_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1939_);
v___x_2195_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_2093_);
lean_dec(v_x_1000_);
v___x_2196_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_2197_ = l_Array_extract___redArg(v___x_2196_, v___x_482_, v___x_2078_);
lean_dec_ref(v___x_2196_);
v___x_2198_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2199_ = lean_box(2);
v___x_2200_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2200_, 0, v___x_2199_);
lean_ctor_set(v___x_2200_, 1, v___x_2198_);
lean_ctor_set(v___x_2200_, 2, v___x_2197_);
if (v___x_2077_ == 0)
{
if (v___x_2191_ == 0)
{
lean_dec_ref_known(v___x_2200_, 3);
lean_dec(v___x_2195_);
lean_dec(v___x_2194_);
lean_dec(v___x_2192_);
lean_dec(v_x_2116_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
goto v___jp_2201_;
}
}
else
{
goto v___jp_2201_;
}
v___jp_2201_:
{
uint8_t v___x_2202_; 
lean_inc(v___x_2194_);
v___x_2202_ = l_Lean_Syntax_matchesNull(v___x_2194_, v___x_1939_);
if (v___x_2202_ == 0)
{
lean_dec_ref_known(v___x_2200_, 3);
lean_dec(v___x_2195_);
lean_dec(v___x_2194_);
lean_dec(v___x_2192_);
lean_dec(v_x_2116_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
uint8_t v___x_2203_; 
v___x_2203_ = l_Lean_Syntax_matchesNull(v___x_2195_, v___x_481_);
if (v___x_2203_ == 0)
{
lean_dec_ref_known(v___x_2200_, 3);
lean_dec(v___x_2194_);
lean_dec(v___x_2192_);
lean_dec(v_x_2116_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1941_ == 0)
{
lean_dec_ref_known(v___x_2200_, 3);
lean_dec(v___x_2194_);
lean_dec(v___x_2192_);
lean_dec(v_x_2116_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v_ty_2207_; lean_object* v_ys_2208_; lean_object* v_xs_2209_; 
v___x_2204_ = l_Lean_Syntax_getArgs(v___x_2094_);
lean_dec(v___x_2094_);
v___x_2205_ = l_Array_extract___redArg(v___x_2204_, v___x_482_, v___x_2192_);
lean_dec_ref(v___x_2204_);
v___x_2206_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2199_);
lean_ctor_set(v___x_2206_, 1, v___x_2198_);
lean_ctor_set(v___x_2206_, 2, v___x_2205_);
v_ty_2207_ = l_Lean_Syntax_getArg(v___x_2194_, v___x_482_);
lean_dec(v___x_2194_);
v_ys_2208_ = l_Lean_Syntax_getArgs(v___x_2200_);
lean_dec_ref_known(v___x_2200_, 3);
v_xs_2209_ = l_Lean_Syntax_getArgs(v___x_2206_);
lean_dec_ref_known(v___x_2206_, 3);
v_x_616_ = v_x_2116_;
v_xs_617_ = v_xs_2209_;
v_ty_618_ = v_ty_2207_;
v_ys_619_ = v_ys_2208_;
v_P_620_ = v_P_2081_;
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
goto v___jp_2159_;
}
}
else
{
goto v___jp_2159_;
}
v___jp_2117_:
{
if (v___y_2123_ == 0)
{
lean_dec(v___y_2124_);
lean_dec(v___y_2122_);
lean_dec(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec(v_x_2116_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
uint8_t v___x_2125_; 
v___x_2125_ = l_Lean_Syntax_matchesNull(v___y_2124_, v___x_481_);
if (v___x_2125_ == 0)
{
lean_dec(v___y_2122_);
lean_dec(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec(v_x_2116_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1941_ == 0)
{
lean_dec(v___y_2122_);
lean_dec(v___y_2120_);
lean_dec(v___y_2119_);
lean_dec(v_x_2116_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v_ty_2129_; lean_object* v_ys_2130_; lean_object* v_xs_2131_; 
v___x_2126_ = l_Lean_Syntax_getArgs(v___x_2094_);
lean_dec(v___x_2094_);
v___x_2127_ = l_Array_extract___redArg(v___x_2126_, v___x_482_, v___y_2119_);
lean_dec_ref(v___x_2126_);
lean_inc(v___y_2118_);
lean_inc(v___y_2121_);
v___x_2128_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2128_, 0, v___y_2121_);
lean_ctor_set(v___x_2128_, 1, v___y_2118_);
lean_ctor_set(v___x_2128_, 2, v___x_2127_);
v_ty_2129_ = l_Lean_Syntax_getArg(v___y_2120_, v___x_482_);
lean_dec(v___y_2120_);
v_ys_2130_ = l_Lean_Syntax_getArgs(v___y_2122_);
lean_dec(v___y_2122_);
v_xs_2131_ = l_Lean_Syntax_getArgs(v___x_2128_);
lean_dec_ref_known(v___x_2128_, 3);
v_x_616_ = v_x_2116_;
v_xs_617_ = v_xs_2131_;
v_ty_618_ = v_ty_2129_;
v_ys_619_ = v_ys_2130_;
v_P_620_ = v_P_2081_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
v___jp_2132_:
{
if (v___y_2139_ == 0)
{
lean_dec(v___y_2137_);
lean_dec(v___y_2135_);
lean_dec(v___y_2133_);
lean_dec(v_x_2116_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___y_2136_ == 0)
{
lean_dec(v___y_2137_);
lean_dec(v___y_2135_);
lean_dec(v___y_2133_);
lean_dec(v_x_2116_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1941_ == 0)
{
lean_dec(v___y_2137_);
lean_dec(v___y_2135_);
lean_dec(v___y_2133_);
lean_dec(v_x_2116_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v_ty_2143_; lean_object* v_ys_2144_; lean_object* v_xs_2145_; 
v___x_2140_ = l_Lean_Syntax_getArgs(v___x_2094_);
lean_dec(v___x_2094_);
v___x_2141_ = l_Array_extract___redArg(v___x_2140_, v___x_482_, v___y_2137_);
lean_dec_ref(v___x_2140_);
lean_inc(v___y_2134_);
lean_inc(v___y_2138_);
v___x_2142_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2142_, 0, v___y_2138_);
lean_ctor_set(v___x_2142_, 1, v___y_2134_);
lean_ctor_set(v___x_2142_, 2, v___x_2141_);
v_ty_2143_ = l_Lean_Syntax_getArg(v___y_2135_, v___x_482_);
lean_dec(v___y_2135_);
v_ys_2144_ = l_Lean_Syntax_getArgs(v___y_2133_);
lean_dec(v___y_2133_);
v_xs_2145_ = l_Lean_Syntax_getArgs(v___x_2142_);
lean_dec_ref_known(v___x_2142_, 3);
v_x_616_ = v_x_2116_;
v_xs_617_ = v_xs_2145_;
v_ty_618_ = v_ty_2143_;
v_ys_619_ = v_ys_2144_;
v_P_620_ = v_P_2081_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
v___jp_2146_:
{
if (v___y_2153_ == 0)
{
lean_dec(v___y_2151_);
lean_dec(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec(v_x_2116_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___y_2147_ == 0)
{
lean_dec(v___y_2151_);
lean_dec(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec(v_x_2116_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1941_ == 0)
{
lean_dec(v___y_2151_);
lean_dec(v___y_2149_);
lean_dec(v___y_2148_);
lean_dec(v_x_2116_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v_ys_2157_; lean_object* v_xs_2158_; 
v___x_2154_ = l_Lean_Syntax_getArgs(v___x_2094_);
lean_dec(v___x_2094_);
v___x_2155_ = l_Array_extract___redArg(v___x_2154_, v___x_482_, v___y_2148_);
lean_dec_ref(v___x_2154_);
lean_inc(v___y_2150_);
lean_inc(v___y_2152_);
v___x_2156_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2156_, 0, v___y_2152_);
lean_ctor_set(v___x_2156_, 1, v___y_2150_);
lean_ctor_set(v___x_2156_, 2, v___x_2155_);
v_ys_2157_ = l_Lean_Syntax_getArgs(v___y_2149_);
lean_dec(v___y_2149_);
v_xs_2158_ = l_Lean_Syntax_getArgs(v___x_2156_);
lean_dec_ref_known(v___x_2156_, 3);
v_x_616_ = v_x_2116_;
v_xs_617_ = v_xs_2158_;
v_ty_618_ = v___y_2151_;
v_ys_619_ = v_ys_2157_;
v_P_620_ = v_P_2081_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
v___jp_2159_:
{
lean_object* v___x_2160_; uint8_t v___x_2161_; 
v___x_2160_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1939_);
lean_inc(v___x_2160_);
v___x_2161_ = l_Lean_Syntax_matchesNull(v___x_2160_, v___x_1939_);
if (v___x_2161_ == 0)
{
lean_object* v___x_2162_; uint8_t v___x_2163_; 
v___x_2162_ = l_Lean_Syntax_getNumArgs(v___x_2094_);
v___x_2163_ = lean_nat_dec_le(v___x_482_, v___x_2162_);
if (v___x_2163_ == 0)
{
lean_dec(v___x_2162_);
lean_dec(v___x_2160_);
lean_dec(v_x_2116_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
lean_dec(v___x_2078_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2164_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_2093_);
lean_dec(v_x_1000_);
v___x_2165_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_2166_ = l_Array_extract___redArg(v___x_2165_, v___x_482_, v___x_2078_);
lean_dec_ref(v___x_2165_);
v___x_2167_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2168_ = lean_box(2);
v___x_2169_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
lean_ctor_set(v___x_2169_, 1, v___x_2167_);
lean_ctor_set(v___x_2169_, 2, v___x_2166_);
if (v___x_2161_ == 0)
{
uint8_t v___x_2170_; 
lean_inc(v_x_2116_);
v___x_2170_ = l_Lean_Syntax_isOfKind(v_x_2116_, v___x_2089_);
if (v___x_2170_ == 0)
{
lean_dec_ref_known(v___x_2169_, 3);
lean_dec(v___x_2164_);
lean_dec(v___x_2162_);
lean_dec(v___x_2160_);
lean_dec(v_x_2116_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
v___y_2118_ = v___x_2167_;
v___y_2119_ = v___x_2162_;
v___y_2120_ = v___x_2160_;
v___y_2121_ = v___x_2168_;
v___y_2122_ = v___x_2169_;
v___y_2123_ = v___x_2161_;
v___y_2124_ = v___x_2164_;
goto v___jp_2117_;
}
}
else
{
v___y_2118_ = v___x_2167_;
v___y_2119_ = v___x_2162_;
v___y_2120_ = v___x_2160_;
v___y_2121_ = v___x_2168_;
v___y_2122_ = v___x_2169_;
v___y_2123_ = v___x_2161_;
v___y_2124_ = v___x_2164_;
goto v___jp_2117_;
}
}
}
else
{
lean_object* v___x_2171_; uint8_t v___x_2172_; 
v___x_2171_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_2093_);
lean_dec(v_x_1000_);
v___x_2172_ = l_Lean_Syntax_matchesNull(v___x_2171_, v___x_481_);
if (v___x_2172_ == 0)
{
lean_object* v___x_2173_; uint8_t v___x_2174_; 
v___x_2173_ = l_Lean_Syntax_getNumArgs(v___x_2094_);
v___x_2174_ = lean_nat_dec_le(v___x_482_, v___x_2173_);
if (v___x_2174_ == 0)
{
lean_dec(v___x_2173_);
lean_dec(v___x_2160_);
lean_dec(v_x_2116_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
lean_dec(v___x_2078_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_2175_; lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; 
v___x_2175_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_2176_ = l_Array_extract___redArg(v___x_2175_, v___x_482_, v___x_2078_);
lean_dec_ref(v___x_2175_);
v___x_2177_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2178_ = lean_box(2);
v___x_2179_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2179_, 0, v___x_2178_);
lean_ctor_set(v___x_2179_, 1, v___x_2177_);
lean_ctor_set(v___x_2179_, 2, v___x_2176_);
if (v___x_2172_ == 0)
{
uint8_t v___x_2180_; 
lean_inc(v_x_2116_);
v___x_2180_ = l_Lean_Syntax_isOfKind(v_x_2116_, v___x_2089_);
if (v___x_2180_ == 0)
{
lean_dec_ref_known(v___x_2179_, 3);
lean_dec(v___x_2173_);
lean_dec(v___x_2160_);
lean_dec(v_x_2116_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
v___y_2133_ = v___x_2179_;
v___y_2134_ = v___x_2177_;
v___y_2135_ = v___x_2160_;
v___y_2136_ = v___x_2172_;
v___y_2137_ = v___x_2173_;
v___y_2138_ = v___x_2178_;
v___y_2139_ = v___x_2161_;
goto v___jp_2132_;
}
}
else
{
v___y_2133_ = v___x_2179_;
v___y_2134_ = v___x_2177_;
v___y_2135_ = v___x_2160_;
v___y_2136_ = v___x_2172_;
v___y_2137_ = v___x_2173_;
v___y_2138_ = v___x_2178_;
v___y_2139_ = v___x_2161_;
goto v___jp_2132_;
}
}
}
else
{
lean_object* v_ty_2181_; lean_object* v___x_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; lean_object* v___x_2186_; 
v_ty_2181_ = l_Lean_Syntax_getArg(v___x_2160_, v___x_482_);
lean_dec(v___x_2160_);
v___x_2182_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_2183_ = l_Array_extract___redArg(v___x_2182_, v___x_482_, v___x_2078_);
lean_dec_ref(v___x_2182_);
v___x_2184_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2185_ = lean_box(2);
v___x_2186_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
lean_ctor_set(v___x_2186_, 1, v___x_2184_);
lean_ctor_set(v___x_2186_, 2, v___x_2183_);
if (v___x_1941_ == 0)
{
lean_object* v___x_2187_; uint8_t v___x_2188_; 
v___x_2187_ = l_Lean_Syntax_getNumArgs(v___x_2094_);
v___x_2188_ = lean_nat_dec_le(v___x_482_, v___x_2187_);
if (v___x_2188_ == 0)
{
lean_dec(v___x_2187_);
lean_dec_ref_known(v___x_2186_, 3);
lean_dec(v_ty_2181_);
lean_dec(v_x_2116_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___x_1941_ == 0)
{
uint8_t v___x_2189_; 
lean_inc(v_x_2116_);
v___x_2189_ = l_Lean_Syntax_isOfKind(v_x_2116_, v___x_2089_);
if (v___x_2189_ == 0)
{
lean_dec(v___x_2187_);
lean_dec_ref_known(v___x_2186_, 3);
lean_dec(v_ty_2181_);
lean_dec(v_x_2116_);
lean_dec(v___x_2094_);
lean_dec(v_P_2081_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
v___y_2147_ = v___x_2172_;
v___y_2148_ = v___x_2187_;
v___y_2149_ = v___x_2186_;
v___y_2150_ = v___x_2184_;
v___y_2151_ = v_ty_2181_;
v___y_2152_ = v___x_2185_;
v___y_2153_ = v___x_2161_;
goto v___jp_2146_;
}
}
else
{
v___y_2147_ = v___x_2172_;
v___y_2148_ = v___x_2187_;
v___y_2149_ = v___x_2186_;
v___y_2150_ = v___x_2184_;
v___y_2151_ = v_ty_2181_;
v___y_2152_ = v___x_2185_;
v___y_2153_ = v___x_2161_;
goto v___jp_2146_;
}
}
}
else
{
lean_object* v_xs_2190_; 
lean_dec(v___x_2094_);
v_xs_2190_ = l_Lean_Syntax_getArgs(v___x_2186_);
lean_dec_ref_known(v___x_2186_, 3);
v_x_554_ = v_x_2116_;
v_ty_555_ = v_ty_2181_;
v_xs_556_ = v_xs_2190_;
v_P_557_ = v_P_2081_;
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
goto v___jp_2082_;
}
}
else
{
goto v___jp_2082_;
}
v___jp_2082_:
{
if (v___x_1941_ == 0)
{
lean_dec(v_P_2081_);
lean_dec(v___x_2078_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v_xs_2088_; 
v___x_2083_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_2084_ = l_Array_extract___redArg(v___x_2083_, v___x_482_, v___x_2078_);
lean_dec_ref(v___x_2083_);
v___x_2085_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2086_ = lean_box(2);
v___x_2087_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2087_, 0, v___x_2086_);
lean_ctor_set(v___x_2087_, 1, v___x_2085_);
lean_ctor_set(v___x_2087_, 2, v___x_2084_);
v_xs_2088_ = l_Lean_Syntax_getArgs(v___x_2087_);
lean_dec_ref_known(v___x_2087_, 3);
v_x_498_ = v_x_1000_;
v_xs_499_ = v_xs_2088_;
v_P_500_ = v_P_2081_;
v___y_501_ = v_a_471_;
v___y_502_ = v_a_472_;
goto v___jp_497_;
}
}
}
}
else
{
lean_object* v_quotContext_2210_; lean_object* v_currMacroScope_2211_; lean_object* v_ref_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; 
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v_quotContext_2210_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_2211_ = lean_ctor_get(v_a_471_, 2);
v_ref_2212_ = lean_ctor_get(v_a_471_, 5);
v___x_2213_ = l_Lean_Syntax_getArg(v___x_2075_, v___x_482_);
lean_dec(v___x_2075_);
v___x_2214_ = lean_unsigned_to_nat(4u);
v___x_2215_ = l_Lean_Syntax_getArg(v___x_483_, v___x_2214_);
lean_dec(v___x_483_);
v___x_2216_ = l_Lean_SourceInfo_fromRef(v_ref_2212_, v___x_1941_);
v___x_2217_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2218_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_2219_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc_n(v_currMacroScope_2211_, 2);
lean_inc_n(v_quotContext_2210_, 2);
v___x_2220_ = l_Lean_addMacroScope(v_quotContext_2210_, v___x_2219_, v_currMacroScope_2211_);
v___x_2221_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc_n(v___x_2216_, 19);
v___x_2222_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2216_);
lean_ctor_set(v___x_2222_, 1, v___x_2218_);
lean_ctor_set(v___x_2222_, 2, v___x_2220_);
lean_ctor_set(v___x_2222_, 3, v___x_2221_);
v___x_2223_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2224_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_2225_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_2226_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
v___x_2227_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2227_, 0, v___x_2216_);
lean_ctor_set(v___x_2227_, 1, v___x_2226_);
v___x_2228_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_2229_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_2230_ = lean_box(0);
v___x_2231_ = l_Lean_addMacroScope(v_quotContext_2210_, v___x_2230_, v_currMacroScope_2211_);
v___x_2232_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
v___x_2233_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2216_);
lean_ctor_set(v___x_2233_, 1, v___x_2229_);
lean_ctor_set(v___x_2233_, 2, v___x_2231_);
lean_ctor_set(v___x_2233_, 3, v___x_2232_);
v___x_2234_ = l_Lean_Syntax_node1(v___x_2216_, v___x_2228_, v___x_2233_);
v___x_2235_ = l_Lean_Syntax_node2(v___x_2216_, v___x_2225_, v___x_2227_, v___x_2234_);
v___x_2236_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_2237_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
v___x_2238_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2216_);
lean_ctor_set(v___x_2238_, 1, v___x_2236_);
v___x_2239_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_2240_ = l_Lean_SourceInfo_fromRef(v_tk_1938_, v___x_830_);
lean_dec(v_tk_1938_);
v___x_2241_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__63));
v___x_2242_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2242_, 0, v___x_2240_);
lean_ctor_set(v___x_2242_, 1, v___x_2241_);
v___x_2243_ = l_Lean_Syntax_node1(v___x_2216_, v___x_1156_, v___x_2242_);
v___x_2244_ = l_Lean_Syntax_node1(v___x_2216_, v___x_2223_, v___x_2243_);
v___x_2245_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
v___x_2246_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2246_, 0, v___x_2216_);
lean_ctor_set(v___x_2246_, 1, v___x_2245_);
v___x_2247_ = l_Lean_Syntax_node2(v___x_2216_, v___x_2076_, v___x_2246_, v___x_2213_);
v___x_2248_ = l_Lean_Syntax_node1(v___x_2216_, v___x_2223_, v___x_2247_);
v___x_2249_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_2250_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2216_);
lean_ctor_set(v___x_2250_, 1, v___x_2249_);
v___x_2251_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_2252_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2216_);
lean_ctor_set(v___x_2252_, 1, v___x_2251_);
v___x_2253_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2254_, 0, v___x_2216_);
lean_ctor_set(v___x_2254_, 1, v___x_2253_);
lean_inc_ref(v___x_2254_);
v___x_2255_ = l_Lean_Syntax_node3(v___x_2216_, v___x_477_, v___x_2252_, v___x_2215_, v___x_2254_);
v___x_2256_ = l_Lean_Syntax_node4(v___x_2216_, v___x_2239_, v___x_2244_, v___x_2248_, v___x_2250_, v___x_2255_);
v___x_2257_ = l_Lean_Syntax_node2(v___x_2216_, v___x_2237_, v___x_2238_, v___x_2256_);
v___x_2258_ = l_Lean_Syntax_node3(v___x_2216_, v___x_2224_, v___x_2235_, v___x_2257_, v___x_2254_);
v___x_2259_ = l_Lean_Syntax_node1(v___x_2216_, v___x_2223_, v___x_2258_);
v___x_2260_ = l_Lean_Syntax_node2(v___x_2216_, v___x_2217_, v___x_2222_, v___x_2259_);
v___x_2261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2261_, 0, v___x_2260_);
lean_ctor_set(v___x_2261_, 1, v_a_472_);
return v___x_2261_;
}
}
}
else
{
lean_object* v_quotContext_2262_; lean_object* v_currMacroScope_2263_; lean_object* v_ref_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
lean_dec(v___x_1940_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v_quotContext_2262_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_2263_ = lean_ctor_get(v_a_471_, 2);
v_ref_2264_ = lean_ctor_get(v_a_471_, 5);
v___x_2265_ = lean_unsigned_to_nat(4u);
v___x_2266_ = l_Lean_Syntax_getArg(v___x_483_, v___x_2265_);
lean_dec(v___x_483_);
v___x_2267_ = l_Lean_SourceInfo_fromRef(v_ref_2264_, v___x_495_);
v___x_2268_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2269_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_2270_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc_n(v_currMacroScope_2263_, 2);
lean_inc_n(v_quotContext_2262_, 2);
v___x_2271_ = l_Lean_addMacroScope(v_quotContext_2262_, v___x_2270_, v_currMacroScope_2263_);
v___x_2272_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc_n(v___x_2267_, 17);
v___x_2273_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2273_, 0, v___x_2267_);
lean_ctor_set(v___x_2273_, 1, v___x_2269_);
lean_ctor_set(v___x_2273_, 2, v___x_2271_);
lean_ctor_set(v___x_2273_, 3, v___x_2272_);
v___x_2274_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2275_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_2276_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_2277_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
v___x_2278_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2278_, 0, v___x_2267_);
lean_ctor_set(v___x_2278_, 1, v___x_2277_);
v___x_2279_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_2280_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_2281_ = lean_box(0);
v___x_2282_ = l_Lean_addMacroScope(v_quotContext_2262_, v___x_2281_, v_currMacroScope_2263_);
v___x_2283_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
v___x_2284_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2267_);
lean_ctor_set(v___x_2284_, 1, v___x_2280_);
lean_ctor_set(v___x_2284_, 2, v___x_2282_);
lean_ctor_set(v___x_2284_, 3, v___x_2283_);
v___x_2285_ = l_Lean_Syntax_node1(v___x_2267_, v___x_2279_, v___x_2284_);
v___x_2286_ = l_Lean_Syntax_node2(v___x_2267_, v___x_2276_, v___x_2278_, v___x_2285_);
v___x_2287_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_2288_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
v___x_2289_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2289_, 0, v___x_2267_);
lean_ctor_set(v___x_2289_, 1, v___x_2287_);
v___x_2290_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_2291_ = l_Lean_SourceInfo_fromRef(v_tk_1938_, v___x_830_);
lean_dec(v_tk_1938_);
v___x_2292_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__63));
v___x_2293_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2291_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = l_Lean_Syntax_node1(v___x_2267_, v___x_1156_, v___x_2293_);
v___x_2295_ = l_Lean_Syntax_node1(v___x_2267_, v___x_2274_, v___x_2294_);
v___x_2296_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2297_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2297_, 0, v___x_2267_);
lean_ctor_set(v___x_2297_, 1, v___x_2274_);
lean_ctor_set(v___x_2297_, 2, v___x_2296_);
v___x_2298_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_2299_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2299_, 0, v___x_2267_);
lean_ctor_set(v___x_2299_, 1, v___x_2298_);
v___x_2300_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_2301_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2301_, 0, v___x_2267_);
lean_ctor_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2303_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2303_, 0, v___x_2267_);
lean_ctor_set(v___x_2303_, 1, v___x_2302_);
lean_inc_ref(v___x_2303_);
v___x_2304_ = l_Lean_Syntax_node3(v___x_2267_, v___x_477_, v___x_2301_, v___x_2266_, v___x_2303_);
v___x_2305_ = l_Lean_Syntax_node4(v___x_2267_, v___x_2290_, v___x_2295_, v___x_2297_, v___x_2299_, v___x_2304_);
v___x_2306_ = l_Lean_Syntax_node2(v___x_2267_, v___x_2288_, v___x_2289_, v___x_2305_);
v___x_2307_ = l_Lean_Syntax_node3(v___x_2267_, v___x_2275_, v___x_2286_, v___x_2306_, v___x_2303_);
v___x_2308_ = l_Lean_Syntax_node1(v___x_2267_, v___x_2274_, v___x_2307_);
v___x_2309_ = l_Lean_Syntax_node2(v___x_2267_, v___x_2268_, v___x_2273_, v___x_2308_);
v___x_2310_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2310_, 0, v___x_2309_);
lean_ctor_set(v___x_2310_, 1, v_a_472_);
return v___x_2310_;
}
}
v___jp_1001_:
{
uint8_t v___x_1007_; 
v___x_1007_ = l_Lean_Syntax_matchesNull(v___y_1002_, v___x_481_);
if (v___x_1007_ == 0)
{
lean_dec(v___y_1006_);
lean_dec(v___y_1004_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v___y_1005_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v_xs_1013_; 
v___x_1008_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_1009_ = l_Array_extract___redArg(v___x_1008_, v___x_482_, v___y_1004_);
lean_dec_ref(v___x_1008_);
v___x_1010_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1011_ = lean_box(2);
v___x_1012_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v___x_1010_);
lean_ctor_set(v___x_1012_, 2, v___x_1009_);
v_xs_1013_ = l_Lean_Syntax_getArgs(v___x_1012_);
lean_dec_ref_known(v___x_1012_, 3);
v_x_498_ = v_x_1000_;
v_xs_499_ = v_xs_1013_;
v_P_500_ = v___y_1006_;
v___y_501_ = v___y_1003_;
v___y_502_ = v___y_1005_;
goto v___jp_497_;
}
}
v___jp_1014_:
{
lean_object* v___x_1023_; lean_object* v___x_1024_; uint8_t v___x_1025_; 
v___x_1023_ = lean_unsigned_to_nat(2u);
v___x_1024_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1023_);
lean_inc(v___x_1024_);
v___x_1025_ = l_Lean_Syntax_matchesNull(v___x_1024_, v___x_1023_);
if (v___x_1025_ == 0)
{
lean_dec(v___x_1024_);
lean_dec(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v___y_1020_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1026_; lean_object* v___x_1027_; uint8_t v___x_1028_; 
v___x_1026_ = lean_unsigned_to_nat(3u);
v___x_1027_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1026_);
lean_dec(v_x_1000_);
v___x_1028_ = l_Lean_Syntax_matchesNull(v___x_1027_, v___x_481_);
if (v___x_1028_ == 0)
{
lean_dec(v___x_1024_);
lean_dec(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec(v___y_1016_);
lean_dec(v___y_1015_);
lean_dec(v___x_829_);
v___y_474_ = v___y_1020_;
goto v___jp_473_;
}
else
{
uint8_t v___x_1029_; 
v___x_1029_ = l_Lean_Syntax_matchesNull(v___y_1016_, v___x_481_);
if (v___x_1029_ == 0)
{
lean_dec(v___x_1024_);
lean_dec(v___y_1022_);
lean_dec(v___y_1021_);
lean_dec(v___y_1019_);
lean_dec(v___y_1018_);
lean_dec(v___y_1015_);
lean_dec(v___x_829_);
v___y_474_ = v___y_1020_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v_ty_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v_ys_1039_; lean_object* v_xs_1040_; 
v___x_1030_ = l_Lean_Syntax_getArgs(v___y_1019_);
lean_dec(v___y_1019_);
v___x_1031_ = l_Array_extract___redArg(v___x_1030_, v___x_482_, v___y_1022_);
lean_dec_ref(v___x_1030_);
v_ty_1032_ = l_Lean_Syntax_getArg(v___x_1024_, v___x_482_);
lean_dec(v___x_1024_);
v___x_1033_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1034_ = lean_box(2);
v___x_1035_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
lean_ctor_set(v___x_1035_, 1, v___x_1033_);
lean_ctor_set(v___x_1035_, 2, v___x_1031_);
v___x_1036_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_1037_ = l_Array_extract___redArg(v___x_1036_, v___x_482_, v___y_1018_);
lean_dec_ref(v___x_1036_);
v___x_1038_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1038_, 0, v___x_1034_);
lean_ctor_set(v___x_1038_, 1, v___x_1033_);
lean_ctor_set(v___x_1038_, 2, v___x_1037_);
v_ys_1039_ = l_Lean_Syntax_getArgs(v___x_1038_);
lean_dec_ref_known(v___x_1038_, 3);
v_xs_1040_ = l_Lean_Syntax_getArgs(v___x_1035_);
lean_dec_ref_known(v___x_1035_, 3);
v_x_616_ = v___y_1015_;
v_xs_617_ = v_xs_1040_;
v_ty_618_ = v_ty_1032_;
v_ys_619_ = v_ys_1039_;
v_P_620_ = v___y_1021_;
v___y_621_ = v___y_1017_;
v___y_622_ = v___y_1020_;
goto v___jp_615_;
}
}
}
}
v___jp_1041_:
{
lean_object* v___x_1050_; lean_object* v___x_1051_; uint8_t v___x_1052_; 
v___x_1050_ = lean_unsigned_to_nat(2u);
v___x_1051_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1050_);
lean_inc(v___x_1051_);
v___x_1052_ = l_Lean_Syntax_matchesNull(v___x_1051_, v___x_1050_);
if (v___x_1052_ == 0)
{
lean_object* v___x_1053_; uint8_t v___x_1054_; 
v___x_1053_ = l_Lean_Syntax_getNumArgs(v___y_1046_);
v___x_1054_ = lean_nat_dec_le(v___x_482_, v___x_1053_);
if (v___x_1054_ == 0)
{
lean_dec(v___x_1053_);
lean_dec(v___x_1051_);
lean_dec(v___y_1049_);
lean_dec(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec(v___y_1042_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v___y_1048_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; 
v___x_1055_ = lean_unsigned_to_nat(3u);
v___x_1056_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1055_);
lean_dec(v_x_1000_);
v___x_1057_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_1058_ = l_Array_extract___redArg(v___x_1057_, v___x_482_, v___y_1045_);
lean_dec_ref(v___x_1057_);
v___x_1059_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1060_ = lean_box(2);
v___x_1061_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1061_, 0, v___x_1060_);
lean_ctor_set(v___x_1061_, 1, v___x_1059_);
lean_ctor_set(v___x_1061_, 2, v___x_1058_);
if (v___x_1052_ == 0)
{
uint8_t v___x_1062_; 
lean_inc(v___y_1047_);
v___x_1062_ = l_Lean_Syntax_isOfKind(v___y_1047_, v___y_1044_);
if (v___x_1062_ == 0)
{
lean_dec_ref_known(v___x_1061_, 3);
lean_dec(v___x_1056_);
lean_dec(v___x_1053_);
lean_dec(v___x_1051_);
lean_dec(v___y_1049_);
lean_dec(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec(v___y_1042_);
v___y_474_ = v___y_1048_;
goto v___jp_473_;
}
else
{
v___y_685_ = v___x_1060_;
v___y_686_ = v___x_1053_;
v___y_687_ = v___y_1047_;
v___y_688_ = v___y_1049_;
v___y_689_ = v___x_1051_;
v___y_690_ = v___x_1056_;
v___y_691_ = v___y_1042_;
v___y_692_ = v___x_1052_;
v___y_693_ = v___x_1061_;
v___y_694_ = v___y_1043_;
v___y_695_ = v___y_1046_;
v___y_696_ = v___x_1059_;
v___y_697_ = v___y_1048_;
goto v___jp_684_;
}
}
else
{
v___y_685_ = v___x_1060_;
v___y_686_ = v___x_1053_;
v___y_687_ = v___y_1047_;
v___y_688_ = v___y_1049_;
v___y_689_ = v___x_1051_;
v___y_690_ = v___x_1056_;
v___y_691_ = v___y_1042_;
v___y_692_ = v___x_1052_;
v___y_693_ = v___x_1061_;
v___y_694_ = v___y_1043_;
v___y_695_ = v___y_1046_;
v___y_696_ = v___x_1059_;
v___y_697_ = v___y_1048_;
goto v___jp_684_;
}
}
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
v___x_1063_ = lean_unsigned_to_nat(3u);
v___x_1064_ = l_Lean_Syntax_getArg(v_x_1000_, v___x_1063_);
lean_dec(v_x_1000_);
v___x_1065_ = l_Lean_Syntax_matchesNull(v___x_1064_, v___x_481_);
if (v___x_1065_ == 0)
{
lean_object* v___x_1066_; uint8_t v___x_1067_; 
v___x_1066_ = l_Lean_Syntax_getNumArgs(v___y_1046_);
v___x_1067_ = lean_nat_dec_le(v___x_482_, v___x_1066_);
if (v___x_1067_ == 0)
{
lean_dec(v___x_1066_);
lean_dec(v___x_1051_);
lean_dec(v___y_1049_);
lean_dec(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec(v___y_1045_);
lean_dec(v___y_1042_);
lean_dec(v___x_829_);
v___y_474_ = v___y_1048_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; 
v___x_1068_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_1069_ = l_Array_extract___redArg(v___x_1068_, v___x_482_, v___y_1045_);
lean_dec_ref(v___x_1068_);
v___x_1070_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1071_ = lean_box(2);
v___x_1072_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1072_, 0, v___x_1071_);
lean_ctor_set(v___x_1072_, 1, v___x_1070_);
lean_ctor_set(v___x_1072_, 2, v___x_1069_);
if (v___x_1065_ == 0)
{
uint8_t v___x_1073_; 
lean_inc(v___y_1047_);
v___x_1073_ = l_Lean_Syntax_isOfKind(v___y_1047_, v___y_1044_);
if (v___x_1073_ == 0)
{
lean_dec_ref_known(v___x_1072_, 3);
lean_dec(v___x_1066_);
lean_dec(v___x_1051_);
lean_dec(v___y_1049_);
lean_dec(v___y_1047_);
lean_dec(v___y_1046_);
lean_dec(v___y_1042_);
v___y_474_ = v___y_1048_;
goto v___jp_473_;
}
else
{
v___y_707_ = v___x_1066_;
v___y_708_ = v___x_1070_;
v___y_709_ = v___y_1047_;
v___y_710_ = v___y_1049_;
v___y_711_ = v___x_1065_;
v___y_712_ = v___x_1071_;
v___y_713_ = v___x_1051_;
v___y_714_ = v___y_1042_;
v___y_715_ = v___x_1052_;
v___y_716_ = v___y_1043_;
v___y_717_ = v___x_1072_;
v___y_718_ = v___y_1046_;
v___y_719_ = v___y_1048_;
goto v___jp_706_;
}
}
else
{
v___y_707_ = v___x_1066_;
v___y_708_ = v___x_1070_;
v___y_709_ = v___y_1047_;
v___y_710_ = v___y_1049_;
v___y_711_ = v___x_1065_;
v___y_712_ = v___x_1071_;
v___y_713_ = v___x_1051_;
v___y_714_ = v___y_1042_;
v___y_715_ = v___x_1052_;
v___y_716_ = v___y_1043_;
v___y_717_ = v___x_1072_;
v___y_718_ = v___y_1046_;
v___y_719_ = v___y_1048_;
goto v___jp_706_;
}
}
}
else
{
lean_object* v_ty_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; uint8_t v___x_1080_; 
v_ty_1074_ = l_Lean_Syntax_getArg(v___x_1051_, v___x_482_);
lean_dec(v___x_1051_);
v___x_1075_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_1076_ = l_Array_extract___redArg(v___x_1075_, v___x_482_, v___y_1045_);
lean_dec_ref(v___x_1075_);
v___x_1077_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1078_ = lean_box(2);
v___x_1079_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
lean_ctor_set(v___x_1079_, 1, v___x_1077_);
lean_ctor_set(v___x_1079_, 2, v___x_1076_);
v___x_1080_ = l_Lean_Syntax_matchesNull(v___y_1042_, v___x_481_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; uint8_t v___x_1082_; 
v___x_1081_ = l_Lean_Syntax_getNumArgs(v___y_1046_);
v___x_1082_ = lean_nat_dec_le(v___x_482_, v___x_1081_);
if (v___x_1082_ == 0)
{
lean_dec(v___x_1081_);
lean_dec_ref_known(v___x_1079_, 3);
lean_dec(v_ty_1074_);
lean_dec(v___y_1049_);
lean_dec(v___y_1047_);
lean_dec(v___y_1046_);
v___y_474_ = v___y_1048_;
goto v___jp_473_;
}
else
{
if (v___x_1080_ == 0)
{
uint8_t v___x_1083_; 
lean_inc(v___y_1047_);
v___x_1083_ = l_Lean_Syntax_isOfKind(v___y_1047_, v___y_1044_);
if (v___x_1083_ == 0)
{
lean_dec(v___x_1081_);
lean_dec_ref_known(v___x_1079_, 3);
lean_dec(v_ty_1074_);
lean_dec(v___y_1049_);
lean_dec(v___y_1047_);
lean_dec(v___y_1046_);
v___y_474_ = v___y_1048_;
goto v___jp_473_;
}
else
{
v___y_728_ = v___x_1079_;
v___y_729_ = v___y_1047_;
v___y_730_ = v___x_1080_;
v___y_731_ = v___x_1081_;
v___y_732_ = v___y_1049_;
v___y_733_ = v___x_1065_;
v___y_734_ = v___x_1052_;
v___y_735_ = v___x_1078_;
v___y_736_ = v___y_1043_;
v___y_737_ = v___y_1046_;
v___y_738_ = v___y_1048_;
v___y_739_ = v_ty_1074_;
v___y_740_ = v___x_1077_;
goto v___jp_727_;
}
}
else
{
v___y_728_ = v___x_1079_;
v___y_729_ = v___y_1047_;
v___y_730_ = v___x_1080_;
v___y_731_ = v___x_1081_;
v___y_732_ = v___y_1049_;
v___y_733_ = v___x_1065_;
v___y_734_ = v___x_1052_;
v___y_735_ = v___x_1078_;
v___y_736_ = v___y_1043_;
v___y_737_ = v___y_1046_;
v___y_738_ = v___y_1048_;
v___y_739_ = v_ty_1074_;
v___y_740_ = v___x_1077_;
goto v___jp_727_;
}
}
}
else
{
lean_object* v_xs_1084_; 
lean_dec(v___y_1046_);
v_xs_1084_ = l_Lean_Syntax_getArgs(v___x_1079_);
lean_dec_ref_known(v___x_1079_, 3);
v_x_554_ = v___y_1047_;
v_ty_555_ = v_ty_1074_;
v_xs_556_ = v_xs_1084_;
v_P_557_ = v___y_1049_;
v___y_558_ = v___y_1043_;
v___y_559_ = v___y_1048_;
goto v___jp_553_;
}
}
}
}
v___jp_1085_:
{
if (v___y_1088_ == 0)
{
lean_dec(v___y_1087_);
lean_dec(v___y_1086_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v_xs_1094_; 
v___x_1089_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_1090_ = l_Array_extract___redArg(v___x_1089_, v___x_482_, v___y_1086_);
lean_dec_ref(v___x_1089_);
v___x_1091_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1092_ = lean_box(2);
v___x_1093_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1092_);
lean_ctor_set(v___x_1093_, 1, v___x_1091_);
lean_ctor_set(v___x_1093_, 2, v___x_1090_);
v_xs_1094_ = l_Lean_Syntax_getArgs(v___x_1093_);
lean_dec_ref_known(v___x_1093_, 3);
v_x_498_ = v_x_1000_;
v_xs_499_ = v_xs_1094_;
v_P_500_ = v___y_1087_;
v___y_501_ = v_a_471_;
v___y_502_ = v_a_472_;
goto v___jp_497_;
}
}
v___jp_1095_:
{
lean_object* v___x_1104_; uint8_t v___x_1105_; 
v___x_1104_ = l_Lean_Syntax_getArg(v_x_1000_, v___y_1103_);
lean_inc(v___x_1104_);
v___x_1105_ = l_Lean_Syntax_matchesNull(v___x_1104_, v___y_1103_);
if (v___x_1105_ == 0)
{
lean_dec(v___x_1104_);
lean_dec(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1106_; uint8_t v___x_1107_; 
v___x_1106_ = l_Lean_Syntax_getArg(v_x_1000_, v___y_1101_);
lean_dec(v_x_1000_);
v___x_1107_ = l_Lean_Syntax_matchesNull(v___x_1106_, v___x_481_);
if (v___x_1107_ == 0)
{
lean_dec(v___x_1104_);
lean_dec(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___y_1102_ == 0)
{
lean_dec(v___x_1104_);
lean_dec(v___y_1100_);
lean_dec(v___y_1099_);
lean_dec(v___y_1098_);
lean_dec(v___y_1097_);
lean_dec(v___y_1096_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v_ty_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v_ys_1117_; lean_object* v_xs_1118_; 
v___x_1108_ = l_Lean_Syntax_getArgs(v___y_1100_);
lean_dec(v___y_1100_);
v___x_1109_ = l_Array_extract___redArg(v___x_1108_, v___x_482_, v___y_1097_);
lean_dec_ref(v___x_1108_);
v_ty_1110_ = l_Lean_Syntax_getArg(v___x_1104_, v___x_482_);
lean_dec(v___x_1104_);
v___x_1111_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1112_ = lean_box(2);
v___x_1113_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1113_, 0, v___x_1112_);
lean_ctor_set(v___x_1113_, 1, v___x_1111_);
lean_ctor_set(v___x_1113_, 2, v___x_1109_);
v___x_1114_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_1115_ = l_Array_extract___redArg(v___x_1114_, v___x_482_, v___y_1096_);
lean_dec_ref(v___x_1114_);
v___x_1116_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1116_, 0, v___x_1112_);
lean_ctor_set(v___x_1116_, 1, v___x_1111_);
lean_ctor_set(v___x_1116_, 2, v___x_1115_);
v_ys_1117_ = l_Lean_Syntax_getArgs(v___x_1116_);
lean_dec_ref_known(v___x_1116_, 3);
v_xs_1118_ = l_Lean_Syntax_getArgs(v___x_1113_);
lean_dec_ref_known(v___x_1113_, 3);
v_x_616_ = v___y_1099_;
v_xs_617_ = v_xs_1118_;
v_ty_618_ = v_ty_1110_;
v_ys_619_ = v_ys_1117_;
v_P_620_ = v___y_1098_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
v___jp_1119_:
{
lean_object* v___x_1128_; uint8_t v___x_1129_; 
v___x_1128_ = l_Lean_Syntax_getArg(v_x_1000_, v___y_1127_);
lean_inc(v___x_1128_);
v___x_1129_ = l_Lean_Syntax_matchesNull(v___x_1128_, v___y_1127_);
if (v___x_1129_ == 0)
{
lean_object* v___x_1130_; uint8_t v___x_1131_; 
v___x_1130_ = l_Lean_Syntax_getNumArgs(v___y_1124_);
v___x_1131_ = lean_nat_dec_le(v___x_482_, v___x_1130_);
if (v___x_1131_ == 0)
{
lean_dec(v___x_1130_);
lean_dec(v___x_1128_);
lean_dec(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec(v_x_1000_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1132_ = l_Lean_Syntax_getArg(v_x_1000_, v___y_1125_);
lean_dec(v_x_1000_);
v___x_1133_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_1134_ = l_Array_extract___redArg(v___x_1133_, v___x_482_, v___y_1121_);
lean_dec_ref(v___x_1133_);
v___x_1135_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1136_ = lean_box(2);
v___x_1137_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1136_);
lean_ctor_set(v___x_1137_, 1, v___x_1135_);
lean_ctor_set(v___x_1137_, 2, v___x_1134_);
if (v___x_1129_ == 0)
{
uint8_t v___x_1138_; 
lean_inc(v___y_1122_);
v___x_1138_ = l_Lean_Syntax_isOfKind(v___y_1122_, v___y_1120_);
if (v___x_1138_ == 0)
{
lean_dec_ref_known(v___x_1137_, 3);
lean_dec(v___x_1132_);
lean_dec(v___x_1130_);
lean_dec(v___x_1128_);
lean_dec(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec(v___y_1122_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
v___y_770_ = v___x_1136_;
v___y_771_ = v___y_1123_;
v___y_772_ = v___y_1122_;
v___y_773_ = v___x_1129_;
v___y_774_ = v___y_1124_;
v___y_775_ = v___x_1132_;
v___y_776_ = v___x_1128_;
v___y_777_ = v___x_1135_;
v___y_778_ = v___x_1130_;
v___y_779_ = v___x_1137_;
v___y_780_ = v___y_1126_;
goto v___jp_769_;
}
}
else
{
v___y_770_ = v___x_1136_;
v___y_771_ = v___y_1123_;
v___y_772_ = v___y_1122_;
v___y_773_ = v___x_1129_;
v___y_774_ = v___y_1124_;
v___y_775_ = v___x_1132_;
v___y_776_ = v___x_1128_;
v___y_777_ = v___x_1135_;
v___y_778_ = v___x_1130_;
v___y_779_ = v___x_1137_;
v___y_780_ = v___y_1126_;
goto v___jp_769_;
}
}
}
else
{
lean_object* v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = l_Lean_Syntax_getArg(v_x_1000_, v___y_1125_);
lean_dec(v_x_1000_);
v___x_1140_ = l_Lean_Syntax_matchesNull(v___x_1139_, v___x_481_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; uint8_t v___x_1142_; 
v___x_1141_ = l_Lean_Syntax_getNumArgs(v___y_1124_);
v___x_1142_ = lean_nat_dec_le(v___x_482_, v___x_1141_);
if (v___x_1142_ == 0)
{
lean_dec(v___x_1141_);
lean_dec(v___x_1128_);
lean_dec(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1143_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_1144_ = l_Array_extract___redArg(v___x_1143_, v___x_482_, v___y_1121_);
lean_dec_ref(v___x_1143_);
v___x_1145_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1146_ = lean_box(2);
v___x_1147_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1146_);
lean_ctor_set(v___x_1147_, 1, v___x_1145_);
lean_ctor_set(v___x_1147_, 2, v___x_1144_);
if (v___x_1140_ == 0)
{
uint8_t v___x_1148_; 
lean_inc(v___y_1122_);
v___x_1148_ = l_Lean_Syntax_isOfKind(v___y_1122_, v___y_1120_);
if (v___x_1148_ == 0)
{
lean_dec_ref_known(v___x_1147_, 3);
lean_dec(v___x_1141_);
lean_dec(v___x_1128_);
lean_dec(v___y_1124_);
lean_dec(v___y_1123_);
lean_dec(v___y_1122_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
v___y_789_ = v___x_1141_;
v___y_790_ = v___y_1123_;
v___y_791_ = v___y_1122_;
v___y_792_ = v___x_1146_;
v___y_793_ = v___x_1129_;
v___y_794_ = v___x_1145_;
v___y_795_ = v___y_1124_;
v___y_796_ = v___x_1128_;
v___y_797_ = v___x_1140_;
v___y_798_ = v___x_1147_;
v___y_799_ = v___y_1126_;
goto v___jp_788_;
}
}
else
{
v___y_789_ = v___x_1141_;
v___y_790_ = v___y_1123_;
v___y_791_ = v___y_1122_;
v___y_792_ = v___x_1146_;
v___y_793_ = v___x_1129_;
v___y_794_ = v___x_1145_;
v___y_795_ = v___y_1124_;
v___y_796_ = v___x_1128_;
v___y_797_ = v___x_1140_;
v___y_798_ = v___x_1147_;
v___y_799_ = v___y_1126_;
goto v___jp_788_;
}
}
}
else
{
lean_object* v_ty_1149_; 
lean_dec(v___y_1124_);
v_ty_1149_ = l_Lean_Syntax_getArg(v___x_1128_, v___x_482_);
lean_dec(v___x_1128_);
if (v___y_1126_ == 0)
{
lean_dec(v_ty_1149_);
lean_dec(v___y_1123_);
lean_dec(v___y_1122_);
lean_dec(v___y_1121_);
lean_dec(v___x_829_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v_xs_1155_; 
v___x_1150_ = l_Lean_Syntax_getArgs(v___x_829_);
lean_dec(v___x_829_);
v___x_1151_ = l_Array_extract___redArg(v___x_1150_, v___x_482_, v___y_1121_);
lean_dec_ref(v___x_1150_);
v___x_1152_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1153_ = lean_box(2);
v___x_1154_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1154_, 0, v___x_1153_);
lean_ctor_set(v___x_1154_, 1, v___x_1152_);
lean_ctor_set(v___x_1154_, 2, v___x_1151_);
v_xs_1155_ = l_Lean_Syntax_getArgs(v___x_1154_);
lean_dec_ref_known(v___x_1154_, 3);
v_x_554_ = v___y_1122_;
v_ty_555_ = v_ty_1149_;
v_xs_556_ = v_xs_1155_;
v_P_557_ = v___y_1123_;
v___y_558_ = v_a_471_;
v___y_559_ = v_a_472_;
goto v___jp_553_;
}
}
}
}
v___jp_1158_:
{
lean_object* v_quotContext_1164_; lean_object* v_currMacroScope_1165_; lean_object* v_ref_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; 
v_quotContext_1164_ = lean_ctor_get(v___y_1162_, 1);
v_currMacroScope_1165_ = lean_ctor_get(v___y_1162_, 2);
v_ref_1166_ = lean_ctor_get(v___y_1162_, 5);
v___x_1167_ = l_Lean_SourceInfo_fromRef(v_ref_1166_, v___x_1157_);
v___x_1168_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_1169_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_1170_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc_n(v_currMacroScope_1165_, 2);
lean_inc_n(v_quotContext_1164_, 2);
v___x_1171_ = l_Lean_addMacroScope(v_quotContext_1164_, v___x_1170_, v_currMacroScope_1165_);
v___x_1172_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc_n(v___x_1167_, 18);
v___x_1173_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1167_);
lean_ctor_set(v___x_1173_, 1, v___x_1169_);
lean_ctor_set(v___x_1173_, 2, v___x_1171_);
lean_ctor_set(v___x_1173_, 3, v___x_1172_);
v___x_1174_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1175_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_1176_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_1177_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
v___x_1178_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1167_);
lean_ctor_set(v___x_1178_, 1, v___x_1177_);
v___x_1179_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_1180_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_1181_ = lean_box(0);
v___x_1182_ = l_Lean_addMacroScope(v_quotContext_1164_, v___x_1181_, v_currMacroScope_1165_);
v___x_1183_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
v___x_1184_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1167_);
lean_ctor_set(v___x_1184_, 1, v___x_1180_);
lean_ctor_set(v___x_1184_, 2, v___x_1182_);
lean_ctor_set(v___x_1184_, 3, v___x_1183_);
v___x_1185_ = l_Lean_Syntax_node1(v___x_1167_, v___x_1179_, v___x_1184_);
v___x_1186_ = l_Lean_Syntax_node2(v___x_1167_, v___x_1176_, v___x_1178_, v___x_1185_);
v___x_1187_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_1188_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
v___x_1189_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1189_, 0, v___x_1167_);
lean_ctor_set(v___x_1189_, 1, v___x_1187_);
v___x_1190_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_1191_ = l_Lean_Syntax_node1(v___x_1167_, v___x_1174_, v_x_1159_);
v___x_1192_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55));
v___x_1193_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
v___x_1194_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1167_);
lean_ctor_set(v___x_1194_, 1, v___x_1193_);
v___x_1195_ = l_Lean_Syntax_node2(v___x_1167_, v___x_1192_, v___x_1194_, v_ty_1160_);
v___x_1196_ = l_Lean_Syntax_node1(v___x_1167_, v___x_1174_, v___x_1195_);
v___x_1197_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_1198_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1167_);
lean_ctor_set(v___x_1198_, 1, v___x_1197_);
v___x_1199_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_1200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1200_, 0, v___x_1167_);
lean_ctor_set(v___x_1200_, 1, v___x_1199_);
v___x_1201_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1202_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1167_);
lean_ctor_set(v___x_1202_, 1, v___x_1201_);
lean_inc_ref(v___x_1202_);
v___x_1203_ = l_Lean_Syntax_node3(v___x_1167_, v___x_477_, v___x_1200_, v_P_1161_, v___x_1202_);
v___x_1204_ = l_Lean_Syntax_node4(v___x_1167_, v___x_1190_, v___x_1191_, v___x_1196_, v___x_1198_, v___x_1203_);
v___x_1205_ = l_Lean_Syntax_node2(v___x_1167_, v___x_1188_, v___x_1189_, v___x_1204_);
v___x_1206_ = l_Lean_Syntax_node3(v___x_1167_, v___x_1175_, v___x_1186_, v___x_1205_, v___x_1202_);
v___x_1207_ = l_Lean_Syntax_node1(v___x_1167_, v___x_1174_, v___x_1206_);
v___x_1208_ = l_Lean_Syntax_node2(v___x_1167_, v___x_1168_, v___x_1173_, v___x_1207_);
v___x_1209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v___y_1163_);
return v___x_1209_;
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
v___jp_684_:
{
if (v___y_692_ == 0)
{
lean_dec(v___y_695_);
lean_dec(v___y_693_);
lean_dec(v___y_691_);
lean_dec(v___y_690_);
lean_dec(v___y_689_);
lean_dec(v___y_688_);
lean_dec(v___y_687_);
lean_dec(v___y_686_);
v___y_474_ = v___y_697_;
goto v___jp_473_;
}
else
{
uint8_t v___x_698_; 
v___x_698_ = l_Lean_Syntax_matchesNull(v___y_690_, v___x_481_);
if (v___x_698_ == 0)
{
lean_dec(v___y_695_);
lean_dec(v___y_693_);
lean_dec(v___y_691_);
lean_dec(v___y_689_);
lean_dec(v___y_688_);
lean_dec(v___y_687_);
lean_dec(v___y_686_);
v___y_474_ = v___y_697_;
goto v___jp_473_;
}
else
{
uint8_t v___x_699_; 
v___x_699_ = l_Lean_Syntax_matchesNull(v___y_691_, v___x_481_);
if (v___x_699_ == 0)
{
lean_dec(v___y_695_);
lean_dec(v___y_693_);
lean_dec(v___y_689_);
lean_dec(v___y_688_);
lean_dec(v___y_687_);
lean_dec(v___y_686_);
v___y_474_ = v___y_697_;
goto v___jp_473_;
}
else
{
lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v_ty_703_; lean_object* v_ys_704_; lean_object* v_xs_705_; 
v___x_700_ = l_Lean_Syntax_getArgs(v___y_695_);
lean_dec(v___y_695_);
v___x_701_ = l_Array_extract___redArg(v___x_700_, v___x_482_, v___y_686_);
lean_dec_ref(v___x_700_);
lean_inc(v___y_696_);
lean_inc(v___y_685_);
v___x_702_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_702_, 0, v___y_685_);
lean_ctor_set(v___x_702_, 1, v___y_696_);
lean_ctor_set(v___x_702_, 2, v___x_701_);
v_ty_703_ = l_Lean_Syntax_getArg(v___y_689_, v___x_482_);
lean_dec(v___y_689_);
v_ys_704_ = l_Lean_Syntax_getArgs(v___y_693_);
lean_dec(v___y_693_);
v_xs_705_ = l_Lean_Syntax_getArgs(v___x_702_);
lean_dec_ref_known(v___x_702_, 3);
v_x_616_ = v___y_687_;
v_xs_617_ = v_xs_705_;
v_ty_618_ = v_ty_703_;
v_ys_619_ = v_ys_704_;
v_P_620_ = v___y_688_;
v___y_621_ = v___y_694_;
v___y_622_ = v___y_697_;
goto v___jp_615_;
}
}
}
}
v___jp_706_:
{
if (v___y_715_ == 0)
{
lean_dec(v___y_718_);
lean_dec(v___y_717_);
lean_dec(v___y_714_);
lean_dec(v___y_713_);
lean_dec(v___y_710_);
lean_dec(v___y_709_);
lean_dec(v___y_707_);
v___y_474_ = v___y_719_;
goto v___jp_473_;
}
else
{
if (v___y_711_ == 0)
{
lean_dec(v___y_718_);
lean_dec(v___y_717_);
lean_dec(v___y_714_);
lean_dec(v___y_713_);
lean_dec(v___y_710_);
lean_dec(v___y_709_);
lean_dec(v___y_707_);
v___y_474_ = v___y_719_;
goto v___jp_473_;
}
else
{
uint8_t v___x_720_; 
v___x_720_ = l_Lean_Syntax_matchesNull(v___y_714_, v___x_481_);
if (v___x_720_ == 0)
{
lean_dec(v___y_718_);
lean_dec(v___y_717_);
lean_dec(v___y_713_);
lean_dec(v___y_710_);
lean_dec(v___y_709_);
lean_dec(v___y_707_);
v___y_474_ = v___y_719_;
goto v___jp_473_;
}
else
{
lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v_ty_724_; lean_object* v_ys_725_; lean_object* v_xs_726_; 
v___x_721_ = l_Lean_Syntax_getArgs(v___y_718_);
lean_dec(v___y_718_);
v___x_722_ = l_Array_extract___redArg(v___x_721_, v___x_482_, v___y_707_);
lean_dec_ref(v___x_721_);
lean_inc(v___y_708_);
lean_inc(v___y_712_);
v___x_723_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_723_, 0, v___y_712_);
lean_ctor_set(v___x_723_, 1, v___y_708_);
lean_ctor_set(v___x_723_, 2, v___x_722_);
v_ty_724_ = l_Lean_Syntax_getArg(v___y_713_, v___x_482_);
lean_dec(v___y_713_);
v_ys_725_ = l_Lean_Syntax_getArgs(v___y_717_);
lean_dec(v___y_717_);
v_xs_726_ = l_Lean_Syntax_getArgs(v___x_723_);
lean_dec_ref_known(v___x_723_, 3);
v_x_616_ = v___y_709_;
v_xs_617_ = v_xs_726_;
v_ty_618_ = v_ty_724_;
v_ys_619_ = v_ys_725_;
v_P_620_ = v___y_710_;
v___y_621_ = v___y_716_;
v___y_622_ = v___y_719_;
goto v___jp_615_;
}
}
}
}
v___jp_727_:
{
if (v___y_734_ == 0)
{
lean_dec(v___y_739_);
lean_dec(v___y_737_);
lean_dec(v___y_732_);
lean_dec(v___y_731_);
lean_dec(v___y_729_);
lean_dec(v___y_728_);
v___y_474_ = v___y_738_;
goto v___jp_473_;
}
else
{
if (v___y_733_ == 0)
{
lean_dec(v___y_739_);
lean_dec(v___y_737_);
lean_dec(v___y_732_);
lean_dec(v___y_731_);
lean_dec(v___y_729_);
lean_dec(v___y_728_);
v___y_474_ = v___y_738_;
goto v___jp_473_;
}
else
{
if (v___y_730_ == 0)
{
lean_dec(v___y_739_);
lean_dec(v___y_737_);
lean_dec(v___y_732_);
lean_dec(v___y_731_);
lean_dec(v___y_729_);
lean_dec(v___y_728_);
v___y_474_ = v___y_738_;
goto v___jp_473_;
}
else
{
lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v_ys_744_; lean_object* v_xs_745_; 
v___x_741_ = l_Lean_Syntax_getArgs(v___y_737_);
lean_dec(v___y_737_);
v___x_742_ = l_Array_extract___redArg(v___x_741_, v___x_482_, v___y_731_);
lean_dec_ref(v___x_741_);
lean_inc(v___y_740_);
lean_inc(v___y_735_);
v___x_743_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_743_, 0, v___y_735_);
lean_ctor_set(v___x_743_, 1, v___y_740_);
lean_ctor_set(v___x_743_, 2, v___x_742_);
v_ys_744_ = l_Lean_Syntax_getArgs(v___y_728_);
lean_dec(v___y_728_);
v_xs_745_ = l_Lean_Syntax_getArgs(v___x_743_);
lean_dec_ref_known(v___x_743_, 3);
v_x_616_ = v___y_729_;
v_xs_617_ = v_xs_745_;
v_ty_618_ = v___y_739_;
v_ys_619_ = v_ys_744_;
v_P_620_ = v___y_732_;
v___y_621_ = v___y_736_;
v___y_622_ = v___y_738_;
goto v___jp_615_;
}
}
}
}
v___jp_746_:
{
uint8_t v___x_760_; 
lean_inc(v___y_754_);
v___x_760_ = l_Lean_Syntax_matchesNull(v___y_754_, v___y_752_);
if (v___x_760_ == 0)
{
lean_dec(v___y_758_);
lean_dec(v___y_755_);
lean_dec(v___y_754_);
lean_dec(v___y_753_);
lean_dec(v___y_751_);
lean_dec(v___y_750_);
lean_dec(v___y_749_);
lean_dec(v___y_747_);
v___y_474_ = v___y_759_;
goto v___jp_473_;
}
else
{
uint8_t v___x_761_; 
v___x_761_ = l_Lean_Syntax_matchesNull(v___y_749_, v___x_481_);
if (v___x_761_ == 0)
{
lean_dec(v___y_758_);
lean_dec(v___y_755_);
lean_dec(v___y_754_);
lean_dec(v___y_753_);
lean_dec(v___y_751_);
lean_dec(v___y_750_);
lean_dec(v___y_747_);
v___y_474_ = v___y_759_;
goto v___jp_473_;
}
else
{
uint8_t v___x_762_; 
v___x_762_ = l_Lean_Syntax_matchesNull(v___y_755_, v___x_481_);
if (v___x_762_ == 0)
{
lean_dec(v___y_758_);
lean_dec(v___y_754_);
lean_dec(v___y_753_);
lean_dec(v___y_751_);
lean_dec(v___y_750_);
lean_dec(v___y_747_);
v___y_474_ = v___y_759_;
goto v___jp_473_;
}
else
{
lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v_ty_766_; lean_object* v_ys_767_; lean_object* v_xs_768_; 
v___x_763_ = l_Lean_Syntax_getArgs(v___y_758_);
lean_dec(v___y_758_);
v___x_764_ = l_Array_extract___redArg(v___x_763_, v___x_482_, v___y_747_);
lean_dec_ref(v___x_763_);
lean_inc(v___y_757_);
lean_inc(v___y_748_);
v___x_765_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_765_, 0, v___y_748_);
lean_ctor_set(v___x_765_, 1, v___y_757_);
lean_ctor_set(v___x_765_, 2, v___x_764_);
v_ty_766_ = l_Lean_Syntax_getArg(v___y_754_, v___x_482_);
lean_dec(v___y_754_);
v_ys_767_ = l_Lean_Syntax_getArgs(v___y_750_);
lean_dec(v___y_750_);
v_xs_768_ = l_Lean_Syntax_getArgs(v___x_765_);
lean_dec_ref_known(v___x_765_, 3);
v_x_616_ = v___y_751_;
v_xs_617_ = v_xs_768_;
v_ty_618_ = v_ty_766_;
v_ys_619_ = v_ys_767_;
v_P_620_ = v___y_753_;
v___y_621_ = v___y_756_;
v___y_622_ = v___y_759_;
goto v___jp_615_;
}
}
}
}
v___jp_769_:
{
if (v___y_773_ == 0)
{
lean_dec(v___y_779_);
lean_dec(v___y_778_);
lean_dec(v___y_776_);
lean_dec(v___y_775_);
lean_dec(v___y_774_);
lean_dec(v___y_772_);
lean_dec(v___y_771_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
uint8_t v___x_781_; 
v___x_781_ = l_Lean_Syntax_matchesNull(v___y_775_, v___x_481_);
if (v___x_781_ == 0)
{
lean_dec(v___y_779_);
lean_dec(v___y_778_);
lean_dec(v___y_776_);
lean_dec(v___y_774_);
lean_dec(v___y_772_);
lean_dec(v___y_771_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___y_780_ == 0)
{
lean_dec(v___y_779_);
lean_dec(v___y_778_);
lean_dec(v___y_776_);
lean_dec(v___y_774_);
lean_dec(v___y_772_);
lean_dec(v___y_771_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v_ty_785_; lean_object* v_ys_786_; lean_object* v_xs_787_; 
v___x_782_ = l_Lean_Syntax_getArgs(v___y_774_);
lean_dec(v___y_774_);
v___x_783_ = l_Array_extract___redArg(v___x_782_, v___x_482_, v___y_778_);
lean_dec_ref(v___x_782_);
lean_inc(v___y_777_);
lean_inc(v___y_770_);
v___x_784_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_784_, 0, v___y_770_);
lean_ctor_set(v___x_784_, 1, v___y_777_);
lean_ctor_set(v___x_784_, 2, v___x_783_);
v_ty_785_ = l_Lean_Syntax_getArg(v___y_776_, v___x_482_);
lean_dec(v___y_776_);
v_ys_786_ = l_Lean_Syntax_getArgs(v___y_779_);
lean_dec(v___y_779_);
v_xs_787_ = l_Lean_Syntax_getArgs(v___x_784_);
lean_dec_ref_known(v___x_784_, 3);
v_x_616_ = v___y_772_;
v_xs_617_ = v_xs_787_;
v_ty_618_ = v_ty_785_;
v_ys_619_ = v_ys_786_;
v_P_620_ = v___y_771_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
v___jp_788_:
{
if (v___y_793_ == 0)
{
lean_dec(v___y_798_);
lean_dec(v___y_796_);
lean_dec(v___y_795_);
lean_dec(v___y_791_);
lean_dec(v___y_790_);
lean_dec(v___y_789_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___y_797_ == 0)
{
lean_dec(v___y_798_);
lean_dec(v___y_796_);
lean_dec(v___y_795_);
lean_dec(v___y_791_);
lean_dec(v___y_790_);
lean_dec(v___y_789_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___y_799_ == 0)
{
lean_dec(v___y_798_);
lean_dec(v___y_796_);
lean_dec(v___y_795_);
lean_dec(v___y_791_);
lean_dec(v___y_790_);
lean_dec(v___y_789_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v_ty_803_; lean_object* v_ys_804_; lean_object* v_xs_805_; 
v___x_800_ = l_Lean_Syntax_getArgs(v___y_795_);
lean_dec(v___y_795_);
v___x_801_ = l_Array_extract___redArg(v___x_800_, v___x_482_, v___y_789_);
lean_dec_ref(v___x_800_);
lean_inc(v___y_794_);
lean_inc(v___y_792_);
v___x_802_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_802_, 0, v___y_792_);
lean_ctor_set(v___x_802_, 1, v___y_794_);
lean_ctor_set(v___x_802_, 2, v___x_801_);
v_ty_803_ = l_Lean_Syntax_getArg(v___y_796_, v___x_482_);
lean_dec(v___y_796_);
v_ys_804_ = l_Lean_Syntax_getArgs(v___y_798_);
lean_dec(v___y_798_);
v_xs_805_ = l_Lean_Syntax_getArgs(v___x_802_);
lean_dec_ref_known(v___x_802_, 3);
v_x_616_ = v___y_791_;
v_xs_617_ = v_xs_805_;
v_ty_618_ = v_ty_803_;
v_ys_619_ = v_ys_804_;
v_P_620_ = v___y_790_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
v___jp_806_:
{
uint8_t v___x_818_; 
lean_inc(v___y_809_);
v___x_818_ = l_Lean_Syntax_matchesNull(v___y_809_, v___y_817_);
if (v___x_818_ == 0)
{
lean_dec(v___y_816_);
lean_dec(v___y_814_);
lean_dec(v___y_813_);
lean_dec(v___y_811_);
lean_dec(v___y_809_);
lean_dec(v___y_808_);
lean_dec(v___y_807_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
uint8_t v___x_819_; 
v___x_819_ = l_Lean_Syntax_matchesNull(v___y_816_, v___x_481_);
if (v___x_819_ == 0)
{
lean_dec(v___y_814_);
lean_dec(v___y_813_);
lean_dec(v___y_811_);
lean_dec(v___y_809_);
lean_dec(v___y_808_);
lean_dec(v___y_807_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
if (v___y_815_ == 0)
{
lean_dec(v___y_814_);
lean_dec(v___y_813_);
lean_dec(v___y_811_);
lean_dec(v___y_809_);
lean_dec(v___y_808_);
lean_dec(v___y_807_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v_ty_823_; lean_object* v_ys_824_; lean_object* v_xs_825_; 
v___x_820_ = l_Lean_Syntax_getArgs(v___y_811_);
lean_dec(v___y_811_);
v___x_821_ = l_Array_extract___redArg(v___x_820_, v___x_482_, v___y_813_);
lean_dec_ref(v___x_820_);
lean_inc(v___y_810_);
lean_inc(v___y_812_);
v___x_822_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_822_, 0, v___y_812_);
lean_ctor_set(v___x_822_, 1, v___y_810_);
lean_ctor_set(v___x_822_, 2, v___x_821_);
v_ty_823_ = l_Lean_Syntax_getArg(v___y_809_, v___x_482_);
lean_dec(v___y_809_);
v_ys_824_ = l_Lean_Syntax_getArgs(v___y_814_);
lean_dec(v___y_814_);
v_xs_825_ = l_Lean_Syntax_getArgs(v___x_822_);
lean_dec_ref_known(v___x_822_, 3);
v_x_616_ = v___y_808_;
v_xs_617_ = v_xs_825_;
v_ty_618_ = v_ty_823_;
v_ys_619_ = v_ys_824_;
v_P_620_ = v___y_807_;
v___y_621_ = v_a_471_;
v___y_622_ = v_a_472_;
goto v___jp_615_;
}
}
}
}
}
else
{
lean_object* v___x_2311_; 
v___x_2311_ = l_Lean_Syntax_getArg(v___x_483_, v___x_482_);
if (v___x_493_ == 0)
{
lean_object* v___x_2324_; uint8_t v___x_2325_; 
v___x_2324_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__67));
lean_inc(v___x_2311_);
v___x_2325_ = l_Lean_Syntax_isOfKind(v___x_2311_, v___x_2324_);
if (v___x_2325_ == 0)
{
lean_object* v___x_2326_; lean_object* v___x_2327_; 
lean_dec(v___x_2311_);
lean_dec(v___x_483_);
v___x_2326_ = lean_box(1);
v___x_2327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2326_);
lean_ctor_set(v___x_2327_, 1, v_a_472_);
return v___x_2327_;
}
else
{
goto v___jp_2312_;
}
}
else
{
goto v___jp_2312_;
}
v___jp_2312_:
{
lean_object* v_ref_2313_; lean_object* v___x_2314_; lean_object* v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
v_ref_2313_ = lean_ctor_get(v_a_471_, 5);
v___x_2314_ = lean_unsigned_to_nat(3u);
v___x_2315_ = l_Lean_Syntax_getArg(v___x_483_, v___x_2314_);
lean_dec(v___x_483_);
v___x_2316_ = l_Lean_SourceInfo_fromRef(v_ref_2313_, v___x_493_);
v___x_2317_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2316_, 2);
v___x_2318_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2316_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
v___x_2319_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2320_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2320_, 0, v___x_2316_);
lean_ctor_set(v___x_2320_, 1, v___x_2319_);
v___x_2321_ = l_Lean_Syntax_node3(v___x_2316_, v___x_477_, v___x_2318_, v___x_2315_, v___x_2320_);
v___x_2322_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65));
v___x_2323_ = l_Lean_expandExplicitBinders(v___x_2322_, v___x_2311_, v___x_2321_, v_a_471_, v_a_472_);
lean_dec(v___x_2311_);
return v___x_2323_;
}
}
}
else
{
lean_object* v_quotContext_2328_; lean_object* v_currMacroScope_2329_; lean_object* v_ref_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; lean_object* v___x_2350_; 
v_quotContext_2328_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_2329_ = lean_ctor_get(v_a_471_, 2);
v_ref_2330_ = lean_ctor_get(v_a_471_, 5);
v___x_2331_ = l_Lean_Syntax_getArg(v___x_483_, v___x_481_);
v___x_2332_ = lean_unsigned_to_nat(2u);
v___x_2333_ = l_Lean_Syntax_getArg(v___x_483_, v___x_2332_);
lean_dec(v___x_483_);
v___x_2334_ = l_Lean_SourceInfo_fromRef(v_ref_2330_, v___x_491_);
v___x_2335_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2336_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__69, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__69_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__69);
v___x_2337_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__71));
lean_inc(v_currMacroScope_2329_);
lean_inc(v_quotContext_2328_);
v___x_2338_ = l_Lean_addMacroScope(v_quotContext_2328_, v___x_2337_, v_currMacroScope_2329_);
v___x_2339_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__74));
lean_inc_n(v___x_2334_, 6);
v___x_2340_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2340_, 0, v___x_2334_);
lean_ctor_set(v___x_2340_, 1, v___x_2336_);
lean_ctor_set(v___x_2340_, 2, v___x_2338_);
lean_ctor_set(v___x_2340_, 3, v___x_2339_);
v___x_2341_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2342_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_2343_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2334_);
lean_ctor_set(v___x_2343_, 1, v___x_2342_);
v___x_2344_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2345_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2334_);
lean_ctor_set(v___x_2345_, 1, v___x_2344_);
lean_inc_ref(v___x_2345_);
lean_inc_ref(v___x_2343_);
v___x_2346_ = l_Lean_Syntax_node3(v___x_2334_, v___x_477_, v___x_2343_, v___x_2331_, v___x_2345_);
v___x_2347_ = l_Lean_Syntax_node3(v___x_2334_, v___x_477_, v___x_2343_, v___x_2333_, v___x_2345_);
v___x_2348_ = l_Lean_Syntax_node2(v___x_2334_, v___x_2341_, v___x_2346_, v___x_2347_);
v___x_2349_ = l_Lean_Syntax_node2(v___x_2334_, v___x_2335_, v___x_2340_, v___x_2348_);
v___x_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2350_, 0, v___x_2349_);
lean_ctor_set(v___x_2350_, 1, v_a_472_);
return v___x_2350_;
}
}
else
{
lean_object* v_quotContext_2351_; lean_object* v_currMacroScope_2352_; lean_object* v_ref_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v_quotContext_2351_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_2352_ = lean_ctor_get(v_a_471_, 2);
v_ref_2353_ = lean_ctor_get(v_a_471_, 5);
v___x_2354_ = l_Lean_Syntax_getArg(v___x_483_, v___x_481_);
v___x_2355_ = lean_unsigned_to_nat(2u);
v___x_2356_ = l_Lean_Syntax_getArg(v___x_483_, v___x_2355_);
lean_dec(v___x_483_);
v___x_2357_ = l_Lean_SourceInfo_fromRef(v_ref_2353_, v___x_489_);
v___x_2358_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2359_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__76, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__76_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__76);
v___x_2360_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__78));
lean_inc(v_currMacroScope_2352_);
lean_inc(v_quotContext_2351_);
v___x_2361_ = l_Lean_addMacroScope(v_quotContext_2351_, v___x_2360_, v_currMacroScope_2352_);
v___x_2362_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__81));
lean_inc_n(v___x_2357_, 6);
v___x_2363_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2363_, 0, v___x_2357_);
lean_ctor_set(v___x_2363_, 1, v___x_2359_);
lean_ctor_set(v___x_2363_, 2, v___x_2361_);
lean_ctor_set(v___x_2363_, 3, v___x_2362_);
v___x_2364_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2365_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_2366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2366_, 0, v___x_2357_);
lean_ctor_set(v___x_2366_, 1, v___x_2365_);
v___x_2367_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2368_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2368_, 0, v___x_2357_);
lean_ctor_set(v___x_2368_, 1, v___x_2367_);
lean_inc_ref(v___x_2368_);
lean_inc_ref(v___x_2366_);
v___x_2369_ = l_Lean_Syntax_node3(v___x_2357_, v___x_477_, v___x_2366_, v___x_2354_, v___x_2368_);
v___x_2370_ = l_Lean_Syntax_node3(v___x_2357_, v___x_477_, v___x_2366_, v___x_2356_, v___x_2368_);
v___x_2371_ = l_Lean_Syntax_node2(v___x_2357_, v___x_2364_, v___x_2369_, v___x_2370_);
v___x_2372_ = l_Lean_Syntax_node2(v___x_2357_, v___x_2358_, v___x_2363_, v___x_2371_);
v___x_2373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2373_, 0, v___x_2372_);
lean_ctor_set(v___x_2373_, 1, v_a_472_);
return v___x_2373_;
}
}
else
{
lean_object* v_quotContext_2374_; lean_object* v_currMacroScope_2375_; lean_object* v_ref_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v_quotContext_2374_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_2375_ = lean_ctor_get(v_a_471_, 2);
v_ref_2376_ = lean_ctor_get(v_a_471_, 5);
v___x_2377_ = l_Lean_Syntax_getArg(v___x_483_, v___x_482_);
lean_dec(v___x_483_);
v___x_2378_ = l_Lean_SourceInfo_fromRef(v_ref_2376_, v___x_487_);
v___x_2379_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2380_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__83, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__83_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__83);
v___x_2381_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__85));
lean_inc(v_currMacroScope_2375_);
lean_inc(v_quotContext_2374_);
v___x_2382_ = l_Lean_addMacroScope(v_quotContext_2374_, v___x_2381_, v_currMacroScope_2375_);
v___x_2383_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__90));
lean_inc_n(v___x_2378_, 5);
v___x_2384_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2384_, 0, v___x_2378_);
lean_ctor_set(v___x_2384_, 1, v___x_2380_);
lean_ctor_set(v___x_2384_, 2, v___x_2382_);
lean_ctor_set(v___x_2384_, 3, v___x_2383_);
v___x_2385_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2386_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_2387_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2387_, 0, v___x_2378_);
lean_ctor_set(v___x_2387_, 1, v___x_2386_);
v___x_2388_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2389_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2389_, 0, v___x_2378_);
lean_ctor_set(v___x_2389_, 1, v___x_2388_);
v___x_2390_ = l_Lean_Syntax_node3(v___x_2378_, v___x_477_, v___x_2387_, v___x_2377_, v___x_2389_);
v___x_2391_ = l_Lean_Syntax_node1(v___x_2378_, v___x_2385_, v___x_2390_);
v___x_2392_ = l_Lean_Syntax_node2(v___x_2378_, v___x_2379_, v___x_2384_, v___x_2391_);
v___x_2393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2393_, 0, v___x_2392_);
lean_ctor_set(v___x_2393_, 1, v_a_472_);
return v___x_2393_;
}
}
else
{
lean_object* v_quotContext_2394_; lean_object* v_currMacroScope_2395_; lean_object* v_ref_2396_; lean_object* v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v_quotContext_2394_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_2395_ = lean_ctor_get(v_a_471_, 2);
v_ref_2396_ = lean_ctor_get(v_a_471_, 5);
v___x_2397_ = l_Lean_Syntax_getArg(v___x_483_, v___x_481_);
v___x_2398_ = lean_unsigned_to_nat(2u);
v___x_2399_ = l_Lean_Syntax_getArg(v___x_483_, v___x_2398_);
lean_dec(v___x_483_);
v___x_2400_ = l_Lean_SourceInfo_fromRef(v_ref_2396_, v___x_485_);
v___x_2401_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2402_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__92, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__92_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__92);
v___x_2403_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__94));
lean_inc(v_currMacroScope_2395_);
lean_inc(v_quotContext_2394_);
v___x_2404_ = l_Lean_addMacroScope(v_quotContext_2394_, v___x_2403_, v_currMacroScope_2395_);
v___x_2405_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__97));
lean_inc_n(v___x_2400_, 6);
v___x_2406_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2400_);
lean_ctor_set(v___x_2406_, 1, v___x_2402_);
lean_ctor_set(v___x_2406_, 2, v___x_2404_);
lean_ctor_set(v___x_2406_, 3, v___x_2405_);
v___x_2407_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2408_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_2409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2400_);
lean_ctor_set(v___x_2409_, 1, v___x_2408_);
v___x_2410_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2411_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2400_);
lean_ctor_set(v___x_2411_, 1, v___x_2410_);
lean_inc_ref(v___x_2411_);
lean_inc_ref(v___x_2409_);
v___x_2412_ = l_Lean_Syntax_node3(v___x_2400_, v___x_477_, v___x_2409_, v___x_2397_, v___x_2411_);
v___x_2413_ = l_Lean_Syntax_node3(v___x_2400_, v___x_477_, v___x_2409_, v___x_2399_, v___x_2411_);
v___x_2414_ = l_Lean_Syntax_node2(v___x_2400_, v___x_2407_, v___x_2412_, v___x_2413_);
v___x_2415_ = l_Lean_Syntax_node2(v___x_2400_, v___x_2401_, v___x_2406_, v___x_2414_);
v___x_2416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
lean_ctor_set(v___x_2416_, 1, v_a_472_);
return v___x_2416_;
}
}
else
{
lean_object* v_quotContext_2417_; lean_object* v_currMacroScope_2418_; lean_object* v_ref_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; uint8_t v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; lean_object* v___x_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v_quotContext_2417_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_2418_ = lean_ctor_get(v_a_471_, 2);
v_ref_2419_ = lean_ctor_get(v_a_471_, 5);
v___x_2420_ = l_Lean_Syntax_getArg(v___x_483_, v___x_481_);
v___x_2421_ = lean_unsigned_to_nat(2u);
v___x_2422_ = l_Lean_Syntax_getArg(v___x_483_, v___x_2421_);
lean_dec(v___x_483_);
v___x_2423_ = 0;
v___x_2424_ = l_Lean_SourceInfo_fromRef(v_ref_2419_, v___x_2423_);
v___x_2425_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2426_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__99, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__99_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__99);
v___x_2427_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__101));
lean_inc(v_currMacroScope_2418_);
lean_inc(v_quotContext_2417_);
v___x_2428_ = l_Lean_addMacroScope(v_quotContext_2417_, v___x_2427_, v_currMacroScope_2418_);
v___x_2429_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__104));
lean_inc_n(v___x_2424_, 6);
v___x_2430_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2430_, 0, v___x_2424_);
lean_ctor_set(v___x_2430_, 1, v___x_2426_);
lean_ctor_set(v___x_2430_, 2, v___x_2428_);
lean_ctor_set(v___x_2430_, 3, v___x_2429_);
v___x_2431_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2432_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_2433_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2433_, 0, v___x_2424_);
lean_ctor_set(v___x_2433_, 1, v___x_2432_);
v___x_2434_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2435_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2435_, 0, v___x_2424_);
lean_ctor_set(v___x_2435_, 1, v___x_2434_);
lean_inc_ref(v___x_2435_);
lean_inc_ref(v___x_2433_);
v___x_2436_ = l_Lean_Syntax_node3(v___x_2424_, v___x_477_, v___x_2433_, v___x_2420_, v___x_2435_);
v___x_2437_ = l_Lean_Syntax_node3(v___x_2424_, v___x_477_, v___x_2433_, v___x_2422_, v___x_2435_);
v___x_2438_ = l_Lean_Syntax_node2(v___x_2424_, v___x_2431_, v___x_2436_, v___x_2437_);
v___x_2439_ = l_Lean_Syntax_node2(v___x_2424_, v___x_2425_, v___x_2430_, v___x_2438_);
v___x_2440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2439_);
lean_ctor_set(v___x_2440_, 1, v_a_472_);
return v___x_2440_;
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
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___boxed(lean_object* v_x_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_){
_start:
{
lean_object* v_res_2444_; 
v_res_2444_ = l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1(v_x_2441_, v_a_2442_, v_a_2443_);
lean_dec_ref(v_a_2442_);
return v_res_2444_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__1(void){
_start:
{
lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2446_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__0));
v___x_2447_ = l_String_toRawSubstring_x27(v___x_2446_);
return v___x_2447_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1(lean_object* v_x_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_){
_start:
{
lean_object* v___x_2464_; uint8_t v___x_2465_; 
v___x_2464_ = ((lean_object*)(l_Std_Do_term_u22a2_u209b___00__closed__1));
lean_inc(v_x_2461_);
v___x_2465_ = l_Lean_Syntax_isOfKind(v_x_2461_, v___x_2464_);
if (v___x_2465_ == 0)
{
lean_object* v___x_2466_; lean_object* v___x_2467_; 
lean_dec(v_x_2461_);
v___x_2466_ = lean_box(1);
v___x_2467_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2467_, 0, v___x_2466_);
lean_ctor_set(v___x_2467_, 1, v_a_2463_);
return v___x_2467_;
}
else
{
lean_object* v_quotContext_2468_; lean_object* v_currMacroScope_2469_; lean_object* v_ref_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; uint8_t v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; 
v_quotContext_2468_ = lean_ctor_get(v_a_2462_, 1);
v_currMacroScope_2469_ = lean_ctor_get(v_a_2462_, 2);
v_ref_2470_ = lean_ctor_get(v_a_2462_, 5);
v___x_2471_ = lean_unsigned_to_nat(1u);
v___x_2472_ = l_Lean_Syntax_getArg(v_x_2461_, v___x_2471_);
lean_dec(v_x_2461_);
v___x_2473_ = 0;
v___x_2474_ = l_Lean_SourceInfo_fromRef(v_ref_2470_, v___x_2473_);
v___x_2475_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2476_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__1, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__1);
v___x_2477_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__3));
lean_inc_n(v_currMacroScope_2469_, 2);
lean_inc_n(v_quotContext_2468_, 2);
v___x_2478_ = l_Lean_addMacroScope(v_quotContext_2468_, v___x_2477_, v_currMacroScope_2469_);
v___x_2479_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__8));
lean_inc_n(v___x_2474_, 9);
v___x_2480_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2480_, 0, v___x_2474_);
lean_ctor_set(v___x_2480_, 1, v___x_2476_);
lean_ctor_set(v___x_2480_, 2, v___x_2478_);
lean_ctor_set(v___x_2480_, 3, v___x_2479_);
v___x_2481_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2482_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__3));
v___x_2483_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__6));
v___x_2484_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2484_, 0, v___x_2474_);
lean_ctor_set(v___x_2484_, 1, v___x_2483_);
v___x_2485_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__1, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__1);
v___x_2486_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__2));
v___x_2487_ = l_Lean_addMacroScope(v_quotContext_2468_, v___x_2486_, v_currMacroScope_2469_);
v___x_2488_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__6));
v___x_2489_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2489_, 0, v___x_2474_);
lean_ctor_set(v___x_2489_, 1, v___x_2485_);
lean_ctor_set(v___x_2489_, 2, v___x_2487_);
lean_ctor_set(v___x_2489_, 3, v___x_2488_);
v___x_2490_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__12));
v___x_2491_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2491_, 0, v___x_2474_);
lean_ctor_set(v___x_2491_, 1, v___x_2490_);
v___x_2492_ = l_Lean_Syntax_node3(v___x_2474_, v___x_2482_, v___x_2484_, v___x_2489_, v___x_2491_);
v___x_2493_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2494_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_2495_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2495_, 0, v___x_2474_);
lean_ctor_set(v___x_2495_, 1, v___x_2494_);
v___x_2496_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2497_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2497_, 0, v___x_2474_);
lean_ctor_set(v___x_2497_, 1, v___x_2496_);
v___x_2498_ = l_Lean_Syntax_node3(v___x_2474_, v___x_2493_, v___x_2495_, v___x_2472_, v___x_2497_);
v___x_2499_ = l_Lean_Syntax_node2(v___x_2474_, v___x_2481_, v___x_2492_, v___x_2498_);
v___x_2500_ = l_Lean_Syntax_node2(v___x_2474_, v___x_2475_, v___x_2480_, v___x_2499_);
v___x_2501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
lean_ctor_set(v___x_2501_, 1, v_a_2463_);
return v___x_2501_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___boxed(lean_object* v_x_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1(v_x_2502_, v_a_2503_, v_a_2504_);
lean_dec_ref(v_a_2503_);
return v_res_2505_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__1(void){
_start:
{
lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2507_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__0));
v___x_2508_ = l_String_toRawSubstring_x27(v___x_2507_);
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1(lean_object* v_x_2524_, lean_object* v_a_2525_, lean_object* v_a_2526_){
_start:
{
lean_object* v___x_2527_; uint8_t v___x_2528_; 
v___x_2527_ = ((lean_object*)(l_Std_Do_term___u22a3_u22a2_u209b___00__closed__1));
lean_inc(v_x_2524_);
v___x_2528_ = l_Lean_Syntax_isOfKind(v_x_2524_, v___x_2527_);
if (v___x_2528_ == 0)
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
lean_dec(v_x_2524_);
v___x_2529_ = lean_box(1);
v___x_2530_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2530_, 0, v___x_2529_);
lean_ctor_set(v___x_2530_, 1, v_a_2526_);
return v___x_2530_;
}
else
{
lean_object* v_quotContext_2531_; lean_object* v_currMacroScope_2532_; lean_object* v_ref_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; uint8_t v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; 
v_quotContext_2531_ = lean_ctor_get(v_a_2525_, 1);
v_currMacroScope_2532_ = lean_ctor_get(v_a_2525_, 2);
v_ref_2533_ = lean_ctor_get(v_a_2525_, 5);
v___x_2534_ = lean_unsigned_to_nat(0u);
v___x_2535_ = l_Lean_Syntax_getArg(v_x_2524_, v___x_2534_);
v___x_2536_ = lean_unsigned_to_nat(2u);
v___x_2537_ = l_Lean_Syntax_getArg(v_x_2524_, v___x_2536_);
lean_dec(v_x_2524_);
v___x_2538_ = 0;
v___x_2539_ = l_Lean_SourceInfo_fromRef(v_ref_2533_, v___x_2538_);
v___x_2540_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_2541_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__1, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__1);
v___x_2542_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__3));
lean_inc(v_currMacroScope_2532_);
lean_inc(v_quotContext_2531_);
v___x_2543_ = l_Lean_addMacroScope(v_quotContext_2531_, v___x_2542_, v_currMacroScope_2532_);
v___x_2544_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__6));
lean_inc_n(v___x_2539_, 6);
v___x_2545_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2545_, 0, v___x_2539_);
lean_ctor_set(v___x_2545_, 1, v___x_2541_);
lean_ctor_set(v___x_2545_, 2, v___x_2543_);
lean_ctor_set(v___x_2545_, 3, v___x_2544_);
v___x_2546_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2547_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2548_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_2549_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2539_);
lean_ctor_set(v___x_2549_, 1, v___x_2548_);
v___x_2550_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2551_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2551_, 0, v___x_2539_);
lean_ctor_set(v___x_2551_, 1, v___x_2550_);
lean_inc_ref(v___x_2551_);
lean_inc_ref(v___x_2549_);
v___x_2552_ = l_Lean_Syntax_node3(v___x_2539_, v___x_2547_, v___x_2549_, v___x_2535_, v___x_2551_);
v___x_2553_ = l_Lean_Syntax_node3(v___x_2539_, v___x_2547_, v___x_2549_, v___x_2537_, v___x_2551_);
v___x_2554_ = l_Lean_Syntax_node2(v___x_2539_, v___x_2546_, v___x_2552_, v___x_2553_);
v___x_2555_ = l_Lean_Syntax_node2(v___x_2539_, v___x_2540_, v___x_2545_, v___x_2554_);
v___x_2556_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2555_);
lean_ctor_set(v___x_2556_, 1, v_a_2526_);
return v___x_2556_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___boxed(lean_object* v_x_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1(v_x_2557_, v_a_2558_, v_a_2559_);
lean_dec_ref(v_a_2558_);
return v_res_2560_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandPure(lean_object* v_x_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_){
_start:
{
lean_object* v___x_2564_; uint8_t v___x_2565_; 
v___x_2564_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2561_);
v___x_2565_ = l_Lean_Syntax_isOfKind(v_x_2561_, v___x_2564_);
if (v___x_2565_ == 0)
{
lean_object* v___x_2566_; lean_object* v___x_2567_; 
lean_dec(v_x_2561_);
v___x_2566_ = lean_box(0);
v___x_2567_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2567_, 0, v___x_2566_);
lean_ctor_set(v___x_2567_, 1, v_a_2563_);
return v___x_2567_;
}
else
{
lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2570_; uint8_t v___x_2571_; 
v___x_2568_ = lean_unsigned_to_nat(1u);
v___x_2569_ = l_Lean_Syntax_getArg(v_x_2561_, v___x_2568_);
lean_dec(v_x_2561_);
v___x_2570_ = l_Lean_Syntax_getNumArgs(v___x_2569_);
v___x_2571_ = lean_nat_dec_le(v___x_2568_, v___x_2570_);
if (v___x_2571_ == 0)
{
lean_object* v___x_2572_; lean_object* v___x_2573_; 
lean_dec(v___x_2570_);
lean_dec(v___x_2569_);
v___x_2572_ = lean_box(0);
v___x_2573_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2572_);
lean_ctor_set(v___x_2573_, 1, v_a_2563_);
return v___x_2573_;
}
else
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; lean_object* v_ts_2581_; lean_object* v___x_2582_; uint8_t v___x_2583_; 
v___x_2574_ = lean_unsigned_to_nat(0u);
v___x_2575_ = l_Lean_Syntax_getArg(v___x_2569_, v___x_2574_);
v___x_2576_ = l_Lean_Syntax_getArgs(v___x_2569_);
lean_dec(v___x_2569_);
v___x_2577_ = l_Array_extract___redArg(v___x_2576_, v___x_2568_, v___x_2570_);
lean_dec_ref(v___x_2576_);
v___x_2578_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2579_ = lean_box(2);
v___x_2580_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2580_, 0, v___x_2579_);
lean_ctor_set(v___x_2580_, 1, v___x_2578_);
lean_ctor_set(v___x_2580_, 2, v___x_2577_);
v_ts_2581_ = l_Lean_Syntax_getArgs(v___x_2580_);
lean_dec_ref_known(v___x_2580_, 3);
v___x_2582_ = lean_array_get_size(v_ts_2581_);
v___x_2583_ = lean_nat_dec_eq(v___x_2582_, v___x_2574_);
if (v___x_2583_ == 0)
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2584_ = l_Lean_SourceInfo_fromRef(v_a_2562_, v___x_2583_);
v___x_2585_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__3));
v___x_2586_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__6));
lean_inc_n(v___x_2584_, 4);
v___x_2587_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2587_, 0, v___x_2584_);
lean_ctor_set(v___x_2587_, 1, v___x_2586_);
v___x_2588_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__12));
v___x_2589_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2589_, 0, v___x_2584_);
lean_ctor_set(v___x_2589_, 1, v___x_2588_);
v___x_2590_ = l_Lean_Syntax_node3(v___x_2584_, v___x_2585_, v___x_2587_, v___x_2575_, v___x_2589_);
v___x_2591_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2592_ = l_Array_append___redArg(v___x_2591_, v_ts_2581_);
lean_dec_ref(v_ts_2581_);
v___x_2593_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2593_, 0, v___x_2584_);
lean_ctor_set(v___x_2593_, 1, v___x_2578_);
lean_ctor_set(v___x_2593_, 2, v___x_2592_);
v___x_2594_ = l_Lean_Syntax_node2(v___x_2584_, v___x_2564_, v___x_2590_, v___x_2593_);
v___x_2595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2595_, 0, v___x_2594_);
lean_ctor_set(v___x_2595_, 1, v_a_2563_);
return v___x_2595_;
}
else
{
uint8_t v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
lean_dec_ref(v_ts_2581_);
v___x_2596_ = 0;
v___x_2597_ = l_Lean_SourceInfo_fromRef(v_a_2562_, v___x_2596_);
v___x_2598_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__3));
v___x_2599_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__6));
lean_inc_n(v___x_2597_, 2);
v___x_2600_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2600_, 0, v___x_2597_);
lean_ctor_set(v___x_2600_, 1, v___x_2599_);
v___x_2601_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__12));
v___x_2602_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2602_, 0, v___x_2597_);
lean_ctor_set(v___x_2602_, 1, v___x_2601_);
v___x_2603_ = l_Lean_Syntax_node3(v___x_2597_, v___x_2598_, v___x_2600_, v___x_2575_, v___x_2602_);
v___x_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
lean_ctor_set(v___x_2604_, 1, v_a_2563_);
return v___x_2604_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandPure___boxed(lean_object* v_x_2605_, lean_object* v_a_2606_, lean_object* v_a_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l_Std_Do_SPred_Notation_unexpandPure(v_x_2605_, v_a_2606_, v_a_2607_);
lean_dec(v_a_2606_);
return v_res_2608_;
}
}
static lean_object* _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2621_ = lean_unsigned_to_nat(0u);
v___x_2622_ = lean_box(0);
v___x_2623_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__5));
v___x_2624_ = l_Lean_addMacroScope(v___x_2623_, v___x_2622_, v___x_2621_);
return v___x_2624_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(lean_object* v_x_2651_, lean_object* v___y_2652_, lean_object* v___y_2653_){
_start:
{
lean_object* v___x_2654_; uint8_t v___x_2655_; 
v___x_2654_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
lean_inc(v_x_2651_);
v___x_2655_ = l_Lean_Syntax_isOfKind(v_x_2651_, v___x_2654_);
if (v___x_2655_ == 0)
{
lean_object* v___x_2656_; uint8_t v___x_2657_; 
v___x_2656_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
lean_inc(v_x_2651_);
v___x_2657_ = l_Lean_Syntax_isOfKind(v_x_2651_, v___x_2656_);
if (v___x_2657_ == 0)
{
lean_object* v___x_2658_; uint8_t v___x_2659_; 
v___x_2658_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__1));
lean_inc(v_x_2651_);
v___x_2659_ = l_Lean_Syntax_isOfKind(v_x_2651_, v___x_2658_);
if (v___x_2659_ == 0)
{
lean_object* v___x_2660_; lean_object* v___x_2661_; uint8_t v___x_2662_; 
v___x_2660_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_2661_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
lean_inc(v_x_2651_);
v___x_2662_ = l_Lean_Syntax_isOfKind(v_x_2651_, v___x_2661_);
if (v___x_2662_ == 0)
{
lean_object* v___x_2663_; uint8_t v___x_2664_; 
v___x_2663_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__3));
lean_inc(v_x_2651_);
v___x_2664_ = l_Lean_Syntax_isOfKind(v_x_2651_, v___x_2663_);
if (v___x_2664_ == 0)
{
lean_object* v___x_2665_; 
v___x_2665_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2665_, 0, v_x_2651_);
lean_ctor_set(v___x_2665_, 1, v___y_2653_);
return v___x_2665_;
}
else
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; uint8_t v___x_2669_; 
v___x_2666_ = lean_unsigned_to_nat(0u);
v___x_2667_ = l_Lean_Syntax_getArg(v_x_2651_, v___x_2666_);
v___x_2668_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
lean_inc(v___x_2667_);
v___x_2669_ = l_Lean_Syntax_isOfKind(v___x_2667_, v___x_2668_);
if (v___x_2669_ == 0)
{
lean_object* v___x_2670_; 
lean_dec(v___x_2667_);
v___x_2670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2670_, 0, v_x_2651_);
lean_ctor_set(v___x_2670_, 1, v___y_2653_);
return v___x_2670_;
}
else
{
lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; uint8_t v___x_2674_; 
v___x_2671_ = lean_unsigned_to_nat(1u);
v___x_2672_ = l_Lean_Syntax_getArg(v___x_2667_, v___x_2671_);
lean_dec(v___x_2667_);
v___x_2673_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
lean_inc(v___x_2672_);
v___x_2674_ = l_Lean_Syntax_isOfKind(v___x_2672_, v___x_2673_);
if (v___x_2674_ == 0)
{
lean_object* v___x_2675_; 
lean_dec(v___x_2672_);
v___x_2675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2675_, 0, v_x_2651_);
lean_ctor_set(v___x_2675_, 1, v___y_2653_);
return v___x_2675_;
}
else
{
lean_object* v___x_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v___x_2676_ = l_Lean_Syntax_getArg(v___x_2672_, v___x_2666_);
lean_dec(v___x_2672_);
v___x_2677_ = lean_box(0);
v___x_2678_ = l_Lean_Syntax_matchesIdent(v___x_2676_, v___x_2677_);
lean_dec(v___x_2676_);
if (v___x_2678_ == 0)
{
lean_object* v___x_2679_; 
v___x_2679_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2679_, 0, v_x_2651_);
lean_ctor_set(v___x_2679_, 1, v___y_2653_);
return v___x_2679_;
}
else
{
lean_object* v___x_2680_; lean_object* v___x_2681_; uint8_t v___x_2682_; 
v___x_2680_ = lean_unsigned_to_nat(3u);
v___x_2681_ = l_Lean_Syntax_getArg(v_x_2651_, v___x_2680_);
lean_inc(v___x_2681_);
v___x_2682_ = l_Lean_Syntax_matchesNull(v___x_2681_, v___x_2671_);
if (v___x_2682_ == 0)
{
lean_object* v___x_2683_; 
lean_dec(v___x_2681_);
v___x_2683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2683_, 0, v_x_2651_);
lean_ctor_set(v___x_2683_, 1, v___y_2653_);
return v___x_2683_;
}
else
{
lean_object* v_P_2684_; lean_object* v___x_2685_; 
v_P_2684_ = l_Lean_Syntax_getArg(v_x_2651_, v___x_2671_);
lean_dec(v_x_2651_);
v___x_2685_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2684_, v___y_2652_, v___y_2653_);
if (lean_obj_tag(v___x_2685_) == 0)
{
lean_object* v_a_2686_; lean_object* v_a_2687_; lean_object* v___x_2689_; uint8_t v_isShared_2690_; uint8_t v_isSharedCheck_2711_; 
v_a_2686_ = lean_ctor_get(v___x_2685_, 0);
v_a_2687_ = lean_ctor_get(v___x_2685_, 1);
v_isSharedCheck_2711_ = !lean_is_exclusive(v___x_2685_);
if (v_isSharedCheck_2711_ == 0)
{
v___x_2689_ = v___x_2685_;
v_isShared_2690_ = v_isSharedCheck_2711_;
goto v_resetjp_2688_;
}
else
{
lean_inc(v_a_2687_);
lean_inc(v_a_2686_);
lean_dec(v___x_2685_);
v___x_2689_ = lean_box(0);
v_isShared_2690_ = v_isSharedCheck_2711_;
goto v_resetjp_2688_;
}
v_resetjp_2688_:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2709_; 
v___x_2691_ = l_Lean_Syntax_getArg(v___x_2681_, v___x_2666_);
lean_dec(v___x_2681_);
v___x_2692_ = l_Lean_SourceInfo_fromRef(v___y_2652_, v___x_2662_);
v___x_2693_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
lean_inc_n(v___x_2692_, 7);
v___x_2694_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2694_, 0, v___x_2692_);
lean_ctor_set(v___x_2694_, 1, v___x_2693_);
v___x_2695_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_2696_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6, &l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6_once, _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6);
v___x_2697_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__14));
v___x_2698_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2692_);
lean_ctor_set(v___x_2698_, 1, v___x_2695_);
lean_ctor_set(v___x_2698_, 2, v___x_2696_);
lean_ctor_set(v___x_2698_, 3, v___x_2697_);
v___x_2699_ = l_Lean_Syntax_node1(v___x_2692_, v___x_2673_, v___x_2698_);
v___x_2700_ = l_Lean_Syntax_node2(v___x_2692_, v___x_2668_, v___x_2694_, v___x_2699_);
v___x_2701_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
v___x_2702_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2702_, 0, v___x_2692_);
lean_ctor_set(v___x_2702_, 1, v___x_2701_);
v___x_2703_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2704_ = l_Lean_Syntax_node1(v___x_2692_, v___x_2703_, v___x_2691_);
v___x_2705_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2706_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2692_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
v___x_2707_ = l_Lean_Syntax_node5(v___x_2692_, v___x_2663_, v___x_2700_, v_a_2686_, v___x_2702_, v___x_2704_, v___x_2706_);
if (v_isShared_2690_ == 0)
{
lean_ctor_set(v___x_2689_, 0, v___x_2707_);
v___x_2709_ = v___x_2689_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v___x_2707_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v_a_2687_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
else
{
lean_dec(v___x_2681_);
return v___x_2685_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; uint8_t v___x_2715_; 
v___x_2712_ = lean_unsigned_to_nat(1u);
v___x_2713_ = l_Lean_Syntax_getArg(v_x_2651_, v___x_2712_);
v___x_2714_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
lean_inc(v___x_2713_);
v___x_2715_ = l_Lean_Syntax_isOfKind(v___x_2713_, v___x_2714_);
if (v___x_2715_ == 0)
{
lean_object* v___x_2716_; 
lean_dec(v___x_2713_);
v___x_2716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2716_, 0, v_x_2651_);
lean_ctor_set(v___x_2716_, 1, v___y_2653_);
return v___x_2716_;
}
else
{
lean_object* v___x_2717_; lean_object* v___x_2718_; uint8_t v___x_2719_; 
v___x_2717_ = lean_unsigned_to_nat(0u);
v___x_2718_ = l_Lean_Syntax_getArg(v___x_2713_, v___x_2712_);
v___x_2719_ = l_Lean_Syntax_matchesNull(v___x_2718_, v___x_2717_);
if (v___x_2719_ == 0)
{
lean_object* v___x_2720_; 
lean_dec(v___x_2713_);
v___x_2720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2720_, 0, v_x_2651_);
lean_ctor_set(v___x_2720_, 1, v___y_2653_);
return v___x_2720_;
}
else
{
lean_object* v___x_2721_; lean_object* v_b_2722_; lean_object* v___x_2723_; 
lean_dec(v_x_2651_);
v___x_2721_ = lean_unsigned_to_nat(3u);
v_b_2722_ = l_Lean_Syntax_getArg(v___x_2713_, v___x_2721_);
v___x_2723_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_b_2722_, v___y_2652_, v___y_2653_);
if (lean_obj_tag(v___x_2723_) == 0)
{
lean_object* v_a_2724_; lean_object* v_a_2725_; lean_object* v___x_2727_; uint8_t v_isShared_2728_; uint8_t v_isSharedCheck_2745_; 
v_a_2724_ = lean_ctor_get(v___x_2723_, 0);
v_a_2725_ = lean_ctor_get(v___x_2723_, 1);
v_isSharedCheck_2745_ = !lean_is_exclusive(v___x_2723_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2727_ = v___x_2723_;
v_isShared_2728_ = v_isSharedCheck_2745_;
goto v_resetjp_2726_;
}
else
{
lean_inc(v_a_2725_);
lean_inc(v_a_2724_);
lean_dec(v___x_2723_);
v___x_2727_ = lean_box(0);
v_isShared_2728_ = v_isSharedCheck_2745_;
goto v_resetjp_2726_;
}
v_resetjp_2726_:
{
lean_object* v___x_2729_; lean_object* v_xs_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2743_; 
v___x_2729_ = l_Lean_Syntax_getArg(v___x_2713_, v___x_2717_);
lean_dec(v___x_2713_);
v_xs_2730_ = l_Lean_Syntax_getArgs(v___x_2729_);
lean_dec(v___x_2729_);
v___x_2731_ = l_Lean_SourceInfo_fromRef(v___y_2652_, v___x_2659_);
lean_inc_n(v___x_2731_, 5);
v___x_2732_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2732_, 0, v___x_2731_);
lean_ctor_set(v___x_2732_, 1, v___x_2660_);
v___x_2733_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2734_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2735_ = l_Array_append___redArg(v___x_2734_, v_xs_2730_);
lean_dec_ref(v_xs_2730_);
v___x_2736_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2731_);
lean_ctor_set(v___x_2736_, 1, v___x_2733_);
lean_ctor_set(v___x_2736_, 2, v___x_2735_);
v___x_2737_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2737_, 0, v___x_2731_);
lean_ctor_set(v___x_2737_, 1, v___x_2733_);
lean_ctor_set(v___x_2737_, 2, v___x_2734_);
v___x_2738_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_2739_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2731_);
lean_ctor_set(v___x_2739_, 1, v___x_2738_);
v___x_2740_ = l_Lean_Syntax_node4(v___x_2731_, v___x_2714_, v___x_2736_, v___x_2737_, v___x_2739_, v_a_2724_);
v___x_2741_ = l_Lean_Syntax_node2(v___x_2731_, v___x_2661_, v___x_2732_, v___x_2740_);
if (v_isShared_2728_ == 0)
{
lean_ctor_set(v___x_2727_, 0, v___x_2741_);
v___x_2743_ = v___x_2727_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2741_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_a_2725_);
v___x_2743_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
return v___x_2743_;
}
}
}
else
{
lean_dec(v___x_2713_);
return v___x_2723_;
}
}
}
}
}
else
{
lean_object* v___x_2746_; lean_object* v_t_2747_; lean_object* v___x_2748_; 
v___x_2746_ = lean_unsigned_to_nat(3u);
v_t_2747_ = l_Lean_Syntax_getArg(v_x_2651_, v___x_2746_);
v___x_2748_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_t_2747_, v___y_2652_, v___y_2653_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; lean_object* v_a_2750_; lean_object* v___x_2752_; uint8_t v_isShared_2753_; uint8_t v_isSharedCheck_2778_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
v_a_2750_ = lean_ctor_get(v___x_2748_, 1);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2752_ = v___x_2748_;
v_isShared_2753_ = v_isSharedCheck_2778_;
goto v_resetjp_2751_;
}
else
{
lean_inc(v_a_2750_);
lean_inc(v_a_2749_);
lean_dec(v___x_2748_);
v___x_2752_ = lean_box(0);
v_isShared_2753_ = v_isSharedCheck_2778_;
goto v_resetjp_2751_;
}
v_resetjp_2751_:
{
lean_object* v___x_2754_; lean_object* v_e_2755_; lean_object* v___x_2756_; 
v___x_2754_ = lean_unsigned_to_nat(5u);
v_e_2755_ = l_Lean_Syntax_getArg(v_x_2651_, v___x_2754_);
v___x_2756_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_e_2755_, v___y_2652_, v_a_2750_);
if (lean_obj_tag(v___x_2756_) == 0)
{
lean_object* v_a_2757_; lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2777_; 
v_a_2757_ = lean_ctor_get(v___x_2756_, 0);
v_a_2758_ = lean_ctor_get(v___x_2756_, 1);
v_isSharedCheck_2777_ = !lean_is_exclusive(v___x_2756_);
if (v_isSharedCheck_2777_ == 0)
{
v___x_2760_ = v___x_2756_;
v_isShared_2761_ = v_isSharedCheck_2777_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_inc(v_a_2757_);
lean_dec(v___x_2756_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2777_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2767_; 
v___x_2762_ = lean_unsigned_to_nat(1u);
v___x_2763_ = l_Lean_Syntax_getArg(v_x_2651_, v___x_2762_);
lean_dec(v_x_2651_);
v___x_2764_ = l_Lean_SourceInfo_fromRef(v___y_2652_, v___x_2657_);
v___x_2765_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__15));
lean_inc(v___x_2764_);
if (v_isShared_2753_ == 0)
{
lean_ctor_set_tag(v___x_2752_, 2);
lean_ctor_set(v___x_2752_, 1, v___x_2765_);
lean_ctor_set(v___x_2752_, 0, v___x_2764_);
v___x_2767_ = v___x_2752_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2776_; 
v_reuseFailAlloc_2776_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2776_, 0, v___x_2764_);
lean_ctor_set(v_reuseFailAlloc_2776_, 1, v___x_2765_);
v___x_2767_ = v_reuseFailAlloc_2776_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; 
v___x_2768_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__16));
lean_inc_n(v___x_2764_, 2);
v___x_2769_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2764_);
lean_ctor_set(v___x_2769_, 1, v___x_2768_);
v___x_2770_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__17));
v___x_2771_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2771_, 0, v___x_2764_);
lean_ctor_set(v___x_2771_, 1, v___x_2770_);
v___x_2772_ = l_Lean_Syntax_node6(v___x_2764_, v___x_2658_, v___x_2767_, v___x_2763_, v___x_2769_, v_a_2749_, v___x_2771_, v_a_2757_);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v___x_2772_);
v___x_2774_ = v___x_2760_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v___x_2772_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v_a_2758_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
else
{
lean_del_object(v___x_2752_);
lean_dec(v_a_2749_);
lean_dec(v_x_2651_);
return v___x_2756_;
}
}
}
else
{
lean_dec(v_x_2651_);
return v___x_2748_;
}
}
}
else
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; uint8_t v___x_2782_; 
v___x_2779_ = lean_unsigned_to_nat(0u);
v___x_2780_ = l_Lean_Syntax_getArg(v_x_2651_, v___x_2779_);
v___x_2781_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
lean_inc(v___x_2780_);
v___x_2782_ = l_Lean_Syntax_isOfKind(v___x_2780_, v___x_2781_);
if (v___x_2782_ == 0)
{
lean_object* v___x_2783_; 
lean_dec(v___x_2780_);
v___x_2783_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2783_, 0, v_x_2651_);
lean_ctor_set(v___x_2783_, 1, v___y_2653_);
return v___x_2783_;
}
else
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; uint8_t v___x_2787_; 
v___x_2784_ = lean_unsigned_to_nat(1u);
v___x_2785_ = l_Lean_Syntax_getArg(v___x_2780_, v___x_2784_);
lean_dec(v___x_2780_);
v___x_2786_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
lean_inc(v___x_2785_);
v___x_2787_ = l_Lean_Syntax_isOfKind(v___x_2785_, v___x_2786_);
if (v___x_2787_ == 0)
{
lean_object* v___x_2788_; 
lean_dec(v___x_2785_);
v___x_2788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2788_, 0, v_x_2651_);
lean_ctor_set(v___x_2788_, 1, v___y_2653_);
return v___x_2788_;
}
else
{
lean_object* v___x_2789_; lean_object* v___x_2790_; uint8_t v___x_2791_; 
v___x_2789_ = l_Lean_Syntax_getArg(v___x_2785_, v___x_2779_);
lean_dec(v___x_2785_);
v___x_2790_ = lean_box(0);
v___x_2791_ = l_Lean_Syntax_matchesIdent(v___x_2789_, v___x_2790_);
lean_dec(v___x_2789_);
if (v___x_2791_ == 0)
{
lean_object* v___x_2792_; 
v___x_2792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2792_, 0, v_x_2651_);
lean_ctor_set(v___x_2792_, 1, v___y_2653_);
return v___x_2792_;
}
else
{
lean_object* v_P_2793_; lean_object* v___x_2794_; 
v_P_2793_ = l_Lean_Syntax_getArg(v_x_2651_, v___x_2784_);
lean_dec(v_x_2651_);
v___x_2794_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2793_, v___y_2652_, v___y_2653_);
if (lean_obj_tag(v___x_2794_) == 0)
{
lean_object* v_a_2795_; lean_object* v_a_2796_; lean_object* v___x_2798_; uint8_t v_isShared_2799_; uint8_t v_isSharedCheck_2815_; 
v_a_2795_ = lean_ctor_get(v___x_2794_, 0);
v_a_2796_ = lean_ctor_get(v___x_2794_, 1);
v_isSharedCheck_2815_ = !lean_is_exclusive(v___x_2794_);
if (v_isSharedCheck_2815_ == 0)
{
v___x_2798_ = v___x_2794_;
v_isShared_2799_ = v_isSharedCheck_2815_;
goto v_resetjp_2797_;
}
else
{
lean_inc(v_a_2796_);
lean_inc(v_a_2795_);
lean_dec(v___x_2794_);
v___x_2798_ = lean_box(0);
v_isShared_2799_ = v_isSharedCheck_2815_;
goto v_resetjp_2797_;
}
v_resetjp_2797_:
{
lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2813_; 
v___x_2800_ = l_Lean_SourceInfo_fromRef(v___y_2652_, v___x_2655_);
v___x_2801_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
lean_inc_n(v___x_2800_, 5);
v___x_2802_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2802_, 0, v___x_2800_);
lean_ctor_set(v___x_2802_, 1, v___x_2801_);
v___x_2803_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_2804_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6, &l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6_once, _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6);
v___x_2805_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__14));
v___x_2806_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_2806_, 0, v___x_2800_);
lean_ctor_set(v___x_2806_, 1, v___x_2803_);
lean_ctor_set(v___x_2806_, 2, v___x_2804_);
lean_ctor_set(v___x_2806_, 3, v___x_2805_);
v___x_2807_ = l_Lean_Syntax_node1(v___x_2800_, v___x_2786_, v___x_2806_);
v___x_2808_ = l_Lean_Syntax_node2(v___x_2800_, v___x_2781_, v___x_2802_, v___x_2807_);
v___x_2809_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2810_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2810_, 0, v___x_2800_);
lean_ctor_set(v___x_2810_, 1, v___x_2809_);
v___x_2811_ = l_Lean_Syntax_node3(v___x_2800_, v___x_2656_, v___x_2808_, v_a_2795_, v___x_2810_);
if (v_isShared_2799_ == 0)
{
lean_ctor_set(v___x_2798_, 0, v___x_2811_);
v___x_2813_ = v___x_2798_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2814_; 
v_reuseFailAlloc_2814_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2814_, 0, v___x_2811_);
lean_ctor_set(v_reuseFailAlloc_2814_, 1, v_a_2796_);
v___x_2813_ = v_reuseFailAlloc_2814_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
return v___x_2813_;
}
}
}
else
{
return v___x_2794_;
}
}
}
}
}
}
else
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2816_ = lean_unsigned_to_nat(1u);
v___x_2817_ = l_Lean_Syntax_getArg(v_x_2651_, v___x_2816_);
lean_dec(v_x_2651_);
v___x_2818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
lean_ctor_set(v___x_2818_, 1, v___y_2653_);
return v___x_2818_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___boxed(lean_object* v_x_2819_, lean_object* v___y_2820_, lean_object* v___y_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_x_2819_, v___y_2820_, v___y_2821_);
lean_dec(v___y_2820_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandEntails(lean_object* v_x_2824_, lean_object* v_a_2825_, lean_object* v_a_2826_){
_start:
{
lean_object* v___x_2827_; uint8_t v___x_2828_; 
v___x_2827_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2824_);
v___x_2828_ = l_Lean_Syntax_isOfKind(v_x_2824_, v___x_2827_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
lean_dec(v_x_2824_);
v___x_2829_ = lean_box(0);
v___x_2830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
lean_ctor_set(v___x_2830_, 1, v_a_2826_);
return v___x_2830_;
}
else
{
lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; uint8_t v___x_2834_; 
v___x_2831_ = lean_unsigned_to_nat(1u);
v___x_2832_ = l_Lean_Syntax_getArg(v_x_2824_, v___x_2831_);
lean_dec(v_x_2824_);
v___x_2833_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2832_);
v___x_2834_ = l_Lean_Syntax_matchesNull(v___x_2832_, v___x_2833_);
if (v___x_2834_ == 0)
{
lean_object* v___x_2835_; lean_object* v___x_2836_; 
lean_dec(v___x_2832_);
v___x_2835_ = lean_box(0);
v___x_2836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2836_, 0, v___x_2835_);
lean_ctor_set(v___x_2836_, 1, v_a_2826_);
return v___x_2836_;
}
else
{
lean_object* v___x_2837_; lean_object* v_P_2838_; lean_object* v___x_2839_; 
v___x_2837_ = lean_unsigned_to_nat(0u);
v_P_2838_ = l_Lean_Syntax_getArg(v___x_2832_, v___x_2837_);
v___x_2839_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2838_, v_a_2825_, v_a_2826_);
if (lean_obj_tag(v___x_2839_) == 0)
{
lean_object* v_a_2840_; lean_object* v_a_2841_; lean_object* v_Q_2842_; lean_object* v___x_2843_; 
v_a_2840_ = lean_ctor_get(v___x_2839_, 0);
lean_inc(v_a_2840_);
v_a_2841_ = lean_ctor_get(v___x_2839_, 1);
lean_inc(v_a_2841_);
lean_dec_ref_known(v___x_2839_, 2);
v_Q_2842_ = l_Lean_Syntax_getArg(v___x_2832_, v___x_2831_);
lean_dec(v___x_2832_);
v___x_2843_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_2842_, v_a_2825_, v_a_2841_);
if (lean_obj_tag(v___x_2843_) == 0)
{
lean_object* v_a_2844_; lean_object* v_a_2845_; lean_object* v___x_2847_; uint8_t v_isShared_2848_; uint8_t v_isSharedCheck_2879_; 
v_a_2844_ = lean_ctor_get(v___x_2843_, 0);
v_a_2845_ = lean_ctor_get(v___x_2843_, 1);
v_isSharedCheck_2879_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2879_ == 0)
{
v___x_2847_ = v___x_2843_;
v_isShared_2848_ = v_isSharedCheck_2879_;
goto v_resetjp_2846_;
}
else
{
lean_inc(v_a_2845_);
lean_inc(v_a_2844_);
lean_dec(v___x_2843_);
v___x_2847_ = lean_box(0);
v_isShared_2848_ = v_isSharedCheck_2879_;
goto v_resetjp_2846_;
}
v_resetjp_2846_:
{
lean_object* v___x_2849_; uint8_t v___x_2850_; 
v___x_2849_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__3));
lean_inc(v_a_2840_);
v___x_2850_ = l_Lean_Syntax_isOfKind(v_a_2840_, v___x_2849_);
if (v___x_2850_ == 0)
{
lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2857_; 
v___x_2851_ = l_Lean_SourceInfo_fromRef(v_a_2825_, v___x_2850_);
v___x_2852_ = ((lean_object*)(l_Std_Do_term___u22a2_u209b___00__closed__1));
v___x_2853_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandEntails___closed__0));
lean_inc(v___x_2851_);
v___x_2854_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2851_);
lean_ctor_set(v___x_2854_, 1, v___x_2853_);
v___x_2855_ = l_Lean_Syntax_node3(v___x_2851_, v___x_2852_, v_a_2840_, v___x_2854_, v_a_2844_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 0, v___x_2855_);
v___x_2857_ = v___x_2847_;
goto v_reusejp_2856_;
}
else
{
lean_object* v_reuseFailAlloc_2858_; 
v_reuseFailAlloc_2858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2858_, 0, v___x_2855_);
lean_ctor_set(v_reuseFailAlloc_2858_, 1, v_a_2845_);
v___x_2857_ = v_reuseFailAlloc_2858_;
goto v_reusejp_2856_;
}
v_reusejp_2856_:
{
return v___x_2857_;
}
}
else
{
lean_object* v___x_2859_; lean_object* v___x_2860_; uint8_t v___x_2861_; 
v___x_2859_ = l_Lean_Syntax_getArg(v_a_2840_, v___x_2831_);
v___x_2860_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__2));
v___x_2861_ = l_Lean_Syntax_matchesIdent(v___x_2859_, v___x_2860_);
lean_dec(v___x_2859_);
if (v___x_2861_ == 0)
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2868_; 
v___x_2862_ = l_Lean_SourceInfo_fromRef(v_a_2825_, v___x_2861_);
v___x_2863_ = ((lean_object*)(l_Std_Do_term___u22a2_u209b___00__closed__1));
v___x_2864_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandEntails___closed__0));
lean_inc(v___x_2862_);
v___x_2865_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2865_, 0, v___x_2862_);
lean_ctor_set(v___x_2865_, 1, v___x_2864_);
v___x_2866_ = l_Lean_Syntax_node3(v___x_2862_, v___x_2863_, v_a_2840_, v___x_2865_, v_a_2844_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 0, v___x_2866_);
v___x_2868_ = v___x_2847_;
goto v_reusejp_2867_;
}
else
{
lean_object* v_reuseFailAlloc_2869_; 
v_reuseFailAlloc_2869_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2869_, 0, v___x_2866_);
lean_ctor_set(v_reuseFailAlloc_2869_, 1, v_a_2845_);
v___x_2868_ = v_reuseFailAlloc_2869_;
goto v_reusejp_2867_;
}
v_reusejp_2867_:
{
return v___x_2868_;
}
}
else
{
uint8_t v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2877_; 
lean_dec(v_a_2840_);
v___x_2870_ = 0;
v___x_2871_ = l_Lean_SourceInfo_fromRef(v_a_2825_, v___x_2870_);
v___x_2872_ = ((lean_object*)(l_Std_Do_term_u22a2_u209b___00__closed__1));
v___x_2873_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandEntails___closed__0));
lean_inc(v___x_2871_);
v___x_2874_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2874_, 0, v___x_2871_);
lean_ctor_set(v___x_2874_, 1, v___x_2873_);
v___x_2875_ = l_Lean_Syntax_node2(v___x_2871_, v___x_2872_, v___x_2874_, v_a_2844_);
if (v_isShared_2848_ == 0)
{
lean_ctor_set(v___x_2847_, 0, v___x_2875_);
v___x_2877_ = v___x_2847_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2878_; 
v_reuseFailAlloc_2878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2878_, 0, v___x_2875_);
lean_ctor_set(v_reuseFailAlloc_2878_, 1, v_a_2845_);
v___x_2877_ = v_reuseFailAlloc_2878_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
return v___x_2877_;
}
}
}
}
}
else
{
lean_object* v_a_2880_; lean_object* v_a_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2888_; 
lean_dec(v_a_2840_);
v_a_2880_ = lean_ctor_get(v___x_2843_, 0);
v_a_2881_ = lean_ctor_get(v___x_2843_, 1);
v_isSharedCheck_2888_ = !lean_is_exclusive(v___x_2843_);
if (v_isSharedCheck_2888_ == 0)
{
v___x_2883_ = v___x_2843_;
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_a_2881_);
lean_inc(v_a_2880_);
lean_dec(v___x_2843_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2888_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2886_; 
if (v_isShared_2884_ == 0)
{
v___x_2886_ = v___x_2883_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_a_2880_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v_a_2881_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
}
}
else
{
lean_object* v_a_2889_; lean_object* v_a_2890_; lean_object* v___x_2892_; uint8_t v_isShared_2893_; uint8_t v_isSharedCheck_2897_; 
lean_dec(v___x_2832_);
v_a_2889_ = lean_ctor_get(v___x_2839_, 0);
v_a_2890_ = lean_ctor_get(v___x_2839_, 1);
v_isSharedCheck_2897_ = !lean_is_exclusive(v___x_2839_);
if (v_isSharedCheck_2897_ == 0)
{
v___x_2892_ = v___x_2839_;
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
else
{
lean_inc(v_a_2890_);
lean_inc(v_a_2889_);
lean_dec(v___x_2839_);
v___x_2892_ = lean_box(0);
v_isShared_2893_ = v_isSharedCheck_2897_;
goto v_resetjp_2891_;
}
v_resetjp_2891_:
{
lean_object* v___x_2895_; 
if (v_isShared_2893_ == 0)
{
v___x_2895_ = v___x_2892_;
goto v_reusejp_2894_;
}
else
{
lean_object* v_reuseFailAlloc_2896_; 
v_reuseFailAlloc_2896_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2896_, 0, v_a_2889_);
lean_ctor_set(v_reuseFailAlloc_2896_, 1, v_a_2890_);
v___x_2895_ = v_reuseFailAlloc_2896_;
goto v_reusejp_2894_;
}
v_reusejp_2894_:
{
return v___x_2895_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandEntails___boxed(lean_object* v_x_2898_, lean_object* v_a_2899_, lean_object* v_a_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Std_Do_SPred_Notation_unexpandEntails(v_x_2898_, v_a_2899_, v_a_2900_);
lean_dec(v_a_2899_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandBientails(lean_object* v_x_2903_, lean_object* v_a_2904_, lean_object* v_a_2905_){
_start:
{
lean_object* v___x_2906_; uint8_t v___x_2907_; 
v___x_2906_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2903_);
v___x_2907_ = l_Lean_Syntax_isOfKind(v_x_2903_, v___x_2906_);
if (v___x_2907_ == 0)
{
lean_object* v___x_2908_; lean_object* v___x_2909_; 
lean_dec(v_x_2903_);
v___x_2908_ = lean_box(0);
v___x_2909_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2908_);
lean_ctor_set(v___x_2909_, 1, v_a_2905_);
return v___x_2909_;
}
else
{
lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; uint8_t v___x_2913_; 
v___x_2910_ = lean_unsigned_to_nat(1u);
v___x_2911_ = l_Lean_Syntax_getArg(v_x_2903_, v___x_2910_);
lean_dec(v_x_2903_);
v___x_2912_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2911_);
v___x_2913_ = l_Lean_Syntax_matchesNull(v___x_2911_, v___x_2912_);
if (v___x_2913_ == 0)
{
lean_object* v___x_2914_; lean_object* v___x_2915_; 
lean_dec(v___x_2911_);
v___x_2914_ = lean_box(0);
v___x_2915_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2915_, 0, v___x_2914_);
lean_ctor_set(v___x_2915_, 1, v_a_2905_);
return v___x_2915_;
}
else
{
lean_object* v___x_2916_; lean_object* v_P_2917_; lean_object* v___x_2918_; 
v___x_2916_ = lean_unsigned_to_nat(0u);
v_P_2917_ = l_Lean_Syntax_getArg(v___x_2911_, v___x_2916_);
v___x_2918_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2917_, v_a_2904_, v_a_2905_);
if (lean_obj_tag(v___x_2918_) == 0)
{
lean_object* v_a_2919_; lean_object* v_a_2920_; lean_object* v_Q_2921_; lean_object* v___x_2922_; 
v_a_2919_ = lean_ctor_get(v___x_2918_, 0);
lean_inc(v_a_2919_);
v_a_2920_ = lean_ctor_get(v___x_2918_, 1);
lean_inc(v_a_2920_);
lean_dec_ref_known(v___x_2918_, 2);
v_Q_2921_ = l_Lean_Syntax_getArg(v___x_2911_, v___x_2910_);
lean_dec(v___x_2911_);
v___x_2922_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_2921_, v_a_2904_, v_a_2920_);
if (lean_obj_tag(v___x_2922_) == 0)
{
lean_object* v_a_2923_; lean_object* v_a_2924_; lean_object* v___x_2926_; uint8_t v_isShared_2927_; uint8_t v_isSharedCheck_2937_; 
v_a_2923_ = lean_ctor_get(v___x_2922_, 0);
v_a_2924_ = lean_ctor_get(v___x_2922_, 1);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2926_ = v___x_2922_;
v_isShared_2927_ = v_isSharedCheck_2937_;
goto v_resetjp_2925_;
}
else
{
lean_inc(v_a_2924_);
lean_inc(v_a_2923_);
lean_dec(v___x_2922_);
v___x_2926_ = lean_box(0);
v_isShared_2927_ = v_isSharedCheck_2937_;
goto v_resetjp_2925_;
}
v_resetjp_2925_:
{
uint8_t v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2935_; 
v___x_2928_ = 0;
v___x_2929_ = l_Lean_SourceInfo_fromRef(v_a_2904_, v___x_2928_);
v___x_2930_ = ((lean_object*)(l_Std_Do_term___u22a3_u22a2_u209b___00__closed__1));
v___x_2931_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandBientails___closed__0));
lean_inc(v___x_2929_);
v___x_2932_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2929_);
lean_ctor_set(v___x_2932_, 1, v___x_2931_);
v___x_2933_ = l_Lean_Syntax_node3(v___x_2929_, v___x_2930_, v_a_2919_, v___x_2932_, v_a_2923_);
if (v_isShared_2927_ == 0)
{
lean_ctor_set(v___x_2926_, 0, v___x_2933_);
v___x_2935_ = v___x_2926_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v___x_2933_);
lean_ctor_set(v_reuseFailAlloc_2936_, 1, v_a_2924_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
}
}
}
else
{
lean_object* v_a_2938_; lean_object* v_a_2939_; lean_object* v___x_2941_; uint8_t v_isShared_2942_; uint8_t v_isSharedCheck_2946_; 
lean_dec(v_a_2919_);
v_a_2938_ = lean_ctor_get(v___x_2922_, 0);
v_a_2939_ = lean_ctor_get(v___x_2922_, 1);
v_isSharedCheck_2946_ = !lean_is_exclusive(v___x_2922_);
if (v_isSharedCheck_2946_ == 0)
{
v___x_2941_ = v___x_2922_;
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
else
{
lean_inc(v_a_2939_);
lean_inc(v_a_2938_);
lean_dec(v___x_2922_);
v___x_2941_ = lean_box(0);
v_isShared_2942_ = v_isSharedCheck_2946_;
goto v_resetjp_2940_;
}
v_resetjp_2940_:
{
lean_object* v___x_2944_; 
if (v_isShared_2942_ == 0)
{
v___x_2944_ = v___x_2941_;
goto v_reusejp_2943_;
}
else
{
lean_object* v_reuseFailAlloc_2945_; 
v_reuseFailAlloc_2945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2945_, 0, v_a_2938_);
lean_ctor_set(v_reuseFailAlloc_2945_, 1, v_a_2939_);
v___x_2944_ = v_reuseFailAlloc_2945_;
goto v_reusejp_2943_;
}
v_reusejp_2943_:
{
return v___x_2944_;
}
}
}
}
else
{
lean_object* v_a_2947_; lean_object* v_a_2948_; lean_object* v___x_2950_; uint8_t v_isShared_2951_; uint8_t v_isSharedCheck_2955_; 
lean_dec(v___x_2911_);
v_a_2947_ = lean_ctor_get(v___x_2918_, 0);
v_a_2948_ = lean_ctor_get(v___x_2918_, 1);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2918_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2950_ = v___x_2918_;
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
else
{
lean_inc(v_a_2948_);
lean_inc(v_a_2947_);
lean_dec(v___x_2918_);
v___x_2950_ = lean_box(0);
v_isShared_2951_ = v_isSharedCheck_2955_;
goto v_resetjp_2949_;
}
v_resetjp_2949_:
{
lean_object* v___x_2953_; 
if (v_isShared_2951_ == 0)
{
v___x_2953_ = v___x_2950_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v_a_2947_);
lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_a_2948_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandBientails___boxed(lean_object* v_x_2956_, lean_object* v_a_2957_, lean_object* v_a_2958_){
_start:
{
lean_object* v_res_2959_; 
v_res_2959_ = l_Std_Do_SPred_Notation_unexpandBientails(v_x_2956_, v_a_2957_, v_a_2958_);
lean_dec(v_a_2957_);
return v_res_2959_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandAnd(lean_object* v_x_2961_, lean_object* v_a_2962_, lean_object* v_a_2963_){
_start:
{
lean_object* v___x_2964_; uint8_t v___x_2965_; 
v___x_2964_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2961_);
v___x_2965_ = l_Lean_Syntax_isOfKind(v_x_2961_, v___x_2964_);
if (v___x_2965_ == 0)
{
lean_object* v___x_2966_; lean_object* v___x_2967_; 
lean_dec(v_x_2961_);
v___x_2966_ = lean_box(0);
v___x_2967_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2967_, 0, v___x_2966_);
lean_ctor_set(v___x_2967_, 1, v_a_2963_);
return v___x_2967_;
}
else
{
lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; uint8_t v___x_2971_; 
v___x_2968_ = lean_unsigned_to_nat(1u);
v___x_2969_ = l_Lean_Syntax_getArg(v_x_2961_, v___x_2968_);
lean_dec(v_x_2961_);
v___x_2970_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2969_);
v___x_2971_ = l_Lean_Syntax_matchesNull(v___x_2969_, v___x_2970_);
if (v___x_2971_ == 0)
{
lean_object* v___x_2972_; lean_object* v___x_2973_; 
lean_dec(v___x_2969_);
v___x_2972_ = lean_box(0);
v___x_2973_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2973_, 0, v___x_2972_);
lean_ctor_set(v___x_2973_, 1, v_a_2963_);
return v___x_2973_;
}
else
{
lean_object* v___x_2974_; lean_object* v_P_2975_; lean_object* v___x_2976_; 
v___x_2974_ = lean_unsigned_to_nat(0u);
v_P_2975_ = l_Lean_Syntax_getArg(v___x_2969_, v___x_2974_);
v___x_2976_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2975_, v_a_2962_, v_a_2963_);
if (lean_obj_tag(v___x_2976_) == 0)
{
lean_object* v_a_2977_; lean_object* v_a_2978_; lean_object* v_Q_2979_; lean_object* v___x_2980_; 
v_a_2977_ = lean_ctor_get(v___x_2976_, 0);
lean_inc(v_a_2977_);
v_a_2978_ = lean_ctor_get(v___x_2976_, 1);
lean_inc(v_a_2978_);
lean_dec_ref_known(v___x_2976_, 2);
v_Q_2979_ = l_Lean_Syntax_getArg(v___x_2969_, v___x_2968_);
lean_dec(v___x_2969_);
v___x_2980_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_2979_, v_a_2962_, v_a_2978_);
if (lean_obj_tag(v___x_2980_) == 0)
{
lean_object* v_a_2981_; lean_object* v_a_2982_; lean_object* v___x_2984_; uint8_t v_isShared_2985_; uint8_t v_isSharedCheck_3001_; 
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
v_a_2982_ = lean_ctor_get(v___x_2980_, 1);
v_isSharedCheck_3001_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3001_ == 0)
{
v___x_2984_ = v___x_2980_;
v_isShared_2985_ = v_isSharedCheck_3001_;
goto v_resetjp_2983_;
}
else
{
lean_inc(v_a_2982_);
lean_inc(v_a_2981_);
lean_dec(v___x_2980_);
v___x_2984_ = lean_box(0);
v_isShared_2985_ = v_isSharedCheck_3001_;
goto v_resetjp_2983_;
}
v_resetjp_2983_:
{
uint8_t v___x_2986_; lean_object* v___x_2987_; lean_object* v___x_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; lean_object* v___x_2999_; 
v___x_2986_ = 0;
v___x_2987_ = l_Lean_SourceInfo_fromRef(v_a_2962_, v___x_2986_);
v___x_2988_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2989_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2987_, 4);
v___x_2990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2990_, 0, v___x_2987_);
lean_ctor_set(v___x_2990_, 1, v___x_2989_);
v___x_2991_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__1));
v___x_2992_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandAnd___closed__0));
v___x_2993_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2993_, 0, v___x_2987_);
lean_ctor_set(v___x_2993_, 1, v___x_2992_);
v___x_2994_ = l_Lean_Syntax_node3(v___x_2987_, v___x_2991_, v_a_2977_, v___x_2993_, v_a_2981_);
v___x_2995_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2996_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2996_, 0, v___x_2987_);
lean_ctor_set(v___x_2996_, 1, v___x_2995_);
v___x_2997_ = l_Lean_Syntax_node3(v___x_2987_, v___x_2988_, v___x_2990_, v___x_2994_, v___x_2996_);
if (v_isShared_2985_ == 0)
{
lean_ctor_set(v___x_2984_, 0, v___x_2997_);
v___x_2999_ = v___x_2984_;
goto v_reusejp_2998_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v___x_2997_);
lean_ctor_set(v_reuseFailAlloc_3000_, 1, v_a_2982_);
v___x_2999_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2998_;
}
v_reusejp_2998_:
{
return v___x_2999_;
}
}
}
else
{
lean_object* v_a_3002_; lean_object* v_a_3003_; lean_object* v___x_3005_; uint8_t v_isShared_3006_; uint8_t v_isSharedCheck_3010_; 
lean_dec(v_a_2977_);
v_a_3002_ = lean_ctor_get(v___x_2980_, 0);
v_a_3003_ = lean_ctor_get(v___x_2980_, 1);
v_isSharedCheck_3010_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_3010_ == 0)
{
v___x_3005_ = v___x_2980_;
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
else
{
lean_inc(v_a_3003_);
lean_inc(v_a_3002_);
lean_dec(v___x_2980_);
v___x_3005_ = lean_box(0);
v_isShared_3006_ = v_isSharedCheck_3010_;
goto v_resetjp_3004_;
}
v_resetjp_3004_:
{
lean_object* v___x_3008_; 
if (v_isShared_3006_ == 0)
{
v___x_3008_ = v___x_3005_;
goto v_reusejp_3007_;
}
else
{
lean_object* v_reuseFailAlloc_3009_; 
v_reuseFailAlloc_3009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3009_, 0, v_a_3002_);
lean_ctor_set(v_reuseFailAlloc_3009_, 1, v_a_3003_);
v___x_3008_ = v_reuseFailAlloc_3009_;
goto v_reusejp_3007_;
}
v_reusejp_3007_:
{
return v___x_3008_;
}
}
}
}
else
{
lean_object* v_a_3011_; lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3019_; 
lean_dec(v___x_2969_);
v_a_3011_ = lean_ctor_get(v___x_2976_, 0);
v_a_3012_ = lean_ctor_get(v___x_2976_, 1);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_2976_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3014_ = v___x_2976_;
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_inc(v_a_3011_);
lean_dec(v___x_2976_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3017_; 
if (v_isShared_3015_ == 0)
{
v___x_3017_ = v___x_3014_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_a_3011_);
lean_ctor_set(v_reuseFailAlloc_3018_, 1, v_a_3012_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandAnd___boxed(lean_object* v_x_3020_, lean_object* v_a_3021_, lean_object* v_a_3022_){
_start:
{
lean_object* v_res_3023_; 
v_res_3023_ = l_Std_Do_SPred_Notation_unexpandAnd(v_x_3020_, v_a_3021_, v_a_3022_);
lean_dec(v_a_3021_);
return v_res_3023_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandOr(lean_object* v_x_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_){
_start:
{
lean_object* v___x_3028_; uint8_t v___x_3029_; 
v___x_3028_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_3025_);
v___x_3029_ = l_Lean_Syntax_isOfKind(v_x_3025_, v___x_3028_);
if (v___x_3029_ == 0)
{
lean_object* v___x_3030_; lean_object* v___x_3031_; 
lean_dec(v_x_3025_);
v___x_3030_ = lean_box(0);
v___x_3031_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3031_, 0, v___x_3030_);
lean_ctor_set(v___x_3031_, 1, v_a_3027_);
return v___x_3031_;
}
else
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; uint8_t v___x_3035_; 
v___x_3032_ = lean_unsigned_to_nat(1u);
v___x_3033_ = l_Lean_Syntax_getArg(v_x_3025_, v___x_3032_);
lean_dec(v_x_3025_);
v___x_3034_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3033_);
v___x_3035_ = l_Lean_Syntax_matchesNull(v___x_3033_, v___x_3034_);
if (v___x_3035_ == 0)
{
lean_object* v___x_3036_; lean_object* v___x_3037_; 
lean_dec(v___x_3033_);
v___x_3036_ = lean_box(0);
v___x_3037_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3036_);
lean_ctor_set(v___x_3037_, 1, v_a_3027_);
return v___x_3037_;
}
else
{
lean_object* v___x_3038_; lean_object* v_P_3039_; lean_object* v___x_3040_; 
v___x_3038_ = lean_unsigned_to_nat(0u);
v_P_3039_ = l_Lean_Syntax_getArg(v___x_3033_, v___x_3038_);
v___x_3040_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_3039_, v_a_3026_, v_a_3027_);
if (lean_obj_tag(v___x_3040_) == 0)
{
lean_object* v_a_3041_; lean_object* v_a_3042_; lean_object* v_Q_3043_; lean_object* v___x_3044_; 
v_a_3041_ = lean_ctor_get(v___x_3040_, 0);
lean_inc(v_a_3041_);
v_a_3042_ = lean_ctor_get(v___x_3040_, 1);
lean_inc(v_a_3042_);
lean_dec_ref_known(v___x_3040_, 2);
v_Q_3043_ = l_Lean_Syntax_getArg(v___x_3033_, v___x_3032_);
lean_dec(v___x_3033_);
v___x_3044_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_3043_, v_a_3026_, v_a_3042_);
if (lean_obj_tag(v___x_3044_) == 0)
{
lean_object* v_a_3045_; lean_object* v_a_3046_; lean_object* v___x_3048_; uint8_t v_isShared_3049_; uint8_t v_isSharedCheck_3065_; 
v_a_3045_ = lean_ctor_get(v___x_3044_, 0);
v_a_3046_ = lean_ctor_get(v___x_3044_, 1);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_3048_ = v___x_3044_;
v_isShared_3049_ = v_isSharedCheck_3065_;
goto v_resetjp_3047_;
}
else
{
lean_inc(v_a_3046_);
lean_inc(v_a_3045_);
lean_dec(v___x_3044_);
v___x_3048_ = lean_box(0);
v_isShared_3049_ = v_isSharedCheck_3065_;
goto v_resetjp_3047_;
}
v_resetjp_3047_:
{
uint8_t v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; lean_object* v___x_3063_; 
v___x_3050_ = 0;
v___x_3051_ = l_Lean_SourceInfo_fromRef(v_a_3026_, v___x_3050_);
v___x_3052_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3053_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3051_, 4);
v___x_3054_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3051_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___x_3055_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__3));
v___x_3056_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandOr___closed__0));
v___x_3057_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3057_, 0, v___x_3051_);
lean_ctor_set(v___x_3057_, 1, v___x_3056_);
v___x_3058_ = l_Lean_Syntax_node3(v___x_3051_, v___x_3055_, v_a_3041_, v___x_3057_, v_a_3045_);
v___x_3059_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3060_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3060_, 0, v___x_3051_);
lean_ctor_set(v___x_3060_, 1, v___x_3059_);
v___x_3061_ = l_Lean_Syntax_node3(v___x_3051_, v___x_3052_, v___x_3054_, v___x_3058_, v___x_3060_);
if (v_isShared_3049_ == 0)
{
lean_ctor_set(v___x_3048_, 0, v___x_3061_);
v___x_3063_ = v___x_3048_;
goto v_reusejp_3062_;
}
else
{
lean_object* v_reuseFailAlloc_3064_; 
v_reuseFailAlloc_3064_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3064_, 0, v___x_3061_);
lean_ctor_set(v_reuseFailAlloc_3064_, 1, v_a_3046_);
v___x_3063_ = v_reuseFailAlloc_3064_;
goto v_reusejp_3062_;
}
v_reusejp_3062_:
{
return v___x_3063_;
}
}
}
else
{
lean_object* v_a_3066_; lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec(v_a_3041_);
v_a_3066_ = lean_ctor_get(v___x_3044_, 0);
v_a_3067_ = lean_ctor_get(v___x_3044_, 1);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_3044_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_3044_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_inc(v_a_3066_);
lean_dec(v___x_3044_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3066_);
lean_ctor_set(v_reuseFailAlloc_3073_, 1, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
else
{
lean_object* v_a_3075_; lean_object* v_a_3076_; lean_object* v___x_3078_; uint8_t v_isShared_3079_; uint8_t v_isSharedCheck_3083_; 
lean_dec(v___x_3033_);
v_a_3075_ = lean_ctor_get(v___x_3040_, 0);
v_a_3076_ = lean_ctor_get(v___x_3040_, 1);
v_isSharedCheck_3083_ = !lean_is_exclusive(v___x_3040_);
if (v_isSharedCheck_3083_ == 0)
{
v___x_3078_ = v___x_3040_;
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
else
{
lean_inc(v_a_3076_);
lean_inc(v_a_3075_);
lean_dec(v___x_3040_);
v___x_3078_ = lean_box(0);
v_isShared_3079_ = v_isSharedCheck_3083_;
goto v_resetjp_3077_;
}
v_resetjp_3077_:
{
lean_object* v___x_3081_; 
if (v_isShared_3079_ == 0)
{
v___x_3081_ = v___x_3078_;
goto v_reusejp_3080_;
}
else
{
lean_object* v_reuseFailAlloc_3082_; 
v_reuseFailAlloc_3082_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3082_, 0, v_a_3075_);
lean_ctor_set(v_reuseFailAlloc_3082_, 1, v_a_3076_);
v___x_3081_ = v_reuseFailAlloc_3082_;
goto v_reusejp_3080_;
}
v_reusejp_3080_:
{
return v___x_3081_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandOr___boxed(lean_object* v_x_3084_, lean_object* v_a_3085_, lean_object* v_a_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = l_Std_Do_SPred_Notation_unexpandOr(v_x_3084_, v_a_3085_, v_a_3086_);
lean_dec(v_a_3085_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandNot(lean_object* v_x_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_){
_start:
{
lean_object* v___x_3092_; uint8_t v___x_3093_; 
v___x_3092_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_3089_);
v___x_3093_ = l_Lean_Syntax_isOfKind(v_x_3089_, v___x_3092_);
if (v___x_3093_ == 0)
{
lean_object* v___x_3094_; lean_object* v___x_3095_; 
lean_dec(v_x_3089_);
v___x_3094_ = lean_box(0);
v___x_3095_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
lean_ctor_set(v___x_3095_, 1, v_a_3091_);
return v___x_3095_;
}
else
{
lean_object* v___x_3096_; lean_object* v___x_3097_; uint8_t v___x_3098_; 
v___x_3096_ = lean_unsigned_to_nat(1u);
v___x_3097_ = l_Lean_Syntax_getArg(v_x_3089_, v___x_3096_);
lean_dec(v_x_3089_);
lean_inc(v___x_3097_);
v___x_3098_ = l_Lean_Syntax_matchesNull(v___x_3097_, v___x_3096_);
if (v___x_3098_ == 0)
{
lean_object* v___x_3099_; lean_object* v___x_3100_; 
lean_dec(v___x_3097_);
v___x_3099_ = lean_box(0);
v___x_3100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3100_, 0, v___x_3099_);
lean_ctor_set(v___x_3100_, 1, v_a_3091_);
return v___x_3100_;
}
else
{
lean_object* v___x_3101_; lean_object* v_P_3102_; lean_object* v___x_3103_; 
v___x_3101_ = lean_unsigned_to_nat(0u);
v_P_3102_ = l_Lean_Syntax_getArg(v___x_3097_, v___x_3101_);
lean_dec(v___x_3097_);
v___x_3103_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_3102_, v_a_3090_, v_a_3091_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3124_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
v_a_3105_ = lean_ctor_get(v___x_3103_, 1);
v_isSharedCheck_3124_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3124_ == 0)
{
v___x_3107_ = v___x_3103_;
v_isShared_3108_ = v_isSharedCheck_3124_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_inc(v_a_3104_);
lean_dec(v___x_3103_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3124_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
uint8_t v___x_3109_; lean_object* v___x_3110_; lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; lean_object* v___x_3122_; 
v___x_3109_ = 0;
v___x_3110_ = l_Lean_SourceInfo_fromRef(v_a_3090_, v___x_3109_);
v___x_3111_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3112_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3110_, 4);
v___x_3113_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3113_, 0, v___x_3110_);
lean_ctor_set(v___x_3113_, 1, v___x_3112_);
v___x_3114_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__5));
v___x_3115_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandNot___closed__0));
v___x_3116_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3110_);
lean_ctor_set(v___x_3116_, 1, v___x_3115_);
v___x_3117_ = l_Lean_Syntax_node2(v___x_3110_, v___x_3114_, v___x_3116_, v_a_3104_);
v___x_3118_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3119_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3110_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
v___x_3120_ = l_Lean_Syntax_node3(v___x_3110_, v___x_3111_, v___x_3113_, v___x_3117_, v___x_3119_);
if (v_isShared_3108_ == 0)
{
lean_ctor_set(v___x_3107_, 0, v___x_3120_);
v___x_3122_ = v___x_3107_;
goto v_reusejp_3121_;
}
else
{
lean_object* v_reuseFailAlloc_3123_; 
v_reuseFailAlloc_3123_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3123_, 0, v___x_3120_);
lean_ctor_set(v_reuseFailAlloc_3123_, 1, v_a_3105_);
v___x_3122_ = v_reuseFailAlloc_3123_;
goto v_reusejp_3121_;
}
v_reusejp_3121_:
{
return v___x_3122_;
}
}
}
else
{
lean_object* v_a_3125_; lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
v_a_3125_ = lean_ctor_get(v___x_3103_, 0);
v_a_3126_ = lean_ctor_get(v___x_3103_, 1);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_3103_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_inc(v_a_3125_);
lean_dec(v___x_3103_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3125_);
lean_ctor_set(v_reuseFailAlloc_3132_, 1, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandNot___boxed(lean_object* v_x_3134_, lean_object* v_a_3135_, lean_object* v_a_3136_){
_start:
{
lean_object* v_res_3137_; 
v_res_3137_ = l_Std_Do_SPred_Notation_unexpandNot(v_x_3134_, v_a_3135_, v_a_3136_);
lean_dec(v_a_3135_);
return v_res_3137_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandImp(lean_object* v_x_3139_, lean_object* v_a_3140_, lean_object* v_a_3141_){
_start:
{
lean_object* v___x_3142_; uint8_t v___x_3143_; 
v___x_3142_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_3139_);
v___x_3143_ = l_Lean_Syntax_isOfKind(v_x_3139_, v___x_3142_);
if (v___x_3143_ == 0)
{
lean_object* v___x_3144_; lean_object* v___x_3145_; 
lean_dec(v_x_3139_);
v___x_3144_ = lean_box(0);
v___x_3145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3145_, 0, v___x_3144_);
lean_ctor_set(v___x_3145_, 1, v_a_3141_);
return v___x_3145_;
}
else
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; uint8_t v___x_3149_; 
v___x_3146_ = lean_unsigned_to_nat(1u);
v___x_3147_ = l_Lean_Syntax_getArg(v_x_3139_, v___x_3146_);
lean_dec(v_x_3139_);
v___x_3148_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_3147_);
v___x_3149_ = l_Lean_Syntax_matchesNull(v___x_3147_, v___x_3148_);
if (v___x_3149_ == 0)
{
lean_object* v___x_3150_; lean_object* v___x_3151_; 
lean_dec(v___x_3147_);
v___x_3150_ = lean_box(0);
v___x_3151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3151_, 0, v___x_3150_);
lean_ctor_set(v___x_3151_, 1, v_a_3141_);
return v___x_3151_;
}
else
{
lean_object* v___x_3152_; lean_object* v_P_3153_; lean_object* v___x_3154_; 
v___x_3152_ = lean_unsigned_to_nat(0u);
v_P_3153_ = l_Lean_Syntax_getArg(v___x_3147_, v___x_3152_);
v___x_3154_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_3153_, v_a_3140_, v_a_3141_);
if (lean_obj_tag(v___x_3154_) == 0)
{
lean_object* v_a_3155_; lean_object* v_a_3156_; lean_object* v_Q_3157_; lean_object* v___x_3158_; 
v_a_3155_ = lean_ctor_get(v___x_3154_, 0);
lean_inc(v_a_3155_);
v_a_3156_ = lean_ctor_get(v___x_3154_, 1);
lean_inc(v_a_3156_);
lean_dec_ref_known(v___x_3154_, 2);
v_Q_3157_ = l_Lean_Syntax_getArg(v___x_3147_, v___x_3146_);
lean_dec(v___x_3147_);
v___x_3158_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_3157_, v_a_3140_, v_a_3156_);
if (lean_obj_tag(v___x_3158_) == 0)
{
lean_object* v_a_3159_; lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3179_; 
v_a_3159_ = lean_ctor_get(v___x_3158_, 0);
v_a_3160_ = lean_ctor_get(v___x_3158_, 1);
v_isSharedCheck_3179_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3179_ == 0)
{
v___x_3162_ = v___x_3158_;
v_isShared_3163_ = v_isSharedCheck_3179_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_inc(v_a_3159_);
lean_dec(v___x_3158_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3179_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
uint8_t v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3177_; 
v___x_3164_ = 0;
v___x_3165_ = l_Lean_SourceInfo_fromRef(v_a_3140_, v___x_3164_);
v___x_3166_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3167_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3165_, 4);
v___x_3168_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3168_, 0, v___x_3165_);
lean_ctor_set(v___x_3168_, 1, v___x_3167_);
v___x_3169_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__7));
v___x_3170_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandImp___closed__0));
v___x_3171_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3165_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
v___x_3172_ = l_Lean_Syntax_node3(v___x_3165_, v___x_3169_, v_a_3155_, v___x_3171_, v_a_3159_);
v___x_3173_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3174_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3174_, 0, v___x_3165_);
lean_ctor_set(v___x_3174_, 1, v___x_3173_);
v___x_3175_ = l_Lean_Syntax_node3(v___x_3165_, v___x_3166_, v___x_3168_, v___x_3172_, v___x_3174_);
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 0, v___x_3175_);
v___x_3177_ = v___x_3162_;
goto v_reusejp_3176_;
}
else
{
lean_object* v_reuseFailAlloc_3178_; 
v_reuseFailAlloc_3178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3178_, 0, v___x_3175_);
lean_ctor_set(v_reuseFailAlloc_3178_, 1, v_a_3160_);
v___x_3177_ = v_reuseFailAlloc_3178_;
goto v_reusejp_3176_;
}
v_reusejp_3176_:
{
return v___x_3177_;
}
}
}
else
{
lean_object* v_a_3180_; lean_object* v_a_3181_; lean_object* v___x_3183_; uint8_t v_isShared_3184_; uint8_t v_isSharedCheck_3188_; 
lean_dec(v_a_3155_);
v_a_3180_ = lean_ctor_get(v___x_3158_, 0);
v_a_3181_ = lean_ctor_get(v___x_3158_, 1);
v_isSharedCheck_3188_ = !lean_is_exclusive(v___x_3158_);
if (v_isSharedCheck_3188_ == 0)
{
v___x_3183_ = v___x_3158_;
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
else
{
lean_inc(v_a_3181_);
lean_inc(v_a_3180_);
lean_dec(v___x_3158_);
v___x_3183_ = lean_box(0);
v_isShared_3184_ = v_isSharedCheck_3188_;
goto v_resetjp_3182_;
}
v_resetjp_3182_:
{
lean_object* v___x_3186_; 
if (v_isShared_3184_ == 0)
{
v___x_3186_ = v___x_3183_;
goto v_reusejp_3185_;
}
else
{
lean_object* v_reuseFailAlloc_3187_; 
v_reuseFailAlloc_3187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3187_, 0, v_a_3180_);
lean_ctor_set(v_reuseFailAlloc_3187_, 1, v_a_3181_);
v___x_3186_ = v_reuseFailAlloc_3187_;
goto v_reusejp_3185_;
}
v_reusejp_3185_:
{
return v___x_3186_;
}
}
}
}
else
{
lean_object* v_a_3189_; lean_object* v_a_3190_; lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3197_; 
lean_dec(v___x_3147_);
v_a_3189_ = lean_ctor_get(v___x_3154_, 0);
v_a_3190_ = lean_ctor_get(v___x_3154_, 1);
v_isSharedCheck_3197_ = !lean_is_exclusive(v___x_3154_);
if (v_isSharedCheck_3197_ == 0)
{
v___x_3192_ = v___x_3154_;
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
else
{
lean_inc(v_a_3190_);
lean_inc(v_a_3189_);
lean_dec(v___x_3154_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3197_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3195_; 
if (v_isShared_3193_ == 0)
{
v___x_3195_ = v___x_3192_;
goto v_reusejp_3194_;
}
else
{
lean_object* v_reuseFailAlloc_3196_; 
v_reuseFailAlloc_3196_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3196_, 0, v_a_3189_);
lean_ctor_set(v_reuseFailAlloc_3196_, 1, v_a_3190_);
v___x_3195_ = v_reuseFailAlloc_3196_;
goto v_reusejp_3194_;
}
v_reusejp_3194_:
{
return v___x_3195_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandImp___boxed(lean_object* v_x_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l_Std_Do_SPred_Notation_unexpandImp(v_x_3198_, v_a_3199_, v_a_3200_);
lean_dec(v_a_3199_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__1(size_t v_sz_3202_, size_t v_i_3203_, lean_object* v_bs_3204_){
_start:
{
uint8_t v___x_3205_; 
v___x_3205_ = lean_usize_dec_lt(v_i_3203_, v_sz_3202_);
if (v___x_3205_ == 0)
{
return v_bs_3204_;
}
else
{
lean_object* v_v_3206_; lean_object* v___x_3207_; lean_object* v_bs_x27_3208_; size_t v___x_3209_; size_t v___x_3210_; lean_object* v___x_3211_; 
v_v_3206_ = lean_array_uget(v_bs_3204_, v_i_3203_);
v___x_3207_ = lean_unsigned_to_nat(0u);
v_bs_x27_3208_ = lean_array_uset(v_bs_3204_, v_i_3203_, v___x_3207_);
v___x_3209_ = ((size_t)1ULL);
v___x_3210_ = lean_usize_add(v_i_3203_, v___x_3209_);
v___x_3211_ = lean_array_uset(v_bs_x27_3208_, v_i_3203_, v_v_3206_);
v_i_3203_ = v___x_3210_;
v_bs_3204_ = v___x_3211_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__1___boxed(lean_object* v_sz_3213_, lean_object* v_i_3214_, lean_object* v_bs_3215_){
_start:
{
size_t v_sz_boxed_3216_; size_t v_i_boxed_3217_; lean_object* v_res_3218_; 
v_sz_boxed_3216_ = lean_unbox_usize(v_sz_3213_);
lean_dec(v_sz_3213_);
v_i_boxed_3217_ = lean_unbox_usize(v_i_3214_);
lean_dec(v_i_3214_);
v_res_3218_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__1(v_sz_boxed_3216_, v_i_boxed_3217_, v_bs_3215_);
return v_res_3218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__0(size_t v_sz_3219_, size_t v_i_3220_, lean_object* v_bs_3221_){
_start:
{
uint8_t v___x_3222_; 
v___x_3222_ = lean_usize_dec_lt(v_i_3220_, v_sz_3219_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; 
v___x_3223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3223_, 0, v_bs_3221_);
return v___x_3223_;
}
else
{
lean_object* v_v_3224_; lean_object* v___x_3225_; uint8_t v___x_3226_; 
v_v_3224_ = lean_array_uget(v_bs_3221_, v_i_3220_);
v___x_3225_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_v_3224_);
v___x_3226_ = l_Lean_Syntax_isOfKind(v_v_3224_, v___x_3225_);
if (v___x_3226_ == 0)
{
lean_object* v___x_3227_; 
lean_dec(v_v_3224_);
lean_dec_ref(v_bs_3221_);
v___x_3227_ = lean_box(0);
return v___x_3227_;
}
else
{
lean_object* v___x_3228_; lean_object* v_bs_x27_3229_; size_t v___x_3230_; size_t v___x_3231_; lean_object* v___x_3232_; 
v___x_3228_ = lean_unsigned_to_nat(0u);
v_bs_x27_3229_ = lean_array_uset(v_bs_3221_, v_i_3220_, v___x_3228_);
v___x_3230_ = ((size_t)1ULL);
v___x_3231_ = lean_usize_add(v_i_3220_, v___x_3230_);
v___x_3232_ = lean_array_uset(v_bs_x27_3229_, v_i_3220_, v_v_3224_);
v_i_3220_ = v___x_3231_;
v_bs_3221_ = v___x_3232_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__0___boxed(lean_object* v_sz_3234_, lean_object* v_i_3235_, lean_object* v_bs_3236_){
_start:
{
size_t v_sz_boxed_3237_; size_t v_i_boxed_3238_; lean_object* v_res_3239_; 
v_sz_boxed_3237_ = lean_unbox_usize(v_sz_3234_);
lean_dec(v_sz_3234_);
v_i_boxed_3238_ = lean_unbox_usize(v_i_3235_);
lean_dec(v_i_3235_);
v_res_3239_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__0(v_sz_boxed_3237_, v_i_boxed_3238_, v_bs_3236_);
return v_res_3239_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandForall(lean_object* v_x_3240_, lean_object* v_a_3241_, lean_object* v_a_3242_){
_start:
{
lean_object* v___x_3243_; uint8_t v___x_3244_; 
v___x_3243_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_3240_);
v___x_3244_ = l_Lean_Syntax_isOfKind(v_x_3240_, v___x_3243_);
if (v___x_3244_ == 0)
{
lean_object* v___x_3245_; lean_object* v___x_3246_; 
lean_dec(v_x_3240_);
v___x_3245_ = lean_box(0);
v___x_3246_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3246_, 0, v___x_3245_);
lean_ctor_set(v___x_3246_, 1, v_a_3242_);
return v___x_3246_;
}
else
{
lean_object* v___x_3247_; lean_object* v___x_3248_; uint8_t v___x_3249_; 
v___x_3247_ = lean_unsigned_to_nat(1u);
v___x_3248_ = l_Lean_Syntax_getArg(v_x_3240_, v___x_3247_);
lean_dec(v_x_3240_);
lean_inc(v___x_3248_);
v___x_3249_ = l_Lean_Syntax_matchesNull(v___x_3248_, v___x_3247_);
if (v___x_3249_ == 0)
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
lean_dec(v___x_3248_);
v___x_3250_ = lean_box(0);
v___x_3251_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3251_, 0, v___x_3250_);
lean_ctor_set(v___x_3251_, 1, v_a_3242_);
return v___x_3251_;
}
else
{
lean_object* v___x_3252_; lean_object* v___x_3253_; lean_object* v___x_3254_; uint8_t v___x_3255_; 
v___x_3252_ = lean_unsigned_to_nat(0u);
v___x_3253_ = l_Lean_Syntax_getArg(v___x_3248_, v___x_3252_);
lean_dec(v___x_3248_);
v___x_3254_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
lean_inc(v___x_3253_);
v___x_3255_ = l_Lean_Syntax_isOfKind(v___x_3253_, v___x_3254_);
if (v___x_3255_ == 0)
{
lean_object* v___x_3256_; lean_object* v___x_3257_; 
lean_dec(v___x_3253_);
v___x_3256_ = lean_box(0);
v___x_3257_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3257_, 0, v___x_3256_);
lean_ctor_set(v___x_3257_, 1, v_a_3242_);
return v___x_3257_;
}
else
{
lean_object* v___x_3258_; lean_object* v___x_3259_; uint8_t v___x_3260_; 
v___x_3258_ = l_Lean_Syntax_getArg(v___x_3253_, v___x_3247_);
lean_dec(v___x_3253_);
v___x_3259_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
lean_inc(v___x_3258_);
v___x_3260_ = l_Lean_Syntax_isOfKind(v___x_3258_, v___x_3259_);
if (v___x_3260_ == 0)
{
lean_object* v___x_3261_; lean_object* v___x_3262_; 
lean_dec(v___x_3258_);
v___x_3261_ = lean_box(0);
v___x_3262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3262_, 0, v___x_3261_);
lean_ctor_set(v___x_3262_, 1, v_a_3242_);
return v___x_3262_;
}
else
{
lean_object* v___x_3263_; uint8_t v___x_3264_; 
v___x_3263_ = l_Lean_Syntax_getArg(v___x_3258_, v___x_3252_);
lean_inc(v___x_3263_);
v___x_3264_ = l_Lean_Syntax_matchesNull(v___x_3263_, v___x_3247_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3265_; lean_object* v___x_3266_; 
lean_dec(v___x_3263_);
lean_dec(v___x_3258_);
v___x_3265_ = lean_box(0);
v___x_3266_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3266_, 0, v___x_3265_);
lean_ctor_set(v___x_3266_, 1, v_a_3242_);
return v___x_3266_;
}
else
{
lean_object* v___x_3267_; lean_object* v___x_3268_; uint8_t v___x_3269_; 
v___x_3267_ = l_Lean_Syntax_getArg(v___x_3263_, v___x_3252_);
lean_dec(v___x_3263_);
v___x_3268_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v___x_3267_);
v___x_3269_ = l_Lean_Syntax_isOfKind(v___x_3267_, v___x_3268_);
if (v___x_3269_ == 0)
{
lean_object* v___x_3270_; lean_object* v___x_3271_; 
lean_dec(v___x_3267_);
lean_dec(v___x_3258_);
v___x_3270_ = lean_box(0);
v___x_3271_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3271_, 0, v___x_3270_);
lean_ctor_set(v___x_3271_, 1, v_a_3242_);
return v___x_3271_;
}
else
{
lean_object* v___x_3272_; uint8_t v___x_3273_; 
v___x_3272_ = l_Lean_Syntax_getArg(v___x_3258_, v___x_3247_);
v___x_3273_ = l_Lean_Syntax_matchesNull(v___x_3272_, v___x_3252_);
if (v___x_3273_ == 0)
{
lean_object* v___x_3274_; lean_object* v___x_3275_; 
lean_dec(v___x_3267_);
lean_dec(v___x_3258_);
v___x_3274_ = lean_box(0);
v___x_3275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3275_, 0, v___x_3274_);
lean_ctor_set(v___x_3275_, 1, v_a_3242_);
return v___x_3275_;
}
else
{
lean_object* v___x_3276_; lean_object* v_00_u03a8_3277_; lean_object* v___x_3278_; uint8_t v___x_3279_; 
v___x_3276_ = lean_unsigned_to_nat(3u);
v_00_u03a8_3277_ = l_Lean_Syntax_getArg(v___x_3258_, v___x_3276_);
lean_dec(v___x_3258_);
v___x_3278_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__13));
lean_inc(v_00_u03a8_3277_);
v___x_3279_ = l_Lean_Syntax_isOfKind(v_00_u03a8_3277_, v___x_3278_);
if (v___x_3279_ == 0)
{
lean_object* v___x_3280_; 
v___x_3280_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3277_, v_a_3241_, v_a_3242_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_a_3281_; lean_object* v_a_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3305_; 
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
v_a_3282_ = lean_ctor_get(v___x_3280_, 1);
v_isSharedCheck_3305_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3305_ == 0)
{
v___x_3284_ = v___x_3280_;
v_isShared_3285_ = v_isSharedCheck_3305_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_a_3282_);
lean_inc(v_a_3281_);
lean_dec(v___x_3280_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3305_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v___x_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3303_; 
v___x_3286_ = l_Lean_SourceInfo_fromRef(v_a_3241_, v___x_3279_);
v___x_3287_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3288_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3286_, 7);
v___x_3289_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3289_, 0, v___x_3286_);
lean_ctor_set(v___x_3289_, 1, v___x_3288_);
v___x_3290_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_3291_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3291_, 0, v___x_3286_);
lean_ctor_set(v___x_3291_, 1, v___x_3290_);
v___x_3292_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3293_ = l_Lean_Syntax_node1(v___x_3286_, v___x_3292_, v___x_3267_);
v___x_3294_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3295_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3295_, 0, v___x_3286_);
lean_ctor_set(v___x_3295_, 1, v___x_3292_);
lean_ctor_set(v___x_3295_, 2, v___x_3294_);
v___x_3296_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3297_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3297_, 0, v___x_3286_);
lean_ctor_set(v___x_3297_, 1, v___x_3296_);
v___x_3298_ = l_Lean_Syntax_node5(v___x_3286_, v___x_3278_, v___x_3291_, v___x_3293_, v___x_3295_, v___x_3297_, v_a_3281_);
v___x_3299_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3300_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3300_, 0, v___x_3286_);
lean_ctor_set(v___x_3300_, 1, v___x_3299_);
v___x_3301_ = l_Lean_Syntax_node3(v___x_3286_, v___x_3287_, v___x_3289_, v___x_3298_, v___x_3300_);
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 0, v___x_3301_);
v___x_3303_ = v___x_3284_;
goto v_reusejp_3302_;
}
else
{
lean_object* v_reuseFailAlloc_3304_; 
v_reuseFailAlloc_3304_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3304_, 0, v___x_3301_);
lean_ctor_set(v_reuseFailAlloc_3304_, 1, v_a_3282_);
v___x_3303_ = v_reuseFailAlloc_3304_;
goto v_reusejp_3302_;
}
v_reusejp_3302_:
{
return v___x_3303_;
}
}
}
else
{
lean_object* v_a_3306_; lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
lean_dec(v___x_3267_);
v_a_3306_ = lean_ctor_get(v___x_3280_, 0);
v_a_3307_ = lean_ctor_get(v___x_3280_, 1);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3309_ = v___x_3280_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_inc(v_a_3306_);
lean_dec(v___x_3280_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3312_; 
if (v_isShared_3310_ == 0)
{
v___x_3312_ = v___x_3309_;
goto v_reusejp_3311_;
}
else
{
lean_object* v_reuseFailAlloc_3313_; 
v_reuseFailAlloc_3313_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3313_, 0, v_a_3306_);
lean_ctor_set(v_reuseFailAlloc_3313_, 1, v_a_3307_);
v___x_3312_ = v_reuseFailAlloc_3313_;
goto v_reusejp_3311_;
}
v_reusejp_3311_:
{
return v___x_3312_;
}
}
}
}
else
{
lean_object* v___x_3315_; lean_object* v___x_3316_; uint8_t v___x_3317_; 
v___x_3315_ = l_Lean_Syntax_getArg(v_00_u03a8_3277_, v___x_3247_);
v___x_3316_ = l_Lean_Syntax_getNumArgs(v___x_3315_);
v___x_3317_ = lean_nat_dec_le(v___x_3247_, v___x_3316_);
if (v___x_3317_ == 0)
{
lean_object* v___x_3318_; 
lean_dec(v___x_3316_);
lean_dec(v___x_3315_);
v___x_3318_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3277_, v_a_3241_, v_a_3242_);
if (lean_obj_tag(v___x_3318_) == 0)
{
lean_object* v_a_3319_; lean_object* v_a_3320_; lean_object* v___x_3322_; uint8_t v_isShared_3323_; uint8_t v_isSharedCheck_3343_; 
v_a_3319_ = lean_ctor_get(v___x_3318_, 0);
v_a_3320_ = lean_ctor_get(v___x_3318_, 1);
v_isSharedCheck_3343_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3343_ == 0)
{
v___x_3322_ = v___x_3318_;
v_isShared_3323_ = v_isSharedCheck_3343_;
goto v_resetjp_3321_;
}
else
{
lean_inc(v_a_3320_);
lean_inc(v_a_3319_);
lean_dec(v___x_3318_);
v___x_3322_ = lean_box(0);
v_isShared_3323_ = v_isSharedCheck_3343_;
goto v_resetjp_3321_;
}
v_resetjp_3321_:
{
lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3341_; 
v___x_3324_ = l_Lean_SourceInfo_fromRef(v_a_3241_, v___x_3317_);
v___x_3325_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3326_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3324_, 7);
v___x_3327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3327_, 0, v___x_3324_);
lean_ctor_set(v___x_3327_, 1, v___x_3326_);
v___x_3328_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_3329_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3329_, 0, v___x_3324_);
lean_ctor_set(v___x_3329_, 1, v___x_3328_);
v___x_3330_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3331_ = l_Lean_Syntax_node1(v___x_3324_, v___x_3330_, v___x_3267_);
v___x_3332_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3333_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3333_, 0, v___x_3324_);
lean_ctor_set(v___x_3333_, 1, v___x_3330_);
lean_ctor_set(v___x_3333_, 2, v___x_3332_);
v___x_3334_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3335_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3335_, 0, v___x_3324_);
lean_ctor_set(v___x_3335_, 1, v___x_3334_);
v___x_3336_ = l_Lean_Syntax_node5(v___x_3324_, v___x_3278_, v___x_3329_, v___x_3331_, v___x_3333_, v___x_3335_, v_a_3319_);
v___x_3337_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3338_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3338_, 0, v___x_3324_);
lean_ctor_set(v___x_3338_, 1, v___x_3337_);
v___x_3339_ = l_Lean_Syntax_node3(v___x_3324_, v___x_3325_, v___x_3327_, v___x_3336_, v___x_3338_);
if (v_isShared_3323_ == 0)
{
lean_ctor_set(v___x_3322_, 0, v___x_3339_);
v___x_3341_ = v___x_3322_;
goto v_reusejp_3340_;
}
else
{
lean_object* v_reuseFailAlloc_3342_; 
v_reuseFailAlloc_3342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3342_, 0, v___x_3339_);
lean_ctor_set(v_reuseFailAlloc_3342_, 1, v_a_3320_);
v___x_3341_ = v_reuseFailAlloc_3342_;
goto v_reusejp_3340_;
}
v_reusejp_3340_:
{
return v___x_3341_;
}
}
}
else
{
lean_object* v_a_3344_; lean_object* v_a_3345_; lean_object* v___x_3347_; uint8_t v_isShared_3348_; uint8_t v_isSharedCheck_3352_; 
lean_dec(v___x_3267_);
v_a_3344_ = lean_ctor_get(v___x_3318_, 0);
v_a_3345_ = lean_ctor_get(v___x_3318_, 1);
v_isSharedCheck_3352_ = !lean_is_exclusive(v___x_3318_);
if (v_isSharedCheck_3352_ == 0)
{
v___x_3347_ = v___x_3318_;
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
else
{
lean_inc(v_a_3345_);
lean_inc(v_a_3344_);
lean_dec(v___x_3318_);
v___x_3347_ = lean_box(0);
v_isShared_3348_ = v_isSharedCheck_3352_;
goto v_resetjp_3346_;
}
v_resetjp_3346_:
{
lean_object* v___x_3350_; 
if (v_isShared_3348_ == 0)
{
v___x_3350_ = v___x_3347_;
goto v_reusejp_3349_;
}
else
{
lean_object* v_reuseFailAlloc_3351_; 
v_reuseFailAlloc_3351_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3351_, 0, v_a_3344_);
lean_ctor_set(v_reuseFailAlloc_3351_, 1, v_a_3345_);
v___x_3350_ = v_reuseFailAlloc_3351_;
goto v_reusejp_3349_;
}
v_reusejp_3349_:
{
return v___x_3350_;
}
}
}
}
else
{
lean_object* v___x_3353_; uint8_t v___x_3354_; 
v___x_3353_ = l_Lean_Syntax_getArg(v___x_3315_, v___x_3252_);
lean_inc(v___x_3353_);
v___x_3354_ = l_Lean_Syntax_isOfKind(v___x_3353_, v___x_3268_);
if (v___x_3354_ == 0)
{
lean_object* v___x_3355_; 
lean_dec(v___x_3353_);
lean_dec(v___x_3316_);
lean_dec(v___x_3315_);
v___x_3355_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3277_, v_a_3241_, v_a_3242_);
if (lean_obj_tag(v___x_3355_) == 0)
{
lean_object* v_a_3356_; lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3380_; 
v_a_3356_ = lean_ctor_get(v___x_3355_, 0);
v_a_3357_ = lean_ctor_get(v___x_3355_, 1);
v_isSharedCheck_3380_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3380_ == 0)
{
v___x_3359_ = v___x_3355_;
v_isShared_3360_ = v_isSharedCheck_3380_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_inc(v_a_3356_);
lean_dec(v___x_3355_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3380_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3368_; lean_object* v___x_3369_; lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3378_; 
v___x_3361_ = l_Lean_SourceInfo_fromRef(v_a_3241_, v___x_3354_);
v___x_3362_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3363_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3361_, 7);
v___x_3364_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3364_, 0, v___x_3361_);
lean_ctor_set(v___x_3364_, 1, v___x_3363_);
v___x_3365_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_3366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3366_, 0, v___x_3361_);
lean_ctor_set(v___x_3366_, 1, v___x_3365_);
v___x_3367_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3368_ = l_Lean_Syntax_node1(v___x_3361_, v___x_3367_, v___x_3267_);
v___x_3369_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3370_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3370_, 0, v___x_3361_);
lean_ctor_set(v___x_3370_, 1, v___x_3367_);
lean_ctor_set(v___x_3370_, 2, v___x_3369_);
v___x_3371_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3372_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3372_, 0, v___x_3361_);
lean_ctor_set(v___x_3372_, 1, v___x_3371_);
v___x_3373_ = l_Lean_Syntax_node5(v___x_3361_, v___x_3278_, v___x_3366_, v___x_3368_, v___x_3370_, v___x_3372_, v_a_3356_);
v___x_3374_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3375_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3375_, 0, v___x_3361_);
lean_ctor_set(v___x_3375_, 1, v___x_3374_);
v___x_3376_ = l_Lean_Syntax_node3(v___x_3361_, v___x_3362_, v___x_3364_, v___x_3373_, v___x_3375_);
if (v_isShared_3360_ == 0)
{
lean_ctor_set(v___x_3359_, 0, v___x_3376_);
v___x_3378_ = v___x_3359_;
goto v_reusejp_3377_;
}
else
{
lean_object* v_reuseFailAlloc_3379_; 
v_reuseFailAlloc_3379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3379_, 0, v___x_3376_);
lean_ctor_set(v_reuseFailAlloc_3379_, 1, v_a_3357_);
v___x_3378_ = v_reuseFailAlloc_3379_;
goto v_reusejp_3377_;
}
v_reusejp_3377_:
{
return v___x_3378_;
}
}
}
else
{
lean_object* v_a_3381_; lean_object* v_a_3382_; lean_object* v___x_3384_; uint8_t v_isShared_3385_; uint8_t v_isSharedCheck_3389_; 
lean_dec(v___x_3267_);
v_a_3381_ = lean_ctor_get(v___x_3355_, 0);
v_a_3382_ = lean_ctor_get(v___x_3355_, 1);
v_isSharedCheck_3389_ = !lean_is_exclusive(v___x_3355_);
if (v_isSharedCheck_3389_ == 0)
{
v___x_3384_ = v___x_3355_;
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
else
{
lean_inc(v_a_3382_);
lean_inc(v_a_3381_);
lean_dec(v___x_3355_);
v___x_3384_ = lean_box(0);
v_isShared_3385_ = v_isSharedCheck_3389_;
goto v_resetjp_3383_;
}
v_resetjp_3383_:
{
lean_object* v___x_3387_; 
if (v_isShared_3385_ == 0)
{
v___x_3387_ = v___x_3384_;
goto v_reusejp_3386_;
}
else
{
lean_object* v_reuseFailAlloc_3388_; 
v_reuseFailAlloc_3388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3388_, 0, v_a_3381_);
lean_ctor_set(v_reuseFailAlloc_3388_, 1, v_a_3382_);
v___x_3387_ = v_reuseFailAlloc_3388_;
goto v_reusejp_3386_;
}
v_reusejp_3386_:
{
return v___x_3387_;
}
}
}
}
else
{
lean_object* v___x_3390_; lean_object* v___x_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; size_t v_sz_3396_; size_t v___x_3397_; lean_object* v___x_3398_; 
v___x_3390_ = l_Lean_Syntax_getArgs(v___x_3315_);
lean_dec(v___x_3315_);
v___x_3391_ = l_Array_extract___redArg(v___x_3390_, v___x_3247_, v___x_3316_);
lean_dec_ref(v___x_3390_);
v___x_3392_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3393_ = lean_box(2);
v___x_3394_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3393_);
lean_ctor_set(v___x_3394_, 1, v___x_3392_);
lean_ctor_set(v___x_3394_, 2, v___x_3391_);
v___x_3395_ = l_Lean_Syntax_getArgs(v___x_3394_);
lean_dec_ref_known(v___x_3394_, 3);
v_sz_3396_ = lean_array_size(v___x_3395_);
v___x_3397_ = ((size_t)0ULL);
v___x_3398_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__0(v_sz_3396_, v___x_3397_, v___x_3395_);
if (lean_obj_tag(v___x_3398_) == 0)
{
lean_object* v___x_3399_; 
lean_dec(v___x_3353_);
v___x_3399_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3277_, v_a_3241_, v_a_3242_);
if (lean_obj_tag(v___x_3399_) == 0)
{
lean_object* v_a_3400_; lean_object* v_a_3401_; lean_object* v___x_3403_; uint8_t v_isShared_3404_; uint8_t v_isSharedCheck_3424_; 
v_a_3400_ = lean_ctor_get(v___x_3399_, 0);
v_a_3401_ = lean_ctor_get(v___x_3399_, 1);
v_isSharedCheck_3424_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3424_ == 0)
{
v___x_3403_ = v___x_3399_;
v_isShared_3404_ = v_isSharedCheck_3424_;
goto v_resetjp_3402_;
}
else
{
lean_inc(v_a_3401_);
lean_inc(v_a_3400_);
lean_dec(v___x_3399_);
v___x_3403_ = lean_box(0);
v_isShared_3404_ = v_isSharedCheck_3424_;
goto v_resetjp_3402_;
}
v_resetjp_3402_:
{
uint8_t v___x_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3413_; lean_object* v___x_3414_; lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; lean_object* v___x_3418_; lean_object* v___x_3419_; lean_object* v___x_3420_; lean_object* v___x_3422_; 
v___x_3405_ = 0;
v___x_3406_ = l_Lean_SourceInfo_fromRef(v_a_3241_, v___x_3405_);
v___x_3407_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3408_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3406_, 7);
v___x_3409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3406_);
lean_ctor_set(v___x_3409_, 1, v___x_3408_);
v___x_3410_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_3411_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3411_, 0, v___x_3406_);
lean_ctor_set(v___x_3411_, 1, v___x_3410_);
v___x_3412_ = l_Lean_Syntax_node1(v___x_3406_, v___x_3392_, v___x_3267_);
v___x_3413_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3414_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3414_, 0, v___x_3406_);
lean_ctor_set(v___x_3414_, 1, v___x_3392_);
lean_ctor_set(v___x_3414_, 2, v___x_3413_);
v___x_3415_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3416_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3406_);
lean_ctor_set(v___x_3416_, 1, v___x_3415_);
v___x_3417_ = l_Lean_Syntax_node5(v___x_3406_, v___x_3278_, v___x_3411_, v___x_3412_, v___x_3414_, v___x_3416_, v_a_3400_);
v___x_3418_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3419_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3419_, 0, v___x_3406_);
lean_ctor_set(v___x_3419_, 1, v___x_3418_);
v___x_3420_ = l_Lean_Syntax_node3(v___x_3406_, v___x_3407_, v___x_3409_, v___x_3417_, v___x_3419_);
if (v_isShared_3404_ == 0)
{
lean_ctor_set(v___x_3403_, 0, v___x_3420_);
v___x_3422_ = v___x_3403_;
goto v_reusejp_3421_;
}
else
{
lean_object* v_reuseFailAlloc_3423_; 
v_reuseFailAlloc_3423_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3423_, 0, v___x_3420_);
lean_ctor_set(v_reuseFailAlloc_3423_, 1, v_a_3401_);
v___x_3422_ = v_reuseFailAlloc_3423_;
goto v_reusejp_3421_;
}
v_reusejp_3421_:
{
return v___x_3422_;
}
}
}
else
{
lean_object* v_a_3425_; lean_object* v_a_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3433_; 
lean_dec(v___x_3267_);
v_a_3425_ = lean_ctor_get(v___x_3399_, 0);
v_a_3426_ = lean_ctor_get(v___x_3399_, 1);
v_isSharedCheck_3433_ = !lean_is_exclusive(v___x_3399_);
if (v_isSharedCheck_3433_ == 0)
{
v___x_3428_ = v___x_3399_;
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_a_3426_);
lean_inc(v_a_3425_);
lean_dec(v___x_3399_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3433_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3431_; 
if (v_isShared_3429_ == 0)
{
v___x_3431_ = v___x_3428_;
goto v_reusejp_3430_;
}
else
{
lean_object* v_reuseFailAlloc_3432_; 
v_reuseFailAlloc_3432_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3432_, 0, v_a_3425_);
lean_ctor_set(v_reuseFailAlloc_3432_, 1, v_a_3426_);
v___x_3431_ = v_reuseFailAlloc_3432_;
goto v_reusejp_3430_;
}
v_reusejp_3430_:
{
return v___x_3431_;
}
}
}
}
else
{
lean_object* v_val_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; uint8_t v___x_3437_; 
v_val_3434_ = lean_ctor_get(v___x_3398_, 0);
lean_inc(v_val_3434_);
lean_dec_ref_known(v___x_3398_, 1);
v___x_3435_ = lean_unsigned_to_nat(2u);
v___x_3436_ = l_Lean_Syntax_getArg(v_00_u03a8_3277_, v___x_3435_);
v___x_3437_ = l_Lean_Syntax_matchesNull(v___x_3436_, v___x_3252_);
if (v___x_3437_ == 0)
{
lean_object* v___x_3438_; 
lean_dec(v_val_3434_);
lean_dec(v___x_3353_);
v___x_3438_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3277_, v_a_3241_, v_a_3242_);
if (lean_obj_tag(v___x_3438_) == 0)
{
lean_object* v_a_3439_; lean_object* v_a_3440_; lean_object* v___x_3442_; uint8_t v_isShared_3443_; uint8_t v_isSharedCheck_3462_; 
v_a_3439_ = lean_ctor_get(v___x_3438_, 0);
v_a_3440_ = lean_ctor_get(v___x_3438_, 1);
v_isSharedCheck_3462_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3462_ == 0)
{
v___x_3442_ = v___x_3438_;
v_isShared_3443_ = v_isSharedCheck_3462_;
goto v_resetjp_3441_;
}
else
{
lean_inc(v_a_3440_);
lean_inc(v_a_3439_);
lean_dec(v___x_3438_);
v___x_3442_ = lean_box(0);
v_isShared_3443_ = v_isSharedCheck_3462_;
goto v_resetjp_3441_;
}
v_resetjp_3441_:
{
lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; lean_object* v___x_3453_; lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3460_; 
v___x_3444_ = l_Lean_SourceInfo_fromRef(v_a_3241_, v___x_3437_);
v___x_3445_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3446_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3444_, 7);
v___x_3447_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3444_);
lean_ctor_set(v___x_3447_, 1, v___x_3446_);
v___x_3448_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_3449_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3449_, 0, v___x_3444_);
lean_ctor_set(v___x_3449_, 1, v___x_3448_);
v___x_3450_ = l_Lean_Syntax_node1(v___x_3444_, v___x_3392_, v___x_3267_);
v___x_3451_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3452_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3452_, 0, v___x_3444_);
lean_ctor_set(v___x_3452_, 1, v___x_3392_);
lean_ctor_set(v___x_3452_, 2, v___x_3451_);
v___x_3453_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3454_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3454_, 0, v___x_3444_);
lean_ctor_set(v___x_3454_, 1, v___x_3453_);
v___x_3455_ = l_Lean_Syntax_node5(v___x_3444_, v___x_3278_, v___x_3449_, v___x_3450_, v___x_3452_, v___x_3454_, v_a_3439_);
v___x_3456_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3457_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3444_);
lean_ctor_set(v___x_3457_, 1, v___x_3456_);
v___x_3458_ = l_Lean_Syntax_node3(v___x_3444_, v___x_3445_, v___x_3447_, v___x_3455_, v___x_3457_);
if (v_isShared_3443_ == 0)
{
lean_ctor_set(v___x_3442_, 0, v___x_3458_);
v___x_3460_ = v___x_3442_;
goto v_reusejp_3459_;
}
else
{
lean_object* v_reuseFailAlloc_3461_; 
v_reuseFailAlloc_3461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3461_, 0, v___x_3458_);
lean_ctor_set(v_reuseFailAlloc_3461_, 1, v_a_3440_);
v___x_3460_ = v_reuseFailAlloc_3461_;
goto v_reusejp_3459_;
}
v_reusejp_3459_:
{
return v___x_3460_;
}
}
}
else
{
lean_object* v_a_3463_; lean_object* v_a_3464_; lean_object* v___x_3466_; uint8_t v_isShared_3467_; uint8_t v_isSharedCheck_3471_; 
lean_dec(v___x_3267_);
v_a_3463_ = lean_ctor_get(v___x_3438_, 0);
v_a_3464_ = lean_ctor_get(v___x_3438_, 1);
v_isSharedCheck_3471_ = !lean_is_exclusive(v___x_3438_);
if (v_isSharedCheck_3471_ == 0)
{
v___x_3466_ = v___x_3438_;
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
else
{
lean_inc(v_a_3464_);
lean_inc(v_a_3463_);
lean_dec(v___x_3438_);
v___x_3466_ = lean_box(0);
v_isShared_3467_ = v_isSharedCheck_3471_;
goto v_resetjp_3465_;
}
v_resetjp_3465_:
{
lean_object* v___x_3469_; 
if (v_isShared_3467_ == 0)
{
v___x_3469_ = v___x_3466_;
goto v_reusejp_3468_;
}
else
{
lean_object* v_reuseFailAlloc_3470_; 
v_reuseFailAlloc_3470_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3470_, 0, v_a_3463_);
lean_ctor_set(v_reuseFailAlloc_3470_, 1, v_a_3464_);
v___x_3469_ = v_reuseFailAlloc_3470_;
goto v_reusejp_3468_;
}
v_reusejp_3468_:
{
return v___x_3469_;
}
}
}
}
else
{
lean_object* v___x_3472_; lean_object* v_00_u03a8_3473_; lean_object* v___x_3474_; 
v___x_3472_ = lean_unsigned_to_nat(4u);
v_00_u03a8_3473_ = l_Lean_Syntax_getArg(v_00_u03a8_3277_, v___x_3472_);
lean_dec(v_00_u03a8_3277_);
v___x_3474_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3473_, v_a_3241_, v_a_3242_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_object* v_a_3475_; lean_object* v_a_3476_; lean_object* v___x_3478_; uint8_t v_isShared_3479_; uint8_t v_isSharedCheck_3503_; 
v_a_3475_ = lean_ctor_get(v___x_3474_, 0);
v_a_3476_ = lean_ctor_get(v___x_3474_, 1);
v_isSharedCheck_3503_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3503_ == 0)
{
v___x_3478_ = v___x_3474_;
v_isShared_3479_ = v_isSharedCheck_3503_;
goto v_resetjp_3477_;
}
else
{
lean_inc(v_a_3476_);
lean_inc(v_a_3475_);
lean_dec(v___x_3474_);
v___x_3478_ = lean_box(0);
v_isShared_3479_ = v_isSharedCheck_3503_;
goto v_resetjp_3477_;
}
v_resetjp_3477_:
{
uint8_t v___x_3480_; lean_object* v___x_3481_; lean_object* v___x_3482_; lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; size_t v_sz_3488_; lean_object* v___x_3489_; lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3494_; lean_object* v___x_3495_; lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3501_; 
v___x_3480_ = 0;
v___x_3481_ = l_Lean_SourceInfo_fromRef(v_a_3241_, v___x_3480_);
v___x_3482_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3483_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3481_, 7);
v___x_3484_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3484_, 0, v___x_3481_);
lean_ctor_set(v___x_3484_, 1, v___x_3483_);
v___x_3485_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_3486_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3481_);
lean_ctor_set(v___x_3486_, 1, v___x_3485_);
v___x_3487_ = l_Array_mkArray2___redArg(v___x_3267_, v___x_3353_);
v_sz_3488_ = lean_array_size(v_val_3434_);
v___x_3489_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__1(v_sz_3488_, v___x_3397_, v_val_3434_);
v___x_3490_ = l_Array_append___redArg(v___x_3487_, v___x_3489_);
lean_dec_ref(v___x_3489_);
v___x_3491_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3481_);
lean_ctor_set(v___x_3491_, 1, v___x_3392_);
lean_ctor_set(v___x_3491_, 2, v___x_3490_);
v___x_3492_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3493_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3493_, 0, v___x_3481_);
lean_ctor_set(v___x_3493_, 1, v___x_3392_);
lean_ctor_set(v___x_3493_, 2, v___x_3492_);
v___x_3494_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3495_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3495_, 0, v___x_3481_);
lean_ctor_set(v___x_3495_, 1, v___x_3494_);
v___x_3496_ = l_Lean_Syntax_node5(v___x_3481_, v___x_3278_, v___x_3486_, v___x_3491_, v___x_3493_, v___x_3495_, v_a_3475_);
v___x_3497_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3498_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3481_);
lean_ctor_set(v___x_3498_, 1, v___x_3497_);
v___x_3499_ = l_Lean_Syntax_node3(v___x_3481_, v___x_3482_, v___x_3484_, v___x_3496_, v___x_3498_);
if (v_isShared_3479_ == 0)
{
lean_ctor_set(v___x_3478_, 0, v___x_3499_);
v___x_3501_ = v___x_3478_;
goto v_reusejp_3500_;
}
else
{
lean_object* v_reuseFailAlloc_3502_; 
v_reuseFailAlloc_3502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3502_, 0, v___x_3499_);
lean_ctor_set(v_reuseFailAlloc_3502_, 1, v_a_3476_);
v___x_3501_ = v_reuseFailAlloc_3502_;
goto v_reusejp_3500_;
}
v_reusejp_3500_:
{
return v___x_3501_;
}
}
}
else
{
lean_object* v_a_3504_; lean_object* v_a_3505_; lean_object* v___x_3507_; uint8_t v_isShared_3508_; uint8_t v_isSharedCheck_3512_; 
lean_dec(v_val_3434_);
lean_dec(v___x_3353_);
lean_dec(v___x_3267_);
v_a_3504_ = lean_ctor_get(v___x_3474_, 0);
v_a_3505_ = lean_ctor_get(v___x_3474_, 1);
v_isSharedCheck_3512_ = !lean_is_exclusive(v___x_3474_);
if (v_isSharedCheck_3512_ == 0)
{
v___x_3507_ = v___x_3474_;
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
else
{
lean_inc(v_a_3505_);
lean_inc(v_a_3504_);
lean_dec(v___x_3474_);
v___x_3507_ = lean_box(0);
v_isShared_3508_ = v_isSharedCheck_3512_;
goto v_resetjp_3506_;
}
v_resetjp_3506_:
{
lean_object* v___x_3510_; 
if (v_isShared_3508_ == 0)
{
v___x_3510_ = v___x_3507_;
goto v_reusejp_3509_;
}
else
{
lean_object* v_reuseFailAlloc_3511_; 
v_reuseFailAlloc_3511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3511_, 0, v_a_3504_);
lean_ctor_set(v_reuseFailAlloc_3511_, 1, v_a_3505_);
v___x_3510_ = v_reuseFailAlloc_3511_;
goto v_reusejp_3509_;
}
v_reusejp_3509_:
{
return v___x_3510_;
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
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandForall___boxed(lean_object* v_x_3513_, lean_object* v_a_3514_, lean_object* v_a_3515_){
_start:
{
lean_object* v_res_3516_; 
v_res_3516_ = l_Std_Do_SPred_Notation_unexpandForall(v_x_3513_, v_a_3514_, v_a_3515_);
lean_dec(v_a_3514_);
return v_res_3516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1(lean_object* v___x_3521_, size_t v_sz_3522_, size_t v_i_3523_, lean_object* v_bs_3524_){
_start:
{
uint8_t v___x_3525_; 
v___x_3525_ = lean_usize_dec_lt(v_i_3523_, v_sz_3522_);
if (v___x_3525_ == 0)
{
lean_dec(v___x_3521_);
return v_bs_3524_;
}
else
{
lean_object* v___x_3526_; lean_object* v_v_3527_; lean_object* v___x_3528_; lean_object* v_bs_x27_3529_; lean_object* v___x_3530_; size_t v___x_3531_; size_t v___x_3532_; lean_object* v___x_3533_; 
v___x_3526_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
v_v_3527_ = lean_array_uget(v_bs_3524_, v_i_3523_);
v___x_3528_ = lean_unsigned_to_nat(0u);
v_bs_x27_3529_ = lean_array_uset(v_bs_3524_, v_i_3523_, v___x_3528_);
lean_inc(v___x_3521_);
v___x_3530_ = l_Lean_Syntax_node1(v___x_3521_, v___x_3526_, v_v_3527_);
v___x_3531_ = ((size_t)1ULL);
v___x_3532_ = lean_usize_add(v_i_3523_, v___x_3531_);
v___x_3533_ = lean_array_uset(v_bs_x27_3529_, v_i_3523_, v___x_3530_);
v_i_3523_ = v___x_3532_;
v_bs_3524_ = v___x_3533_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___boxed(lean_object* v___x_3535_, lean_object* v_sz_3536_, lean_object* v_i_3537_, lean_object* v_bs_3538_){
_start:
{
size_t v_sz_boxed_3539_; size_t v_i_boxed_3540_; lean_object* v_res_3541_; 
v_sz_boxed_3539_ = lean_unbox_usize(v_sz_3536_);
lean_dec(v_sz_3536_);
v_i_boxed_3540_ = lean_unbox_usize(v_i_3537_);
lean_dec(v_i_3537_);
v_res_3541_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1(v___x_3535_, v_sz_boxed_3539_, v_i_boxed_3540_, v_bs_3538_);
return v_res_3541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__0(size_t v_sz_3542_, size_t v_i_3543_, lean_object* v_bs_3544_){
_start:
{
uint8_t v___x_3545_; 
v___x_3545_ = lean_usize_dec_lt(v_i_3543_, v_sz_3542_);
if (v___x_3545_ == 0)
{
lean_object* v___x_3546_; 
v___x_3546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3546_, 0, v_bs_3544_);
return v___x_3546_;
}
else
{
lean_object* v___x_3547_; lean_object* v_v_3548_; uint8_t v___x_3549_; 
v___x_3547_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
v_v_3548_ = lean_array_uget_borrowed(v_bs_3544_, v_i_3543_);
lean_inc(v_v_3548_);
v___x_3549_ = l_Lean_Syntax_isOfKind(v_v_3548_, v___x_3547_);
if (v___x_3549_ == 0)
{
lean_object* v___x_3550_; 
lean_dec_ref(v_bs_3544_);
v___x_3550_ = lean_box(0);
return v___x_3550_;
}
else
{
lean_object* v___x_3551_; lean_object* v_z_3552_; lean_object* v___x_3553_; uint8_t v___x_3554_; 
v___x_3551_ = lean_unsigned_to_nat(0u);
v_z_3552_ = l_Lean_Syntax_getArg(v_v_3548_, v___x_3551_);
v___x_3553_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_z_3552_);
v___x_3554_ = l_Lean_Syntax_isOfKind(v_z_3552_, v___x_3553_);
if (v___x_3554_ == 0)
{
lean_object* v___x_3555_; 
lean_dec(v_z_3552_);
lean_dec_ref(v_bs_3544_);
v___x_3555_ = lean_box(0);
return v___x_3555_;
}
else
{
lean_object* v_bs_x27_3556_; size_t v___x_3557_; size_t v___x_3558_; lean_object* v___x_3559_; 
v_bs_x27_3556_ = lean_array_uset(v_bs_3544_, v_i_3543_, v___x_3551_);
v___x_3557_ = ((size_t)1ULL);
v___x_3558_ = lean_usize_add(v_i_3543_, v___x_3557_);
v___x_3559_ = lean_array_uset(v_bs_x27_3556_, v_i_3543_, v_z_3552_);
v_i_3543_ = v___x_3558_;
v_bs_3544_ = v___x_3559_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__0___boxed(lean_object* v_sz_3561_, lean_object* v_i_3562_, lean_object* v_bs_3563_){
_start:
{
size_t v_sz_boxed_3564_; size_t v_i_boxed_3565_; lean_object* v_res_3566_; 
v_sz_boxed_3564_ = lean_unbox_usize(v_sz_3561_);
lean_dec(v_sz_3561_);
v_i_boxed_3565_ = lean_unbox_usize(v_i_3562_);
lean_dec(v_i_3562_);
v_res_3566_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__0(v_sz_boxed_3564_, v_i_boxed_3565_, v_bs_3563_);
return v_res_3566_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandExists(lean_object* v_x_3572_, lean_object* v_a_3573_, lean_object* v_a_3574_){
_start:
{
lean_object* v___x_3575_; uint8_t v___x_3576_; 
v___x_3575_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_3572_);
v___x_3576_ = l_Lean_Syntax_isOfKind(v_x_3572_, v___x_3575_);
if (v___x_3576_ == 0)
{
lean_object* v___x_3577_; lean_object* v___x_3578_; 
lean_dec(v_x_3572_);
v___x_3577_ = lean_box(0);
v___x_3578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3578_, 0, v___x_3577_);
lean_ctor_set(v___x_3578_, 1, v_a_3574_);
return v___x_3578_;
}
else
{
lean_object* v___x_3579_; lean_object* v___x_3580_; uint8_t v___x_3581_; 
v___x_3579_ = lean_unsigned_to_nat(1u);
v___x_3580_ = l_Lean_Syntax_getArg(v_x_3572_, v___x_3579_);
lean_dec(v_x_3572_);
lean_inc(v___x_3580_);
v___x_3581_ = l_Lean_Syntax_matchesNull(v___x_3580_, v___x_3579_);
if (v___x_3581_ == 0)
{
lean_object* v___x_3582_; lean_object* v___x_3583_; 
lean_dec(v___x_3580_);
v___x_3582_ = lean_box(0);
v___x_3583_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3582_);
lean_ctor_set(v___x_3583_, 1, v_a_3574_);
return v___x_3583_;
}
else
{
lean_object* v___x_3584_; lean_object* v___x_3585_; lean_object* v___x_3586_; uint8_t v___x_3587_; 
v___x_3584_ = lean_unsigned_to_nat(0u);
v___x_3585_ = l_Lean_Syntax_getArg(v___x_3580_, v___x_3584_);
lean_dec(v___x_3580_);
v___x_3586_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
lean_inc(v___x_3585_);
v___x_3587_ = l_Lean_Syntax_isOfKind(v___x_3585_, v___x_3586_);
if (v___x_3587_ == 0)
{
lean_object* v___x_3588_; lean_object* v___x_3589_; 
lean_dec(v___x_3585_);
v___x_3588_ = lean_box(0);
v___x_3589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3589_, 0, v___x_3588_);
lean_ctor_set(v___x_3589_, 1, v_a_3574_);
return v___x_3589_;
}
else
{
lean_object* v___x_3590_; lean_object* v___x_3591_; uint8_t v___x_3592_; 
v___x_3590_ = l_Lean_Syntax_getArg(v___x_3585_, v___x_3579_);
lean_dec(v___x_3585_);
v___x_3591_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
lean_inc(v___x_3590_);
v___x_3592_ = l_Lean_Syntax_isOfKind(v___x_3590_, v___x_3591_);
if (v___x_3592_ == 0)
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
lean_dec(v___x_3590_);
v___x_3593_ = lean_box(0);
v___x_3594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3594_, 0, v___x_3593_);
lean_ctor_set(v___x_3594_, 1, v_a_3574_);
return v___x_3594_;
}
else
{
lean_object* v___x_3595_; uint8_t v___x_3596_; 
v___x_3595_ = l_Lean_Syntax_getArg(v___x_3590_, v___x_3584_);
lean_inc(v___x_3595_);
v___x_3596_ = l_Lean_Syntax_matchesNull(v___x_3595_, v___x_3579_);
if (v___x_3596_ == 0)
{
lean_object* v___x_3597_; lean_object* v___x_3598_; 
lean_dec(v___x_3595_);
lean_dec(v___x_3590_);
v___x_3597_ = lean_box(0);
v___x_3598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3598_, 0, v___x_3597_);
lean_ctor_set(v___x_3598_, 1, v_a_3574_);
return v___x_3598_;
}
else
{
lean_object* v___x_3599_; lean_object* v___x_3600_; uint8_t v___x_3601_; 
v___x_3599_ = l_Lean_Syntax_getArg(v___x_3595_, v___x_3584_);
lean_dec(v___x_3595_);
v___x_3600_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v___x_3599_);
v___x_3601_ = l_Lean_Syntax_isOfKind(v___x_3599_, v___x_3600_);
if (v___x_3601_ == 0)
{
lean_object* v___x_3602_; lean_object* v___x_3603_; 
lean_dec(v___x_3599_);
lean_dec(v___x_3590_);
v___x_3602_ = lean_box(0);
v___x_3603_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3603_, 0, v___x_3602_);
lean_ctor_set(v___x_3603_, 1, v_a_3574_);
return v___x_3603_;
}
else
{
lean_object* v___x_3604_; uint8_t v___x_3605_; 
v___x_3604_ = l_Lean_Syntax_getArg(v___x_3590_, v___x_3579_);
v___x_3605_ = l_Lean_Syntax_matchesNull(v___x_3604_, v___x_3584_);
if (v___x_3605_ == 0)
{
lean_object* v___x_3606_; lean_object* v___x_3607_; 
lean_dec(v___x_3599_);
lean_dec(v___x_3590_);
v___x_3606_ = lean_box(0);
v___x_3607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___x_3606_);
lean_ctor_set(v___x_3607_, 1, v_a_3574_);
return v___x_3607_;
}
else
{
lean_object* v___x_3608_; lean_object* v_00_u03a8_3609_; lean_object* v___x_3610_; uint8_t v___x_3611_; 
v___x_3608_ = lean_unsigned_to_nat(3u);
v_00_u03a8_3609_ = l_Lean_Syntax_getArg(v___x_3590_, v___x_3608_);
lean_dec(v___x_3590_);
v___x_3610_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__11));
lean_inc(v_00_u03a8_3609_);
v___x_3611_ = l_Lean_Syntax_isOfKind(v_00_u03a8_3609_, v___x_3610_);
if (v___x_3611_ == 0)
{
lean_object* v___x_3612_; 
v___x_3612_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3609_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_3612_) == 0)
{
lean_object* v_a_3613_; lean_object* v_a_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3643_; 
v_a_3613_ = lean_ctor_get(v___x_3612_, 0);
v_a_3614_ = lean_ctor_get(v___x_3612_, 1);
v_isSharedCheck_3643_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3643_ == 0)
{
v___x_3616_ = v___x_3612_;
v_isShared_3617_ = v_isSharedCheck_3643_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_a_3614_);
lean_inc(v_a_3613_);
lean_dec(v___x_3612_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3643_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___x_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; lean_object* v___x_3630_; lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3641_; 
v___x_3618_ = l_Lean_SourceInfo_fromRef(v_a_3573_, v___x_3611_);
v___x_3619_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3620_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3618_, 10);
v___x_3621_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3621_, 0, v___x_3618_);
lean_ctor_set(v___x_3621_, 1, v___x_3620_);
v___x_3622_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_3623_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3623_, 0, v___x_3618_);
lean_ctor_set(v___x_3623_, 1, v___x_3622_);
v___x_3624_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__67));
v___x_3625_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__2));
v___x_3626_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3627_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
v___x_3628_ = l_Lean_Syntax_node1(v___x_3618_, v___x_3627_, v___x_3599_);
v___x_3629_ = l_Lean_Syntax_node1(v___x_3618_, v___x_3626_, v___x_3628_);
v___x_3630_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3631_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3631_, 0, v___x_3618_);
lean_ctor_set(v___x_3631_, 1, v___x_3626_);
lean_ctor_set(v___x_3631_, 2, v___x_3630_);
v___x_3632_ = l_Lean_Syntax_node2(v___x_3618_, v___x_3625_, v___x_3629_, v___x_3631_);
v___x_3633_ = l_Lean_Syntax_node1(v___x_3618_, v___x_3624_, v___x_3632_);
v___x_3634_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3635_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3635_, 0, v___x_3618_);
lean_ctor_set(v___x_3635_, 1, v___x_3634_);
v___x_3636_ = l_Lean_Syntax_node4(v___x_3618_, v___x_3610_, v___x_3623_, v___x_3633_, v___x_3635_, v_a_3613_);
v___x_3637_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3638_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3638_, 0, v___x_3618_);
lean_ctor_set(v___x_3638_, 1, v___x_3637_);
v___x_3639_ = l_Lean_Syntax_node3(v___x_3618_, v___x_3619_, v___x_3621_, v___x_3636_, v___x_3638_);
if (v_isShared_3617_ == 0)
{
lean_ctor_set(v___x_3616_, 0, v___x_3639_);
v___x_3641_ = v___x_3616_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3642_; 
v_reuseFailAlloc_3642_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3642_, 0, v___x_3639_);
lean_ctor_set(v_reuseFailAlloc_3642_, 1, v_a_3614_);
v___x_3641_ = v_reuseFailAlloc_3642_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
return v___x_3641_;
}
}
}
else
{
lean_object* v_a_3644_; lean_object* v_a_3645_; lean_object* v___x_3647_; uint8_t v_isShared_3648_; uint8_t v_isSharedCheck_3652_; 
lean_dec(v___x_3599_);
v_a_3644_ = lean_ctor_get(v___x_3612_, 0);
v_a_3645_ = lean_ctor_get(v___x_3612_, 1);
v_isSharedCheck_3652_ = !lean_is_exclusive(v___x_3612_);
if (v_isSharedCheck_3652_ == 0)
{
v___x_3647_ = v___x_3612_;
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
else
{
lean_inc(v_a_3645_);
lean_inc(v_a_3644_);
lean_dec(v___x_3612_);
v___x_3647_ = lean_box(0);
v_isShared_3648_ = v_isSharedCheck_3652_;
goto v_resetjp_3646_;
}
v_resetjp_3646_:
{
lean_object* v___x_3650_; 
if (v_isShared_3648_ == 0)
{
v___x_3650_ = v___x_3647_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v_a_3644_);
lean_ctor_set(v_reuseFailAlloc_3651_, 1, v_a_3645_);
v___x_3650_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
return v___x_3650_;
}
}
}
}
else
{
lean_object* v___x_3653_; lean_object* v___x_3654_; uint8_t v___x_3655_; 
v___x_3653_ = l_Lean_Syntax_getArg(v_00_u03a8_3609_, v___x_3579_);
v___x_3654_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__67));
lean_inc(v___x_3653_);
v___x_3655_ = l_Lean_Syntax_isOfKind(v___x_3653_, v___x_3654_);
if (v___x_3655_ == 0)
{
lean_object* v___x_3656_; 
lean_dec(v___x_3653_);
v___x_3656_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3609_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v_a_3657_; lean_object* v_a_3658_; lean_object* v___x_3660_; uint8_t v_isShared_3661_; uint8_t v_isSharedCheck_3686_; 
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
v_a_3658_ = lean_ctor_get(v___x_3656_, 1);
v_isSharedCheck_3686_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3686_ == 0)
{
v___x_3660_ = v___x_3656_;
v_isShared_3661_ = v_isSharedCheck_3686_;
goto v_resetjp_3659_;
}
else
{
lean_inc(v_a_3658_);
lean_inc(v_a_3657_);
lean_dec(v___x_3656_);
v___x_3660_ = lean_box(0);
v_isShared_3661_ = v_isSharedCheck_3686_;
goto v_resetjp_3659_;
}
v_resetjp_3659_:
{
lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3664_; lean_object* v___x_3665_; lean_object* v___x_3666_; lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3677_; lean_object* v___x_3678_; lean_object* v___x_3679_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___x_3684_; 
v___x_3662_ = l_Lean_SourceInfo_fromRef(v_a_3573_, v___x_3655_);
v___x_3663_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3664_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3662_, 10);
v___x_3665_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3665_, 0, v___x_3662_);
lean_ctor_set(v___x_3665_, 1, v___x_3664_);
v___x_3666_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_3667_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3667_, 0, v___x_3662_);
lean_ctor_set(v___x_3667_, 1, v___x_3666_);
v___x_3668_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__2));
v___x_3669_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3670_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
v___x_3671_ = l_Lean_Syntax_node1(v___x_3662_, v___x_3670_, v___x_3599_);
v___x_3672_ = l_Lean_Syntax_node1(v___x_3662_, v___x_3669_, v___x_3671_);
v___x_3673_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3674_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3662_);
lean_ctor_set(v___x_3674_, 1, v___x_3669_);
lean_ctor_set(v___x_3674_, 2, v___x_3673_);
v___x_3675_ = l_Lean_Syntax_node2(v___x_3662_, v___x_3668_, v___x_3672_, v___x_3674_);
v___x_3676_ = l_Lean_Syntax_node1(v___x_3662_, v___x_3654_, v___x_3675_);
v___x_3677_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3678_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3678_, 0, v___x_3662_);
lean_ctor_set(v___x_3678_, 1, v___x_3677_);
v___x_3679_ = l_Lean_Syntax_node4(v___x_3662_, v___x_3610_, v___x_3667_, v___x_3676_, v___x_3678_, v_a_3657_);
v___x_3680_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3681_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3681_, 0, v___x_3662_);
lean_ctor_set(v___x_3681_, 1, v___x_3680_);
v___x_3682_ = l_Lean_Syntax_node3(v___x_3662_, v___x_3663_, v___x_3665_, v___x_3679_, v___x_3681_);
if (v_isShared_3661_ == 0)
{
lean_ctor_set(v___x_3660_, 0, v___x_3682_);
v___x_3684_ = v___x_3660_;
goto v_reusejp_3683_;
}
else
{
lean_object* v_reuseFailAlloc_3685_; 
v_reuseFailAlloc_3685_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3685_, 0, v___x_3682_);
lean_ctor_set(v_reuseFailAlloc_3685_, 1, v_a_3658_);
v___x_3684_ = v_reuseFailAlloc_3685_;
goto v_reusejp_3683_;
}
v_reusejp_3683_:
{
return v___x_3684_;
}
}
}
else
{
lean_object* v_a_3687_; lean_object* v_a_3688_; lean_object* v___x_3690_; uint8_t v_isShared_3691_; uint8_t v_isSharedCheck_3695_; 
lean_dec(v___x_3599_);
v_a_3687_ = lean_ctor_get(v___x_3656_, 0);
v_a_3688_ = lean_ctor_get(v___x_3656_, 1);
v_isSharedCheck_3695_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3695_ == 0)
{
v___x_3690_ = v___x_3656_;
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
else
{
lean_inc(v_a_3688_);
lean_inc(v_a_3687_);
lean_dec(v___x_3656_);
v___x_3690_ = lean_box(0);
v_isShared_3691_ = v_isSharedCheck_3695_;
goto v_resetjp_3689_;
}
v_resetjp_3689_:
{
lean_object* v___x_3693_; 
if (v_isShared_3691_ == 0)
{
v___x_3693_ = v___x_3690_;
goto v_reusejp_3692_;
}
else
{
lean_object* v_reuseFailAlloc_3694_; 
v_reuseFailAlloc_3694_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3694_, 0, v_a_3687_);
lean_ctor_set(v_reuseFailAlloc_3694_, 1, v_a_3688_);
v___x_3693_ = v_reuseFailAlloc_3694_;
goto v_reusejp_3692_;
}
v_reusejp_3692_:
{
return v___x_3693_;
}
}
}
}
else
{
lean_object* v___x_3696_; lean_object* v___x_3697_; uint8_t v___x_3698_; 
v___x_3696_ = l_Lean_Syntax_getArg(v___x_3653_, v___x_3584_);
lean_dec(v___x_3653_);
v___x_3697_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__2));
lean_inc(v___x_3696_);
v___x_3698_ = l_Lean_Syntax_isOfKind(v___x_3696_, v___x_3697_);
if (v___x_3698_ == 0)
{
lean_object* v___x_3699_; 
lean_dec(v___x_3696_);
v___x_3699_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3609_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_3699_) == 0)
{
lean_object* v_a_3700_; lean_object* v_a_3701_; lean_object* v___x_3703_; uint8_t v_isShared_3704_; uint8_t v_isSharedCheck_3728_; 
v_a_3700_ = lean_ctor_get(v___x_3699_, 0);
v_a_3701_ = lean_ctor_get(v___x_3699_, 1);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3703_ = v___x_3699_;
v_isShared_3704_ = v_isSharedCheck_3728_;
goto v_resetjp_3702_;
}
else
{
lean_inc(v_a_3701_);
lean_inc(v_a_3700_);
lean_dec(v___x_3699_);
v___x_3703_ = lean_box(0);
v_isShared_3704_ = v_isSharedCheck_3728_;
goto v_resetjp_3702_;
}
v_resetjp_3702_:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; lean_object* v___x_3719_; lean_object* v___x_3720_; lean_object* v___x_3721_; lean_object* v___x_3722_; lean_object* v___x_3723_; lean_object* v___x_3724_; lean_object* v___x_3726_; 
v___x_3705_ = l_Lean_SourceInfo_fromRef(v_a_3573_, v___x_3698_);
v___x_3706_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3707_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3705_, 10);
v___x_3708_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3708_, 0, v___x_3705_);
lean_ctor_set(v___x_3708_, 1, v___x_3707_);
v___x_3709_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_3710_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3705_);
lean_ctor_set(v___x_3710_, 1, v___x_3709_);
v___x_3711_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3712_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
v___x_3713_ = l_Lean_Syntax_node1(v___x_3705_, v___x_3712_, v___x_3599_);
v___x_3714_ = l_Lean_Syntax_node1(v___x_3705_, v___x_3711_, v___x_3713_);
v___x_3715_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3716_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3705_);
lean_ctor_set(v___x_3716_, 1, v___x_3711_);
lean_ctor_set(v___x_3716_, 2, v___x_3715_);
v___x_3717_ = l_Lean_Syntax_node2(v___x_3705_, v___x_3697_, v___x_3714_, v___x_3716_);
v___x_3718_ = l_Lean_Syntax_node1(v___x_3705_, v___x_3654_, v___x_3717_);
v___x_3719_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3720_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3720_, 0, v___x_3705_);
lean_ctor_set(v___x_3720_, 1, v___x_3719_);
v___x_3721_ = l_Lean_Syntax_node4(v___x_3705_, v___x_3610_, v___x_3710_, v___x_3718_, v___x_3720_, v_a_3700_);
v___x_3722_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3723_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3723_, 0, v___x_3705_);
lean_ctor_set(v___x_3723_, 1, v___x_3722_);
v___x_3724_ = l_Lean_Syntax_node3(v___x_3705_, v___x_3706_, v___x_3708_, v___x_3721_, v___x_3723_);
if (v_isShared_3704_ == 0)
{
lean_ctor_set(v___x_3703_, 0, v___x_3724_);
v___x_3726_ = v___x_3703_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v___x_3724_);
lean_ctor_set(v_reuseFailAlloc_3727_, 1, v_a_3701_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
else
{
lean_object* v_a_3729_; lean_object* v_a_3730_; lean_object* v___x_3732_; uint8_t v_isShared_3733_; uint8_t v_isSharedCheck_3737_; 
lean_dec(v___x_3599_);
v_a_3729_ = lean_ctor_get(v___x_3699_, 0);
v_a_3730_ = lean_ctor_get(v___x_3699_, 1);
v_isSharedCheck_3737_ = !lean_is_exclusive(v___x_3699_);
if (v_isSharedCheck_3737_ == 0)
{
v___x_3732_ = v___x_3699_;
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
else
{
lean_inc(v_a_3730_);
lean_inc(v_a_3729_);
lean_dec(v___x_3699_);
v___x_3732_ = lean_box(0);
v_isShared_3733_ = v_isSharedCheck_3737_;
goto v_resetjp_3731_;
}
v_resetjp_3731_:
{
lean_object* v___x_3735_; 
if (v_isShared_3733_ == 0)
{
v___x_3735_ = v___x_3732_;
goto v_reusejp_3734_;
}
else
{
lean_object* v_reuseFailAlloc_3736_; 
v_reuseFailAlloc_3736_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3736_, 0, v_a_3729_);
lean_ctor_set(v_reuseFailAlloc_3736_, 1, v_a_3730_);
v___x_3735_ = v_reuseFailAlloc_3736_;
goto v_reusejp_3734_;
}
v_reusejp_3734_:
{
return v___x_3735_;
}
}
}
}
else
{
lean_object* v___x_3738_; lean_object* v___x_3739_; uint8_t v___x_3740_; 
v___x_3738_ = l_Lean_Syntax_getArg(v___x_3696_, v___x_3584_);
v___x_3739_ = l_Lean_Syntax_getNumArgs(v___x_3738_);
v___x_3740_ = lean_nat_dec_le(v___x_3579_, v___x_3739_);
if (v___x_3740_ == 0)
{
lean_object* v___x_3741_; 
lean_dec(v___x_3739_);
lean_dec(v___x_3738_);
lean_dec(v___x_3696_);
v___x_3741_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3609_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_3741_) == 0)
{
lean_object* v_a_3742_; lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3770_; 
v_a_3742_ = lean_ctor_get(v___x_3741_, 0);
v_a_3743_ = lean_ctor_get(v___x_3741_, 1);
v_isSharedCheck_3770_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3770_ == 0)
{
v___x_3745_ = v___x_3741_;
v_isShared_3746_ = v_isSharedCheck_3770_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_inc(v_a_3742_);
lean_dec(v___x_3741_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3770_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v___x_3747_; lean_object* v___x_3748_; lean_object* v___x_3749_; lean_object* v___x_3750_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___x_3762_; lean_object* v___x_3763_; lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3768_; 
v___x_3747_ = l_Lean_SourceInfo_fromRef(v_a_3573_, v___x_3740_);
v___x_3748_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3749_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3747_, 10);
v___x_3750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3747_);
lean_ctor_set(v___x_3750_, 1, v___x_3749_);
v___x_3751_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_3752_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3752_, 0, v___x_3747_);
lean_ctor_set(v___x_3752_, 1, v___x_3751_);
v___x_3753_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3754_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
v___x_3755_ = l_Lean_Syntax_node1(v___x_3747_, v___x_3754_, v___x_3599_);
v___x_3756_ = l_Lean_Syntax_node1(v___x_3747_, v___x_3753_, v___x_3755_);
v___x_3757_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3758_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3747_);
lean_ctor_set(v___x_3758_, 1, v___x_3753_);
lean_ctor_set(v___x_3758_, 2, v___x_3757_);
v___x_3759_ = l_Lean_Syntax_node2(v___x_3747_, v___x_3697_, v___x_3756_, v___x_3758_);
v___x_3760_ = l_Lean_Syntax_node1(v___x_3747_, v___x_3654_, v___x_3759_);
v___x_3761_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3762_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3762_, 0, v___x_3747_);
lean_ctor_set(v___x_3762_, 1, v___x_3761_);
v___x_3763_ = l_Lean_Syntax_node4(v___x_3747_, v___x_3610_, v___x_3752_, v___x_3760_, v___x_3762_, v_a_3742_);
v___x_3764_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3765_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3747_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = l_Lean_Syntax_node3(v___x_3747_, v___x_3748_, v___x_3750_, v___x_3763_, v___x_3765_);
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 0, v___x_3766_);
v___x_3768_ = v___x_3745_;
goto v_reusejp_3767_;
}
else
{
lean_object* v_reuseFailAlloc_3769_; 
v_reuseFailAlloc_3769_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3769_, 0, v___x_3766_);
lean_ctor_set(v_reuseFailAlloc_3769_, 1, v_a_3743_);
v___x_3768_ = v_reuseFailAlloc_3769_;
goto v_reusejp_3767_;
}
v_reusejp_3767_:
{
return v___x_3768_;
}
}
}
else
{
lean_object* v_a_3771_; lean_object* v_a_3772_; lean_object* v___x_3774_; uint8_t v_isShared_3775_; uint8_t v_isSharedCheck_3779_; 
lean_dec(v___x_3599_);
v_a_3771_ = lean_ctor_get(v___x_3741_, 0);
v_a_3772_ = lean_ctor_get(v___x_3741_, 1);
v_isSharedCheck_3779_ = !lean_is_exclusive(v___x_3741_);
if (v_isSharedCheck_3779_ == 0)
{
v___x_3774_ = v___x_3741_;
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
else
{
lean_inc(v_a_3772_);
lean_inc(v_a_3771_);
lean_dec(v___x_3741_);
v___x_3774_ = lean_box(0);
v_isShared_3775_ = v_isSharedCheck_3779_;
goto v_resetjp_3773_;
}
v_resetjp_3773_:
{
lean_object* v___x_3777_; 
if (v_isShared_3775_ == 0)
{
v___x_3777_ = v___x_3774_;
goto v_reusejp_3776_;
}
else
{
lean_object* v_reuseFailAlloc_3778_; 
v_reuseFailAlloc_3778_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3778_, 0, v_a_3771_);
lean_ctor_set(v_reuseFailAlloc_3778_, 1, v_a_3772_);
v___x_3777_ = v_reuseFailAlloc_3778_;
goto v_reusejp_3776_;
}
v_reusejp_3776_:
{
return v___x_3777_;
}
}
}
}
else
{
lean_object* v___x_3780_; lean_object* v___x_3781_; uint8_t v___x_3782_; 
v___x_3780_ = l_Lean_Syntax_getArg(v___x_3738_, v___x_3584_);
v___x_3781_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
lean_inc(v___x_3780_);
v___x_3782_ = l_Lean_Syntax_isOfKind(v___x_3780_, v___x_3781_);
if (v___x_3782_ == 0)
{
lean_object* v___x_3783_; 
lean_dec(v___x_3780_);
lean_dec(v___x_3739_);
lean_dec(v___x_3738_);
lean_dec(v___x_3696_);
v___x_3783_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3609_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_3783_) == 0)
{
lean_object* v_a_3784_; lean_object* v_a_3785_; lean_object* v___x_3787_; uint8_t v_isShared_3788_; uint8_t v_isSharedCheck_3811_; 
v_a_3784_ = lean_ctor_get(v___x_3783_, 0);
v_a_3785_ = lean_ctor_get(v___x_3783_, 1);
v_isSharedCheck_3811_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3811_ == 0)
{
v___x_3787_ = v___x_3783_;
v_isShared_3788_ = v_isSharedCheck_3811_;
goto v_resetjp_3786_;
}
else
{
lean_inc(v_a_3785_);
lean_inc(v_a_3784_);
lean_dec(v___x_3783_);
v___x_3787_ = lean_box(0);
v_isShared_3788_ = v_isSharedCheck_3811_;
goto v_resetjp_3786_;
}
v_resetjp_3786_:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; lean_object* v___x_3791_; lean_object* v___x_3792_; lean_object* v___x_3793_; lean_object* v___x_3794_; lean_object* v___x_3795_; lean_object* v___x_3796_; lean_object* v___x_3797_; lean_object* v___x_3798_; lean_object* v___x_3799_; lean_object* v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3809_; 
v___x_3789_ = l_Lean_SourceInfo_fromRef(v_a_3573_, v___x_3782_);
v___x_3790_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3791_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3789_, 10);
v___x_3792_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3789_);
lean_ctor_set(v___x_3792_, 1, v___x_3791_);
v___x_3793_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_3794_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3794_, 0, v___x_3789_);
lean_ctor_set(v___x_3794_, 1, v___x_3793_);
v___x_3795_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3796_ = l_Lean_Syntax_node1(v___x_3789_, v___x_3781_, v___x_3599_);
v___x_3797_ = l_Lean_Syntax_node1(v___x_3789_, v___x_3795_, v___x_3796_);
v___x_3798_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3799_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3799_, 0, v___x_3789_);
lean_ctor_set(v___x_3799_, 1, v___x_3795_);
lean_ctor_set(v___x_3799_, 2, v___x_3798_);
v___x_3800_ = l_Lean_Syntax_node2(v___x_3789_, v___x_3697_, v___x_3797_, v___x_3799_);
v___x_3801_ = l_Lean_Syntax_node1(v___x_3789_, v___x_3654_, v___x_3800_);
v___x_3802_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3803_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3803_, 0, v___x_3789_);
lean_ctor_set(v___x_3803_, 1, v___x_3802_);
v___x_3804_ = l_Lean_Syntax_node4(v___x_3789_, v___x_3610_, v___x_3794_, v___x_3801_, v___x_3803_, v_a_3784_);
v___x_3805_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3806_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3789_);
lean_ctor_set(v___x_3806_, 1, v___x_3805_);
v___x_3807_ = l_Lean_Syntax_node3(v___x_3789_, v___x_3790_, v___x_3792_, v___x_3804_, v___x_3806_);
if (v_isShared_3788_ == 0)
{
lean_ctor_set(v___x_3787_, 0, v___x_3807_);
v___x_3809_ = v___x_3787_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3810_; 
v_reuseFailAlloc_3810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3810_, 0, v___x_3807_);
lean_ctor_set(v_reuseFailAlloc_3810_, 1, v_a_3785_);
v___x_3809_ = v_reuseFailAlloc_3810_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
return v___x_3809_;
}
}
}
else
{
lean_object* v_a_3812_; lean_object* v_a_3813_; lean_object* v___x_3815_; uint8_t v_isShared_3816_; uint8_t v_isSharedCheck_3820_; 
lean_dec(v___x_3599_);
v_a_3812_ = lean_ctor_get(v___x_3783_, 0);
v_a_3813_ = lean_ctor_get(v___x_3783_, 1);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3783_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3815_ = v___x_3783_;
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
else
{
lean_inc(v_a_3813_);
lean_inc(v_a_3812_);
lean_dec(v___x_3783_);
v___x_3815_ = lean_box(0);
v_isShared_3816_ = v_isSharedCheck_3820_;
goto v_resetjp_3814_;
}
v_resetjp_3814_:
{
lean_object* v___x_3818_; 
if (v_isShared_3816_ == 0)
{
v___x_3818_ = v___x_3815_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v_a_3812_);
lean_ctor_set(v_reuseFailAlloc_3819_, 1, v_a_3813_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
else
{
lean_object* v___x_3821_; uint8_t v___x_3822_; 
v___x_3821_ = l_Lean_Syntax_getArg(v___x_3780_, v___x_3584_);
lean_dec(v___x_3780_);
lean_inc(v___x_3821_);
v___x_3822_ = l_Lean_Syntax_isOfKind(v___x_3821_, v___x_3600_);
if (v___x_3822_ == 0)
{
lean_object* v___x_3823_; 
lean_dec(v___x_3821_);
lean_dec(v___x_3739_);
lean_dec(v___x_3738_);
lean_dec(v___x_3696_);
v___x_3823_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3609_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_3823_) == 0)
{
lean_object* v_a_3824_; lean_object* v_a_3825_; lean_object* v___x_3827_; uint8_t v_isShared_3828_; uint8_t v_isSharedCheck_3851_; 
v_a_3824_ = lean_ctor_get(v___x_3823_, 0);
v_a_3825_ = lean_ctor_get(v___x_3823_, 1);
v_isSharedCheck_3851_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3851_ == 0)
{
v___x_3827_ = v___x_3823_;
v_isShared_3828_ = v_isSharedCheck_3851_;
goto v_resetjp_3826_;
}
else
{
lean_inc(v_a_3825_);
lean_inc(v_a_3824_);
lean_dec(v___x_3823_);
v___x_3827_ = lean_box(0);
v_isShared_3828_ = v_isSharedCheck_3851_;
goto v_resetjp_3826_;
}
v_resetjp_3826_:
{
lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; lean_object* v___x_3837_; lean_object* v___x_3838_; lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3849_; 
v___x_3829_ = l_Lean_SourceInfo_fromRef(v_a_3573_, v___x_3822_);
v___x_3830_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3831_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3829_, 10);
v___x_3832_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3832_, 0, v___x_3829_);
lean_ctor_set(v___x_3832_, 1, v___x_3831_);
v___x_3833_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_3834_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3834_, 0, v___x_3829_);
lean_ctor_set(v___x_3834_, 1, v___x_3833_);
v___x_3835_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3836_ = l_Lean_Syntax_node1(v___x_3829_, v___x_3781_, v___x_3599_);
v___x_3837_ = l_Lean_Syntax_node1(v___x_3829_, v___x_3835_, v___x_3836_);
v___x_3838_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3839_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3839_, 0, v___x_3829_);
lean_ctor_set(v___x_3839_, 1, v___x_3835_);
lean_ctor_set(v___x_3839_, 2, v___x_3838_);
v___x_3840_ = l_Lean_Syntax_node2(v___x_3829_, v___x_3697_, v___x_3837_, v___x_3839_);
v___x_3841_ = l_Lean_Syntax_node1(v___x_3829_, v___x_3654_, v___x_3840_);
v___x_3842_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3843_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3829_);
lean_ctor_set(v___x_3843_, 1, v___x_3842_);
v___x_3844_ = l_Lean_Syntax_node4(v___x_3829_, v___x_3610_, v___x_3834_, v___x_3841_, v___x_3843_, v_a_3824_);
v___x_3845_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3846_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3829_);
lean_ctor_set(v___x_3846_, 1, v___x_3845_);
v___x_3847_ = l_Lean_Syntax_node3(v___x_3829_, v___x_3830_, v___x_3832_, v___x_3844_, v___x_3846_);
if (v_isShared_3828_ == 0)
{
lean_ctor_set(v___x_3827_, 0, v___x_3847_);
v___x_3849_ = v___x_3827_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v___x_3847_);
lean_ctor_set(v_reuseFailAlloc_3850_, 1, v_a_3825_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
return v___x_3849_;
}
}
}
else
{
lean_object* v_a_3852_; lean_object* v_a_3853_; lean_object* v___x_3855_; uint8_t v_isShared_3856_; uint8_t v_isSharedCheck_3860_; 
lean_dec(v___x_3599_);
v_a_3852_ = lean_ctor_get(v___x_3823_, 0);
v_a_3853_ = lean_ctor_get(v___x_3823_, 1);
v_isSharedCheck_3860_ = !lean_is_exclusive(v___x_3823_);
if (v_isSharedCheck_3860_ == 0)
{
v___x_3855_ = v___x_3823_;
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
else
{
lean_inc(v_a_3853_);
lean_inc(v_a_3852_);
lean_dec(v___x_3823_);
v___x_3855_ = lean_box(0);
v_isShared_3856_ = v_isSharedCheck_3860_;
goto v_resetjp_3854_;
}
v_resetjp_3854_:
{
lean_object* v___x_3858_; 
if (v_isShared_3856_ == 0)
{
v___x_3858_ = v___x_3855_;
goto v_reusejp_3857_;
}
else
{
lean_object* v_reuseFailAlloc_3859_; 
v_reuseFailAlloc_3859_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3859_, 0, v_a_3852_);
lean_ctor_set(v_reuseFailAlloc_3859_, 1, v_a_3853_);
v___x_3858_ = v_reuseFailAlloc_3859_;
goto v_reusejp_3857_;
}
v_reusejp_3857_:
{
return v___x_3858_;
}
}
}
}
else
{
lean_object* v___x_3861_; lean_object* v___x_3862_; lean_object* v___x_3863_; lean_object* v___x_3864_; lean_object* v___x_3865_; lean_object* v___x_3866_; size_t v_sz_3867_; size_t v___x_3868_; lean_object* v___x_3869_; 
v___x_3861_ = l_Lean_Syntax_getArgs(v___x_3738_);
lean_dec(v___x_3738_);
v___x_3862_ = l_Array_extract___redArg(v___x_3861_, v___x_3579_, v___x_3739_);
lean_dec_ref(v___x_3861_);
v___x_3863_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_3864_ = lean_box(2);
v___x_3865_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3865_, 0, v___x_3864_);
lean_ctor_set(v___x_3865_, 1, v___x_3863_);
lean_ctor_set(v___x_3865_, 2, v___x_3862_);
v___x_3866_ = l_Lean_Syntax_getArgs(v___x_3865_);
lean_dec_ref_known(v___x_3865_, 3);
v_sz_3867_ = lean_array_size(v___x_3866_);
v___x_3868_ = ((size_t)0ULL);
v___x_3869_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__0(v_sz_3867_, v___x_3868_, v___x_3866_);
if (lean_obj_tag(v___x_3869_) == 0)
{
lean_object* v___x_3870_; 
lean_dec(v___x_3821_);
lean_dec(v___x_3696_);
v___x_3870_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3609_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_3870_) == 0)
{
lean_object* v_a_3871_; lean_object* v_a_3872_; lean_object* v___x_3874_; uint8_t v_isShared_3875_; uint8_t v_isSharedCheck_3898_; 
v_a_3871_ = lean_ctor_get(v___x_3870_, 0);
v_a_3872_ = lean_ctor_get(v___x_3870_, 1);
v_isSharedCheck_3898_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3898_ == 0)
{
v___x_3874_ = v___x_3870_;
v_isShared_3875_ = v_isSharedCheck_3898_;
goto v_resetjp_3873_;
}
else
{
lean_inc(v_a_3872_);
lean_inc(v_a_3871_);
lean_dec(v___x_3870_);
v___x_3874_ = lean_box(0);
v_isShared_3875_ = v_isSharedCheck_3898_;
goto v_resetjp_3873_;
}
v_resetjp_3873_:
{
uint8_t v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; lean_object* v___x_3889_; lean_object* v___x_3890_; lean_object* v___x_3891_; lean_object* v___x_3892_; lean_object* v___x_3893_; lean_object* v___x_3894_; lean_object* v___x_3896_; 
v___x_3876_ = 0;
v___x_3877_ = l_Lean_SourceInfo_fromRef(v_a_3573_, v___x_3876_);
v___x_3878_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3879_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3877_, 10);
v___x_3880_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3877_);
lean_ctor_set(v___x_3880_, 1, v___x_3879_);
v___x_3881_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_3882_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3877_);
lean_ctor_set(v___x_3882_, 1, v___x_3881_);
v___x_3883_ = l_Lean_Syntax_node1(v___x_3877_, v___x_3781_, v___x_3599_);
v___x_3884_ = l_Lean_Syntax_node1(v___x_3877_, v___x_3863_, v___x_3883_);
v___x_3885_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3886_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3877_);
lean_ctor_set(v___x_3886_, 1, v___x_3863_);
lean_ctor_set(v___x_3886_, 2, v___x_3885_);
v___x_3887_ = l_Lean_Syntax_node2(v___x_3877_, v___x_3697_, v___x_3884_, v___x_3886_);
v___x_3888_ = l_Lean_Syntax_node1(v___x_3877_, v___x_3654_, v___x_3887_);
v___x_3889_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3890_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3890_, 0, v___x_3877_);
lean_ctor_set(v___x_3890_, 1, v___x_3889_);
v___x_3891_ = l_Lean_Syntax_node4(v___x_3877_, v___x_3610_, v___x_3882_, v___x_3888_, v___x_3890_, v_a_3871_);
v___x_3892_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3893_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3893_, 0, v___x_3877_);
lean_ctor_set(v___x_3893_, 1, v___x_3892_);
v___x_3894_ = l_Lean_Syntax_node3(v___x_3877_, v___x_3878_, v___x_3880_, v___x_3891_, v___x_3893_);
if (v_isShared_3875_ == 0)
{
lean_ctor_set(v___x_3874_, 0, v___x_3894_);
v___x_3896_ = v___x_3874_;
goto v_reusejp_3895_;
}
else
{
lean_object* v_reuseFailAlloc_3897_; 
v_reuseFailAlloc_3897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3897_, 0, v___x_3894_);
lean_ctor_set(v_reuseFailAlloc_3897_, 1, v_a_3872_);
v___x_3896_ = v_reuseFailAlloc_3897_;
goto v_reusejp_3895_;
}
v_reusejp_3895_:
{
return v___x_3896_;
}
}
}
else
{
lean_object* v_a_3899_; lean_object* v_a_3900_; lean_object* v___x_3902_; uint8_t v_isShared_3903_; uint8_t v_isSharedCheck_3907_; 
lean_dec(v___x_3599_);
v_a_3899_ = lean_ctor_get(v___x_3870_, 0);
v_a_3900_ = lean_ctor_get(v___x_3870_, 1);
v_isSharedCheck_3907_ = !lean_is_exclusive(v___x_3870_);
if (v_isSharedCheck_3907_ == 0)
{
v___x_3902_ = v___x_3870_;
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
else
{
lean_inc(v_a_3900_);
lean_inc(v_a_3899_);
lean_dec(v___x_3870_);
v___x_3902_ = lean_box(0);
v_isShared_3903_ = v_isSharedCheck_3907_;
goto v_resetjp_3901_;
}
v_resetjp_3901_:
{
lean_object* v___x_3905_; 
if (v_isShared_3903_ == 0)
{
v___x_3905_ = v___x_3902_;
goto v_reusejp_3904_;
}
else
{
lean_object* v_reuseFailAlloc_3906_; 
v_reuseFailAlloc_3906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3906_, 0, v_a_3899_);
lean_ctor_set(v_reuseFailAlloc_3906_, 1, v_a_3900_);
v___x_3905_ = v_reuseFailAlloc_3906_;
goto v_reusejp_3904_;
}
v_reusejp_3904_:
{
return v___x_3905_;
}
}
}
}
else
{
lean_object* v_val_3908_; lean_object* v___x_3909_; uint8_t v___x_3910_; 
v_val_3908_ = lean_ctor_get(v___x_3869_, 0);
lean_inc(v_val_3908_);
lean_dec_ref_known(v___x_3869_, 1);
v___x_3909_ = l_Lean_Syntax_getArg(v___x_3696_, v___x_3579_);
lean_dec(v___x_3696_);
v___x_3910_ = l_Lean_Syntax_matchesNull(v___x_3909_, v___x_3584_);
if (v___x_3910_ == 0)
{
lean_object* v___x_3911_; 
lean_dec(v_val_3908_);
lean_dec(v___x_3821_);
v___x_3911_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3609_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_3911_) == 0)
{
lean_object* v_a_3912_; lean_object* v_a_3913_; lean_object* v___x_3915_; uint8_t v_isShared_3916_; uint8_t v_isSharedCheck_3938_; 
v_a_3912_ = lean_ctor_get(v___x_3911_, 0);
v_a_3913_ = lean_ctor_get(v___x_3911_, 1);
v_isSharedCheck_3938_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3938_ == 0)
{
v___x_3915_ = v___x_3911_;
v_isShared_3916_ = v_isSharedCheck_3938_;
goto v_resetjp_3914_;
}
else
{
lean_inc(v_a_3913_);
lean_inc(v_a_3912_);
lean_dec(v___x_3911_);
v___x_3915_ = lean_box(0);
v_isShared_3916_ = v_isSharedCheck_3938_;
goto v_resetjp_3914_;
}
v_resetjp_3914_:
{
lean_object* v___x_3917_; lean_object* v___x_3918_; lean_object* v___x_3919_; lean_object* v___x_3920_; lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; lean_object* v___x_3924_; lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3936_; 
v___x_3917_ = l_Lean_SourceInfo_fromRef(v_a_3573_, v___x_3910_);
v___x_3918_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3919_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3917_, 10);
v___x_3920_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3920_, 0, v___x_3917_);
lean_ctor_set(v___x_3920_, 1, v___x_3919_);
v___x_3921_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_3922_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3922_, 0, v___x_3917_);
lean_ctor_set(v___x_3922_, 1, v___x_3921_);
v___x_3923_ = l_Lean_Syntax_node1(v___x_3917_, v___x_3781_, v___x_3599_);
v___x_3924_ = l_Lean_Syntax_node1(v___x_3917_, v___x_3863_, v___x_3923_);
v___x_3925_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3926_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3926_, 0, v___x_3917_);
lean_ctor_set(v___x_3926_, 1, v___x_3863_);
lean_ctor_set(v___x_3926_, 2, v___x_3925_);
v___x_3927_ = l_Lean_Syntax_node2(v___x_3917_, v___x_3697_, v___x_3924_, v___x_3926_);
v___x_3928_ = l_Lean_Syntax_node1(v___x_3917_, v___x_3654_, v___x_3927_);
v___x_3929_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3930_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3930_, 0, v___x_3917_);
lean_ctor_set(v___x_3930_, 1, v___x_3929_);
v___x_3931_ = l_Lean_Syntax_node4(v___x_3917_, v___x_3610_, v___x_3922_, v___x_3928_, v___x_3930_, v_a_3912_);
v___x_3932_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3933_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3917_);
lean_ctor_set(v___x_3933_, 1, v___x_3932_);
v___x_3934_ = l_Lean_Syntax_node3(v___x_3917_, v___x_3918_, v___x_3920_, v___x_3931_, v___x_3933_);
if (v_isShared_3916_ == 0)
{
lean_ctor_set(v___x_3915_, 0, v___x_3934_);
v___x_3936_ = v___x_3915_;
goto v_reusejp_3935_;
}
else
{
lean_object* v_reuseFailAlloc_3937_; 
v_reuseFailAlloc_3937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3937_, 0, v___x_3934_);
lean_ctor_set(v_reuseFailAlloc_3937_, 1, v_a_3913_);
v___x_3936_ = v_reuseFailAlloc_3937_;
goto v_reusejp_3935_;
}
v_reusejp_3935_:
{
return v___x_3936_;
}
}
}
else
{
lean_object* v_a_3939_; lean_object* v_a_3940_; lean_object* v___x_3942_; uint8_t v_isShared_3943_; uint8_t v_isSharedCheck_3947_; 
lean_dec(v___x_3599_);
v_a_3939_ = lean_ctor_get(v___x_3911_, 0);
v_a_3940_ = lean_ctor_get(v___x_3911_, 1);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3911_);
if (v_isSharedCheck_3947_ == 0)
{
v___x_3942_ = v___x_3911_;
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
else
{
lean_inc(v_a_3940_);
lean_inc(v_a_3939_);
lean_dec(v___x_3911_);
v___x_3942_ = lean_box(0);
v_isShared_3943_ = v_isSharedCheck_3947_;
goto v_resetjp_3941_;
}
v_resetjp_3941_:
{
lean_object* v___x_3945_; 
if (v_isShared_3943_ == 0)
{
v___x_3945_ = v___x_3942_;
goto v_reusejp_3944_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_a_3939_);
lean_ctor_set(v_reuseFailAlloc_3946_, 1, v_a_3940_);
v___x_3945_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3944_;
}
v_reusejp_3944_:
{
return v___x_3945_;
}
}
}
}
else
{
lean_object* v_00_u03a8_3948_; lean_object* v___x_3949_; 
v_00_u03a8_3948_ = l_Lean_Syntax_getArg(v_00_u03a8_3609_, v___x_3608_);
lean_dec(v_00_u03a8_3609_);
v___x_3949_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_3948_, v_a_3573_, v_a_3574_);
if (lean_obj_tag(v___x_3949_) == 0)
{
lean_object* v_a_3950_; lean_object* v_a_3951_; lean_object* v___x_3953_; uint8_t v_isShared_3954_; uint8_t v_isSharedCheck_3982_; 
v_a_3950_ = lean_ctor_get(v___x_3949_, 0);
v_a_3951_ = lean_ctor_get(v___x_3949_, 1);
v_isSharedCheck_3982_ = !lean_is_exclusive(v___x_3949_);
if (v_isSharedCheck_3982_ == 0)
{
v___x_3953_ = v___x_3949_;
v_isShared_3954_ = v_isSharedCheck_3982_;
goto v_resetjp_3952_;
}
else
{
lean_inc(v_a_3951_);
lean_inc(v_a_3950_);
lean_dec(v___x_3949_);
v___x_3953_ = lean_box(0);
v_isShared_3954_ = v_isSharedCheck_3982_;
goto v_resetjp_3952_;
}
v_resetjp_3952_:
{
uint8_t v___x_3955_; lean_object* v___x_3956_; lean_object* v___x_3957_; lean_object* v___x_3958_; lean_object* v___x_3959_; lean_object* v___x_3960_; lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3963_; lean_object* v___x_3964_; size_t v_sz_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; lean_object* v___x_3968_; lean_object* v___x_3969_; lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; lean_object* v___x_3973_; lean_object* v___x_3974_; lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3980_; 
v___x_3955_ = 0;
v___x_3956_ = l_Lean_SourceInfo_fromRef(v_a_3573_, v___x_3955_);
v___x_3957_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_3958_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_3956_, 12);
v___x_3959_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3959_, 0, v___x_3956_);
lean_ctor_set(v___x_3959_, 1, v___x_3958_);
v___x_3960_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_3961_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3961_, 0, v___x_3956_);
lean_ctor_set(v___x_3961_, 1, v___x_3960_);
v___x_3962_ = l_Lean_Syntax_node1(v___x_3956_, v___x_3781_, v___x_3599_);
v___x_3963_ = l_Lean_Syntax_node1(v___x_3956_, v___x_3781_, v___x_3821_);
v___x_3964_ = l_Array_mkArray2___redArg(v___x_3962_, v___x_3963_);
v_sz_3965_ = lean_array_size(v_val_3908_);
v___x_3966_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1(v___x_3956_, v_sz_3965_, v___x_3868_, v_val_3908_);
v___x_3967_ = l_Array_append___redArg(v___x_3964_, v___x_3966_);
lean_dec_ref(v___x_3966_);
v___x_3968_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3968_, 0, v___x_3956_);
lean_ctor_set(v___x_3968_, 1, v___x_3863_);
lean_ctor_set(v___x_3968_, 2, v___x_3967_);
v___x_3969_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_3970_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_3970_, 0, v___x_3956_);
lean_ctor_set(v___x_3970_, 1, v___x_3863_);
lean_ctor_set(v___x_3970_, 2, v___x_3969_);
v___x_3971_ = l_Lean_Syntax_node2(v___x_3956_, v___x_3697_, v___x_3968_, v___x_3970_);
v___x_3972_ = l_Lean_Syntax_node1(v___x_3956_, v___x_3654_, v___x_3971_);
v___x_3973_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_3974_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3974_, 0, v___x_3956_);
lean_ctor_set(v___x_3974_, 1, v___x_3973_);
v___x_3975_ = l_Lean_Syntax_node4(v___x_3956_, v___x_3610_, v___x_3961_, v___x_3972_, v___x_3974_, v_a_3950_);
v___x_3976_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_3977_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_3977_, 0, v___x_3956_);
lean_ctor_set(v___x_3977_, 1, v___x_3976_);
v___x_3978_ = l_Lean_Syntax_node3(v___x_3956_, v___x_3957_, v___x_3959_, v___x_3975_, v___x_3977_);
if (v_isShared_3954_ == 0)
{
lean_ctor_set(v___x_3953_, 0, v___x_3978_);
v___x_3980_ = v___x_3953_;
goto v_reusejp_3979_;
}
else
{
lean_object* v_reuseFailAlloc_3981_; 
v_reuseFailAlloc_3981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3981_, 0, v___x_3978_);
lean_ctor_set(v_reuseFailAlloc_3981_, 1, v_a_3951_);
v___x_3980_ = v_reuseFailAlloc_3981_;
goto v_reusejp_3979_;
}
v_reusejp_3979_:
{
return v___x_3980_;
}
}
}
else
{
lean_object* v_a_3983_; lean_object* v_a_3984_; lean_object* v___x_3986_; uint8_t v_isShared_3987_; uint8_t v_isSharedCheck_3991_; 
lean_dec(v_val_3908_);
lean_dec(v___x_3821_);
lean_dec(v___x_3599_);
v_a_3983_ = lean_ctor_get(v___x_3949_, 0);
v_a_3984_ = lean_ctor_get(v___x_3949_, 1);
v_isSharedCheck_3991_ = !lean_is_exclusive(v___x_3949_);
if (v_isSharedCheck_3991_ == 0)
{
v___x_3986_ = v___x_3949_;
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
else
{
lean_inc(v_a_3984_);
lean_inc(v_a_3983_);
lean_dec(v___x_3949_);
v___x_3986_ = lean_box(0);
v_isShared_3987_ = v_isSharedCheck_3991_;
goto v_resetjp_3985_;
}
v_resetjp_3985_:
{
lean_object* v___x_3989_; 
if (v_isShared_3987_ == 0)
{
v___x_3989_ = v___x_3986_;
goto v_reusejp_3988_;
}
else
{
lean_object* v_reuseFailAlloc_3990_; 
v_reuseFailAlloc_3990_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3990_, 0, v_a_3983_);
lean_ctor_set(v_reuseFailAlloc_3990_, 1, v_a_3984_);
v___x_3989_ = v_reuseFailAlloc_3990_;
goto v_reusejp_3988_;
}
v_reusejp_3988_:
{
return v___x_3989_;
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
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandExists___boxed(lean_object* v_x_3992_, lean_object* v_a_3993_, lean_object* v_a_3994_){
_start:
{
lean_object* v_res_3995_; 
v_res_3995_ = l_Std_Do_SPred_Notation_unexpandExists(v_x_3992_, v_a_3993_, v_a_3994_);
lean_dec(v_a_3993_);
return v_res_3995_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandIff(lean_object* v_x_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_){
_start:
{
lean_object* v___x_4000_; uint8_t v___x_4001_; 
v___x_4000_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_3997_);
v___x_4001_ = l_Lean_Syntax_isOfKind(v_x_3997_, v___x_4000_);
if (v___x_4001_ == 0)
{
lean_object* v___x_4002_; lean_object* v___x_4003_; 
lean_dec(v_x_3997_);
v___x_4002_ = lean_box(0);
v___x_4003_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4002_);
lean_ctor_set(v___x_4003_, 1, v_a_3999_);
return v___x_4003_;
}
else
{
lean_object* v___x_4004_; lean_object* v___x_4005_; lean_object* v___x_4006_; uint8_t v___x_4007_; 
v___x_4004_ = lean_unsigned_to_nat(1u);
v___x_4005_ = l_Lean_Syntax_getArg(v_x_3997_, v___x_4004_);
lean_dec(v_x_3997_);
v___x_4006_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_4005_);
v___x_4007_ = l_Lean_Syntax_matchesNull(v___x_4005_, v___x_4006_);
if (v___x_4007_ == 0)
{
lean_object* v___x_4008_; lean_object* v___x_4009_; 
lean_dec(v___x_4005_);
v___x_4008_ = lean_box(0);
v___x_4009_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_4009_, 0, v___x_4008_);
lean_ctor_set(v___x_4009_, 1, v_a_3999_);
return v___x_4009_;
}
else
{
lean_object* v___x_4010_; lean_object* v_P_4011_; lean_object* v___x_4012_; 
v___x_4010_ = lean_unsigned_to_nat(0u);
v_P_4011_ = l_Lean_Syntax_getArg(v___x_4005_, v___x_4010_);
v___x_4012_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_4011_, v_a_3998_, v_a_3999_);
if (lean_obj_tag(v___x_4012_) == 0)
{
lean_object* v_a_4013_; lean_object* v_a_4014_; lean_object* v_Q_4015_; lean_object* v___x_4016_; 
v_a_4013_ = lean_ctor_get(v___x_4012_, 0);
lean_inc(v_a_4013_);
v_a_4014_ = lean_ctor_get(v___x_4012_, 1);
lean_inc(v_a_4014_);
lean_dec_ref_known(v___x_4012_, 2);
v_Q_4015_ = l_Lean_Syntax_getArg(v___x_4005_, v___x_4004_);
lean_dec(v___x_4005_);
v___x_4016_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_4015_, v_a_3998_, v_a_4014_);
if (lean_obj_tag(v___x_4016_) == 0)
{
lean_object* v_a_4017_; lean_object* v_a_4018_; lean_object* v___x_4020_; uint8_t v_isShared_4021_; uint8_t v_isSharedCheck_4037_; 
v_a_4017_ = lean_ctor_get(v___x_4016_, 0);
v_a_4018_ = lean_ctor_get(v___x_4016_, 1);
v_isSharedCheck_4037_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4037_ == 0)
{
v___x_4020_ = v___x_4016_;
v_isShared_4021_ = v_isSharedCheck_4037_;
goto v_resetjp_4019_;
}
else
{
lean_inc(v_a_4018_);
lean_inc(v_a_4017_);
lean_dec(v___x_4016_);
v___x_4020_ = lean_box(0);
v_isShared_4021_ = v_isSharedCheck_4037_;
goto v_resetjp_4019_;
}
v_resetjp_4019_:
{
uint8_t v___x_4022_; lean_object* v___x_4023_; lean_object* v___x_4024_; lean_object* v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; lean_object* v___x_4035_; 
v___x_4022_ = 0;
v___x_4023_ = l_Lean_SourceInfo_fromRef(v_a_3998_, v___x_4022_);
v___x_4024_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_4025_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_4023_, 4);
v___x_4026_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4026_, 0, v___x_4023_);
lean_ctor_set(v___x_4026_, 1, v___x_4025_);
v___x_4027_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__9));
v___x_4028_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandIff___closed__0));
v___x_4029_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4029_, 0, v___x_4023_);
lean_ctor_set(v___x_4029_, 1, v___x_4028_);
v___x_4030_ = l_Lean_Syntax_node3(v___x_4023_, v___x_4027_, v_a_4013_, v___x_4029_, v_a_4017_);
v___x_4031_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_4032_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_4032_, 0, v___x_4023_);
lean_ctor_set(v___x_4032_, 1, v___x_4031_);
v___x_4033_ = l_Lean_Syntax_node3(v___x_4023_, v___x_4024_, v___x_4026_, v___x_4030_, v___x_4032_);
if (v_isShared_4021_ == 0)
{
lean_ctor_set(v___x_4020_, 0, v___x_4033_);
v___x_4035_ = v___x_4020_;
goto v_reusejp_4034_;
}
else
{
lean_object* v_reuseFailAlloc_4036_; 
v_reuseFailAlloc_4036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4036_, 0, v___x_4033_);
lean_ctor_set(v_reuseFailAlloc_4036_, 1, v_a_4018_);
v___x_4035_ = v_reuseFailAlloc_4036_;
goto v_reusejp_4034_;
}
v_reusejp_4034_:
{
return v___x_4035_;
}
}
}
else
{
lean_object* v_a_4038_; lean_object* v_a_4039_; lean_object* v___x_4041_; uint8_t v_isShared_4042_; uint8_t v_isSharedCheck_4046_; 
lean_dec(v_a_4013_);
v_a_4038_ = lean_ctor_get(v___x_4016_, 0);
v_a_4039_ = lean_ctor_get(v___x_4016_, 1);
v_isSharedCheck_4046_ = !lean_is_exclusive(v___x_4016_);
if (v_isSharedCheck_4046_ == 0)
{
v___x_4041_ = v___x_4016_;
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
else
{
lean_inc(v_a_4039_);
lean_inc(v_a_4038_);
lean_dec(v___x_4016_);
v___x_4041_ = lean_box(0);
v_isShared_4042_ = v_isSharedCheck_4046_;
goto v_resetjp_4040_;
}
v_resetjp_4040_:
{
lean_object* v___x_4044_; 
if (v_isShared_4042_ == 0)
{
v___x_4044_ = v___x_4041_;
goto v_reusejp_4043_;
}
else
{
lean_object* v_reuseFailAlloc_4045_; 
v_reuseFailAlloc_4045_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4045_, 0, v_a_4038_);
lean_ctor_set(v_reuseFailAlloc_4045_, 1, v_a_4039_);
v___x_4044_ = v_reuseFailAlloc_4045_;
goto v_reusejp_4043_;
}
v_reusejp_4043_:
{
return v___x_4044_;
}
}
}
}
else
{
lean_object* v_a_4047_; lean_object* v_a_4048_; lean_object* v___x_4050_; uint8_t v_isShared_4051_; uint8_t v_isSharedCheck_4055_; 
lean_dec(v___x_4005_);
v_a_4047_ = lean_ctor_get(v___x_4012_, 0);
v_a_4048_ = lean_ctor_get(v___x_4012_, 1);
v_isSharedCheck_4055_ = !lean_is_exclusive(v___x_4012_);
if (v_isSharedCheck_4055_ == 0)
{
v___x_4050_ = v___x_4012_;
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
else
{
lean_inc(v_a_4048_);
lean_inc(v_a_4047_);
lean_dec(v___x_4012_);
v___x_4050_ = lean_box(0);
v_isShared_4051_ = v_isSharedCheck_4055_;
goto v_resetjp_4049_;
}
v_resetjp_4049_:
{
lean_object* v___x_4053_; 
if (v_isShared_4051_ == 0)
{
v___x_4053_ = v___x_4050_;
goto v_reusejp_4052_;
}
else
{
lean_object* v_reuseFailAlloc_4054_; 
v_reuseFailAlloc_4054_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4054_, 0, v_a_4047_);
lean_ctor_set(v_reuseFailAlloc_4054_, 1, v_a_4048_);
v___x_4053_ = v_reuseFailAlloc_4054_;
goto v_reusejp_4052_;
}
v_reusejp_4052_:
{
return v___x_4053_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandIff___boxed(lean_object* v_x_4056_, lean_object* v_a_4057_, lean_object* v_a_4058_){
_start:
{
lean_object* v_res_4059_; 
v_res_4059_ = l_Std_Do_SPred_Notation_unexpandIff(v_x_4056_, v_a_4057_, v_a_4058_);
lean_dec(v_a_4057_);
return v_res_4059_;
}
}
lean_object* runtime_initialize_Std_Do_SPred_Notation_Basic(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Do_SPred_Notation(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
