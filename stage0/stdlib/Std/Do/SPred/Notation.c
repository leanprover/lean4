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
lean_object* l_Array_mkArray0___redArg();
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
v___x_338_ = l_Array_mkArray0___redArg();
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
lean_dec_ref_known(v___x_719_, 3);
v_xs_722_ = l_Lean_Syntax_getArgs(v___x_715_);
lean_dec_ref_known(v___x_715_, 3);
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
lean_dec(v___x_696_);
lean_inc(v_x_723_);
v___x_724_ = l_Lean_Syntax_isOfKind(v_x_723_, v___x_692_);
if (v___x_724_ == 0)
{
lean_dec(v_x_723_);
lean_dec(v_x_691_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_725_ = lean_unsigned_to_nat(2u);
v___x_726_ = l_Lean_Syntax_getArg(v_x_691_, v___x_725_);
lean_inc(v___x_726_);
v___x_727_ = l_Lean_Syntax_matchesNull(v___x_726_, v___x_725_);
if (v___x_727_ == 0)
{
lean_dec(v___x_726_);
lean_dec(v_x_723_);
lean_dec(v_x_691_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; uint8_t v___x_730_; 
v___x_728_ = lean_unsigned_to_nat(3u);
v___x_729_ = l_Lean_Syntax_getArg(v_x_691_, v___x_728_);
lean_dec(v_x_691_);
v___x_730_ = l_Lean_Syntax_matchesNull(v___x_729_, v___x_481_);
if (v___x_730_ == 0)
{
lean_dec(v___x_726_);
lean_dec(v_x_723_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_731_; uint8_t v___x_732_; 
v___x_731_ = l_Lean_Syntax_getArg(v___x_483_, v___x_725_);
v___x_732_ = l_Lean_Syntax_matchesNull(v___x_731_, v___x_481_);
if (v___x_732_ == 0)
{
lean_dec(v___x_726_);
lean_dec(v_x_723_);
lean_dec(v___x_689_);
lean_dec(v___x_687_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v_ty_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v_P_740_; lean_object* v_xs_741_; 
v_ty_733_ = l_Lean_Syntax_getArg(v___x_726_, v___x_482_);
lean_dec(v___x_726_);
v___x_734_ = lean_unsigned_to_nat(4u);
v___x_735_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_736_ = l_Array_extract___redArg(v___x_735_, v___x_482_, v___x_689_);
lean_dec_ref(v___x_735_);
v___x_737_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_738_ = lean_box(2);
v___x_739_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_739_, 0, v___x_738_);
lean_ctor_set(v___x_739_, 1, v___x_737_);
lean_ctor_set(v___x_739_, 2, v___x_736_);
v_P_740_ = l_Lean_Syntax_getArg(v___x_483_, v___x_734_);
lean_dec(v___x_483_);
v_xs_741_ = l_Lean_Syntax_getArgs(v___x_739_);
lean_dec_ref_known(v___x_739_, 3);
v_x_554_ = v_x_723_;
v_ty_555_ = v_ty_733_;
v_xs_556_ = v_xs_741_;
v_P_557_ = v_P_740_;
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
lean_object* v___x_742_; lean_object* v___x_743_; uint8_t v___x_744_; 
v___x_742_ = lean_unsigned_to_nat(2u);
v___x_743_ = l_Lean_Syntax_getArg(v___x_483_, v___x_742_);
v___x_744_ = l_Lean_Syntax_matchesNull(v___x_743_, v___x_481_);
if (v___x_744_ == 0)
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
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v_P_751_; lean_object* v_xs_752_; 
v___x_745_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_746_ = l_Array_extract___redArg(v___x_745_, v___x_482_, v___x_689_);
lean_dec_ref(v___x_745_);
v___x_747_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_748_ = lean_box(2);
v___x_749_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_749_, 0, v___x_748_);
lean_ctor_set(v___x_749_, 1, v___x_747_);
lean_ctor_set(v___x_749_, 2, v___x_746_);
v___x_750_ = lean_unsigned_to_nat(4u);
v_P_751_ = l_Lean_Syntax_getArg(v___x_483_, v___x_750_);
lean_dec(v___x_483_);
v_xs_752_ = l_Lean_Syntax_getArgs(v___x_749_);
lean_dec_ref_known(v___x_749_, 3);
v_x_498_ = v_x_691_;
v_xs_499_ = v_xs_752_;
v_P_500_ = v_P_751_;
v___y_501_ = v_a_471_;
v___y_502_ = v_a_472_;
goto v___jp_497_;
}
}
}
}
else
{
lean_object* v_x_753_; lean_object* v___x_754_; uint8_t v___x_755_; lean_object* v_x_757_; lean_object* v_ty_758_; lean_object* v_P_759_; lean_object* v___y_760_; lean_object* v___y_761_; 
v_x_753_ = l_Lean_Syntax_getArg(v___x_687_, v___x_481_);
v___x_754_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__62));
lean_inc(v_x_753_);
v___x_755_ = l_Lean_Syntax_isOfKind(v_x_753_, v___x_754_);
if (v___x_755_ == 0)
{
lean_object* v___x_808_; lean_object* v_____discr_810_; lean_object* v_____discr_811_; lean_object* v___y_812_; lean_object* v___y_813_; uint8_t v___x_866_; 
v___x_808_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__58));
lean_inc(v_x_753_);
v___x_866_ = l_Lean_Syntax_isOfKind(v_x_753_, v___x_808_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; uint8_t v___x_868_; 
lean_dec(v___x_687_);
v___x_867_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_753_);
v___x_868_ = l_Lean_Syntax_isOfKind(v_x_753_, v___x_867_);
if (v___x_868_ == 0)
{
lean_dec(v_x_753_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_869_; lean_object* v___x_870_; uint8_t v___x_871_; 
v___x_869_ = lean_unsigned_to_nat(2u);
v___x_870_ = l_Lean_Syntax_getArg(v___x_483_, v___x_869_);
v___x_871_ = l_Lean_Syntax_matchesNull(v___x_870_, v___x_481_);
if (v___x_871_ == 0)
{
lean_dec(v_x_753_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v_quotContext_872_; lean_object* v_currMacroScope_873_; lean_object* v_ref_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v_quotContext_872_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_873_ = lean_ctor_get(v_a_471_, 2);
v_ref_874_ = lean_ctor_get(v_a_471_, 5);
v___x_875_ = lean_unsigned_to_nat(4u);
v___x_876_ = l_Lean_Syntax_getArg(v___x_483_, v___x_875_);
lean_dec(v___x_483_);
v___x_877_ = l_Lean_SourceInfo_fromRef(v_ref_874_, v___x_866_);
v___x_878_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_879_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_880_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc_n(v_currMacroScope_873_, 2);
lean_inc_n(v_quotContext_872_, 2);
v___x_881_ = l_Lean_addMacroScope(v_quotContext_872_, v___x_880_, v_currMacroScope_873_);
v___x_882_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc_n(v___x_877_, 16);
v___x_883_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_883_, 0, v___x_877_);
lean_ctor_set(v___x_883_, 1, v___x_879_);
lean_ctor_set(v___x_883_, 2, v___x_881_);
lean_ctor_set(v___x_883_, 3, v___x_882_);
v___x_884_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_885_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_886_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_887_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
v___x_888_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_888_, 0, v___x_877_);
lean_ctor_set(v___x_888_, 1, v___x_887_);
v___x_889_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_890_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_891_ = lean_box(0);
v___x_892_ = l_Lean_addMacroScope(v_quotContext_872_, v___x_891_, v_currMacroScope_873_);
v___x_893_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
v___x_894_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_894_, 0, v___x_877_);
lean_ctor_set(v___x_894_, 1, v___x_890_);
lean_ctor_set(v___x_894_, 2, v___x_892_);
lean_ctor_set(v___x_894_, 3, v___x_893_);
v___x_895_ = l_Lean_Syntax_node1(v___x_877_, v___x_889_, v___x_894_);
v___x_896_ = l_Lean_Syntax_node2(v___x_877_, v___x_886_, v___x_888_, v___x_895_);
v___x_897_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_898_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
v___x_899_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_899_, 0, v___x_877_);
lean_ctor_set(v___x_899_, 1, v___x_897_);
v___x_900_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_901_ = l_Lean_Syntax_node1(v___x_877_, v___x_884_, v_x_753_);
v___x_902_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_903_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_903_, 0, v___x_877_);
lean_ctor_set(v___x_903_, 1, v___x_884_);
lean_ctor_set(v___x_903_, 2, v___x_902_);
v___x_904_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_905_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_905_, 0, v___x_877_);
lean_ctor_set(v___x_905_, 1, v___x_904_);
v___x_906_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_907_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_907_, 0, v___x_877_);
lean_ctor_set(v___x_907_, 1, v___x_906_);
v___x_908_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_909_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_909_, 0, v___x_877_);
lean_ctor_set(v___x_909_, 1, v___x_908_);
lean_inc_ref(v___x_909_);
v___x_910_ = l_Lean_Syntax_node3(v___x_877_, v___x_477_, v___x_907_, v___x_876_, v___x_909_);
v___x_911_ = l_Lean_Syntax_node4(v___x_877_, v___x_900_, v___x_901_, v___x_903_, v___x_905_, v___x_910_);
v___x_912_ = l_Lean_Syntax_node2(v___x_877_, v___x_898_, v___x_899_, v___x_911_);
v___x_913_ = l_Lean_Syntax_node3(v___x_877_, v___x_885_, v___x_896_, v___x_912_, v___x_909_);
v___x_914_ = l_Lean_Syntax_node1(v___x_877_, v___x_884_, v___x_913_);
v___x_915_ = l_Lean_Syntax_node2(v___x_877_, v___x_878_, v___x_883_, v___x_914_);
v___x_916_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_915_);
lean_ctor_set(v___x_916_, 1, v_a_472_);
return v___x_916_;
}
}
}
else
{
lean_object* v___x_917_; lean_object* v___x_918_; uint8_t v___x_919_; 
v___x_917_ = l_Lean_Syntax_getArg(v_x_753_, v___x_482_);
v___x_918_ = l_Lean_Syntax_getNumArgs(v___x_917_);
v___x_919_ = lean_nat_dec_le(v___x_482_, v___x_918_);
if (v___x_919_ == 0)
{
uint8_t v___x_920_; 
lean_dec(v___x_918_);
lean_inc(v___x_917_);
v___x_920_ = l_Lean_Syntax_matchesNull(v___x_917_, v___x_482_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
lean_dec(v___x_917_);
v___x_921_ = lean_unsigned_to_nat(2u);
v___x_922_ = lean_unsigned_to_nat(4u);
v___x_923_ = l_Lean_Syntax_getArg(v___x_483_, v___x_921_);
v___x_924_ = l_Lean_Syntax_getArg(v___x_483_, v___x_922_);
lean_dec(v___x_483_);
v_____discr_810_ = v___x_923_;
v_____discr_811_ = v___x_924_;
v___y_812_ = v_a_471_;
v___y_813_ = v_a_472_;
goto v___jp_809_;
}
else
{
lean_object* v_x_925_; lean_object* v___x_926_; uint8_t v___x_927_; 
v_x_925_ = l_Lean_Syntax_getArg(v___x_917_, v___x_481_);
lean_dec(v___x_917_);
v___x_926_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_925_);
v___x_927_ = l_Lean_Syntax_isOfKind(v_x_925_, v___x_926_);
if (v___x_927_ == 0)
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; 
lean_dec(v_x_925_);
v___x_928_ = lean_unsigned_to_nat(2u);
v___x_929_ = lean_unsigned_to_nat(4u);
v___x_930_ = l_Lean_Syntax_getArg(v___x_483_, v___x_928_);
v___x_931_ = l_Lean_Syntax_getArg(v___x_483_, v___x_929_);
lean_dec(v___x_483_);
v_____discr_810_ = v___x_930_;
v_____discr_811_ = v___x_931_;
v___y_812_ = v_a_471_;
v___y_813_ = v_a_472_;
goto v___jp_809_;
}
else
{
lean_object* v___x_932_; lean_object* v___x_933_; uint8_t v___x_934_; 
v___x_932_ = lean_unsigned_to_nat(2u);
v___x_933_ = l_Lean_Syntax_getArg(v_x_753_, v___x_932_);
lean_inc(v___x_933_);
v___x_934_ = l_Lean_Syntax_matchesNull(v___x_933_, v___x_932_);
if (v___x_934_ == 0)
{
lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; 
lean_dec(v___x_933_);
lean_dec(v_x_925_);
v___x_935_ = lean_unsigned_to_nat(4u);
v___x_936_ = l_Lean_Syntax_getArg(v___x_483_, v___x_932_);
v___x_937_ = l_Lean_Syntax_getArg(v___x_483_, v___x_935_);
lean_dec(v___x_483_);
v_____discr_810_ = v___x_936_;
v_____discr_811_ = v___x_937_;
v___y_812_ = v_a_471_;
v___y_813_ = v_a_472_;
goto v___jp_809_;
}
else
{
lean_object* v___x_938_; lean_object* v___x_939_; uint8_t v___x_940_; 
v___x_938_ = lean_unsigned_to_nat(3u);
v___x_939_ = l_Lean_Syntax_getArg(v_x_753_, v___x_938_);
v___x_940_ = l_Lean_Syntax_matchesNull(v___x_939_, v___x_481_);
if (v___x_940_ == 0)
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec(v___x_933_);
lean_dec(v_x_925_);
v___x_941_ = lean_unsigned_to_nat(4u);
v___x_942_ = l_Lean_Syntax_getArg(v___x_483_, v___x_932_);
v___x_943_ = l_Lean_Syntax_getArg(v___x_483_, v___x_941_);
lean_dec(v___x_483_);
v_____discr_810_ = v___x_942_;
v_____discr_811_ = v___x_943_;
v___y_812_ = v_a_471_;
v___y_813_ = v_a_472_;
goto v___jp_809_;
}
else
{
lean_object* v___x_944_; lean_object* v___x_945_; uint8_t v___x_946_; 
v___x_944_ = lean_unsigned_to_nat(4u);
v___x_945_ = l_Lean_Syntax_getArg(v___x_483_, v___x_932_);
lean_inc(v___x_945_);
v___x_946_ = l_Lean_Syntax_matchesNull(v___x_945_, v___x_481_);
if (v___x_946_ == 0)
{
lean_object* v___x_947_; 
lean_dec(v___x_933_);
lean_dec(v_x_925_);
v___x_947_ = l_Lean_Syntax_getArg(v___x_483_, v___x_944_);
lean_dec(v___x_483_);
v_____discr_810_ = v___x_945_;
v_____discr_811_ = v___x_947_;
v___y_812_ = v_a_471_;
v___y_813_ = v_a_472_;
goto v___jp_809_;
}
else
{
lean_object* v_ty_948_; lean_object* v_P_949_; 
lean_dec(v___x_945_);
lean_dec(v_x_753_);
lean_dec(v___x_687_);
v_ty_948_ = l_Lean_Syntax_getArg(v___x_933_, v___x_482_);
lean_dec(v___x_933_);
v_P_949_ = l_Lean_Syntax_getArg(v___x_483_, v___x_944_);
lean_dec(v___x_483_);
v_x_757_ = v_x_925_;
v_ty_758_ = v_ty_948_;
v_P_759_ = v_P_949_;
v___y_760_ = v_a_471_;
v___y_761_ = v_a_472_;
goto v___jp_756_;
}
}
}
}
}
}
else
{
lean_object* v_x_950_; uint8_t v___x_951_; 
v_x_950_ = l_Lean_Syntax_getArg(v___x_917_, v___x_481_);
lean_inc(v_x_950_);
v___x_951_ = l_Lean_Syntax_isOfKind(v_x_950_, v___x_754_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v_P_958_; uint8_t v___x_959_; 
v___x_952_ = lean_unsigned_to_nat(2u);
v___x_953_ = l_Lean_Syntax_getArg(v_x_753_, v___x_952_);
v___x_954_ = lean_unsigned_to_nat(3u);
v___x_955_ = l_Lean_Syntax_getArg(v_x_753_, v___x_954_);
v___x_956_ = lean_unsigned_to_nat(4u);
v___x_957_ = l_Lean_Syntax_getArg(v___x_483_, v___x_952_);
v_P_958_ = l_Lean_Syntax_getArg(v___x_483_, v___x_956_);
lean_dec(v___x_483_);
lean_inc(v___x_917_);
v___x_959_ = l_Lean_Syntax_matchesNull(v___x_917_, v___x_482_);
if (v___x_959_ == 0)
{
lean_object* v___x_960_; uint8_t v___x_961_; 
v___x_960_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_950_);
v___x_961_ = l_Lean_Syntax_isOfKind(v_x_950_, v___x_960_);
if (v___x_961_ == 0)
{
lean_dec(v___x_955_);
lean_dec(v___x_953_);
lean_dec(v_x_950_);
lean_dec(v___x_918_);
lean_dec(v___x_917_);
v_____discr_810_ = v___x_957_;
v_____discr_811_ = v_P_958_;
v___y_812_ = v_a_471_;
v___y_813_ = v_a_472_;
goto v___jp_809_;
}
else
{
uint8_t v___x_962_; 
lean_inc(v___x_953_);
v___x_962_ = l_Lean_Syntax_matchesNull(v___x_953_, v___x_952_);
if (v___x_962_ == 0)
{
lean_dec(v___x_955_);
lean_dec(v___x_953_);
lean_dec(v_x_950_);
lean_dec(v___x_918_);
lean_dec(v___x_917_);
v_____discr_810_ = v___x_957_;
v_____discr_811_ = v_P_958_;
v___y_812_ = v_a_471_;
v___y_813_ = v_a_472_;
goto v___jp_809_;
}
else
{
uint8_t v___x_963_; 
v___x_963_ = l_Lean_Syntax_matchesNull(v___x_955_, v___x_481_);
if (v___x_963_ == 0)
{
lean_dec(v___x_953_);
lean_dec(v_x_950_);
lean_dec(v___x_918_);
lean_dec(v___x_917_);
v_____discr_810_ = v___x_957_;
v_____discr_811_ = v_P_958_;
v___y_812_ = v_a_471_;
v___y_813_ = v_a_472_;
goto v___jp_809_;
}
else
{
uint8_t v___x_964_; 
lean_inc(v___x_957_);
v___x_964_ = l_Lean_Syntax_matchesNull(v___x_957_, v___x_481_);
if (v___x_964_ == 0)
{
lean_dec(v___x_953_);
lean_dec(v_x_950_);
lean_dec(v___x_918_);
lean_dec(v___x_917_);
v_____discr_810_ = v___x_957_;
v_____discr_811_ = v_P_958_;
v___y_812_ = v_a_471_;
v___y_813_ = v_a_472_;
goto v___jp_809_;
}
else
{
lean_object* v_quotContext_965_; lean_object* v_currMacroScope_966_; lean_object* v_ref_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v_ty_973_; lean_object* v_xs_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
lean_dec(v___x_957_);
lean_dec(v_x_753_);
lean_dec(v___x_687_);
v_quotContext_965_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_966_ = lean_ctor_get(v_a_471_, 2);
v_ref_967_ = lean_ctor_get(v_a_471_, 5);
v___x_968_ = l_Lean_Syntax_getArgs(v___x_917_);
lean_dec(v___x_917_);
v___x_969_ = l_Array_extract___redArg(v___x_968_, v___x_482_, v___x_918_);
lean_dec_ref(v___x_968_);
v___x_970_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_971_ = lean_box(2);
v___x_972_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_972_, 0, v___x_971_);
lean_ctor_set(v___x_972_, 1, v___x_970_);
lean_ctor_set(v___x_972_, 2, v___x_969_);
v_ty_973_ = l_Lean_Syntax_getArg(v___x_953_, v___x_482_);
lean_dec(v___x_953_);
v_xs_974_ = l_Lean_Syntax_getArgs(v___x_972_);
lean_dec_ref_known(v___x_972_, 3);
v___x_975_ = l_Lean_SourceInfo_fromRef(v_ref_967_, v___x_755_);
v___x_976_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_977_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_978_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc_n(v_currMacroScope_966_, 2);
lean_inc_n(v_quotContext_965_, 2);
v___x_979_ = l_Lean_addMacroScope(v_quotContext_965_, v___x_978_, v_currMacroScope_966_);
v___x_980_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc_n(v___x_975_, 26);
v___x_981_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_981_, 0, v___x_975_);
lean_ctor_set(v___x_981_, 1, v___x_977_);
lean_ctor_set(v___x_981_, 2, v___x_979_);
lean_ctor_set(v___x_981_, 3, v___x_980_);
v___x_982_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_983_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_984_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
v___x_985_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_975_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_987_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_988_ = lean_box(0);
v___x_989_ = l_Lean_addMacroScope(v_quotContext_965_, v___x_988_, v_currMacroScope_966_);
v___x_990_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
v___x_991_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_991_, 0, v___x_975_);
lean_ctor_set(v___x_991_, 1, v___x_987_);
lean_ctor_set(v___x_991_, 2, v___x_989_);
lean_ctor_set(v___x_991_, 3, v___x_990_);
v___x_992_ = l_Lean_Syntax_node1(v___x_975_, v___x_986_, v___x_991_);
lean_inc_ref(v___x_985_);
v___x_993_ = l_Lean_Syntax_node2(v___x_975_, v___x_983_, v___x_985_, v___x_992_);
v___x_994_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_995_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
v___x_996_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_996_, 0, v___x_975_);
lean_ctor_set(v___x_996_, 1, v___x_994_);
v___x_997_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_998_ = l_Lean_Syntax_node1(v___x_975_, v___x_970_, v_x_950_);
v___x_999_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55));
v___x_1000_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
v___x_1001_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1001_, 0, v___x_975_);
lean_ctor_set(v___x_1001_, 1, v___x_1000_);
lean_inc(v_ty_973_);
lean_inc_ref(v___x_1001_);
v___x_1002_ = l_Lean_Syntax_node2(v___x_975_, v___x_999_, v___x_1001_, v_ty_973_);
v___x_1003_ = l_Lean_Syntax_node1(v___x_975_, v___x_970_, v___x_1002_);
v___x_1004_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_1005_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1005_, 0, v___x_975_);
lean_ctor_set(v___x_1005_, 1, v___x_1004_);
v___x_1006_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_1007_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1007_, 0, v___x_975_);
lean_ctor_set(v___x_1007_, 1, v___x_1006_);
v___x_1008_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_1009_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1009_, 0, v___x_975_);
lean_ctor_set(v___x_1009_, 1, v___x_1008_);
v___x_1010_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_1011_ = l_Array_append___redArg(v___x_1010_, v_xs_974_);
lean_dec_ref(v_xs_974_);
v___x_1012_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1012_, 0, v___x_975_);
lean_ctor_set(v___x_1012_, 1, v___x_970_);
lean_ctor_set(v___x_1012_, 2, v___x_1011_);
v___x_1013_ = l_Lean_Syntax_node2(v___x_975_, v___x_970_, v___x_1001_, v_ty_973_);
v___x_1014_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1014_, 0, v___x_975_);
lean_ctor_set(v___x_1014_, 1, v___x_970_);
lean_ctor_set(v___x_1014_, 2, v___x_1010_);
v___x_1015_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1016_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1016_, 0, v___x_975_);
lean_ctor_set(v___x_1016_, 1, v___x_1015_);
lean_inc_ref_n(v___x_1016_, 2);
lean_inc_ref(v___x_1014_);
v___x_1017_ = l_Lean_Syntax_node5(v___x_975_, v___x_808_, v___x_985_, v___x_1012_, v___x_1013_, v___x_1014_, v___x_1016_);
v___x_1018_ = l_Lean_Syntax_node1(v___x_975_, v___x_970_, v___x_1017_);
v___x_1019_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_1020_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1020_, 0, v___x_975_);
lean_ctor_set(v___x_1020_, 1, v___x_1019_);
v___x_1021_ = l_Lean_Syntax_node5(v___x_975_, v___x_496_, v___x_1009_, v___x_1018_, v___x_1014_, v___x_1020_, v_P_958_);
v___x_1022_ = l_Lean_Syntax_node3(v___x_975_, v___x_477_, v___x_1007_, v___x_1021_, v___x_1016_);
v___x_1023_ = l_Lean_Syntax_node4(v___x_975_, v___x_997_, v___x_998_, v___x_1003_, v___x_1005_, v___x_1022_);
v___x_1024_ = l_Lean_Syntax_node2(v___x_975_, v___x_995_, v___x_996_, v___x_1023_);
v___x_1025_ = l_Lean_Syntax_node3(v___x_975_, v___x_982_, v___x_993_, v___x_1024_, v___x_1016_);
v___x_1026_ = l_Lean_Syntax_node1(v___x_975_, v___x_970_, v___x_1025_);
v___x_1027_ = l_Lean_Syntax_node2(v___x_975_, v___x_976_, v___x_981_, v___x_1026_);
v___x_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1028_, 0, v___x_1027_);
lean_ctor_set(v___x_1028_, 1, v_a_472_);
return v___x_1028_;
}
}
}
}
}
else
{
lean_object* v___x_1029_; uint8_t v___x_1030_; 
lean_dec(v___x_918_);
lean_dec(v___x_917_);
v___x_1029_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_950_);
v___x_1030_ = l_Lean_Syntax_isOfKind(v_x_950_, v___x_1029_);
if (v___x_1030_ == 0)
{
lean_dec(v___x_955_);
lean_dec(v___x_953_);
lean_dec(v_x_950_);
v_____discr_810_ = v___x_957_;
v_____discr_811_ = v_P_958_;
v___y_812_ = v_a_471_;
v___y_813_ = v_a_472_;
goto v___jp_809_;
}
else
{
uint8_t v___x_1031_; 
lean_inc(v___x_953_);
v___x_1031_ = l_Lean_Syntax_matchesNull(v___x_953_, v___x_952_);
if (v___x_1031_ == 0)
{
lean_dec(v___x_955_);
lean_dec(v___x_953_);
lean_dec(v_x_950_);
v_____discr_810_ = v___x_957_;
v_____discr_811_ = v_P_958_;
v___y_812_ = v_a_471_;
v___y_813_ = v_a_472_;
goto v___jp_809_;
}
else
{
uint8_t v___x_1032_; 
v___x_1032_ = l_Lean_Syntax_matchesNull(v___x_955_, v___x_481_);
if (v___x_1032_ == 0)
{
lean_dec(v___x_953_);
lean_dec(v_x_950_);
v_____discr_810_ = v___x_957_;
v_____discr_811_ = v_P_958_;
v___y_812_ = v_a_471_;
v___y_813_ = v_a_472_;
goto v___jp_809_;
}
else
{
uint8_t v___x_1033_; 
lean_inc(v___x_957_);
v___x_1033_ = l_Lean_Syntax_matchesNull(v___x_957_, v___x_481_);
if (v___x_1033_ == 0)
{
lean_dec(v___x_953_);
lean_dec(v_x_950_);
v_____discr_810_ = v___x_957_;
v_____discr_811_ = v_P_958_;
v___y_812_ = v_a_471_;
v___y_813_ = v_a_472_;
goto v___jp_809_;
}
else
{
lean_object* v_ty_1034_; 
lean_dec(v___x_957_);
lean_dec(v_x_753_);
lean_dec(v___x_687_);
v_ty_1034_ = l_Lean_Syntax_getArg(v___x_953_, v___x_482_);
lean_dec(v___x_953_);
v_x_757_ = v_x_950_;
v_ty_758_ = v_ty_1034_;
v_P_759_ = v_P_958_;
v___y_760_ = v_a_471_;
v___y_761_ = v_a_472_;
goto v___jp_756_;
}
}
}
}
}
}
else
{
lean_object* v___x_1035_; lean_object* v___x_1036_; uint8_t v___x_1037_; 
v___x_1035_ = lean_unsigned_to_nat(2u);
v___x_1036_ = l_Lean_Syntax_getArg(v_x_753_, v___x_1035_);
lean_inc(v___x_1036_);
v___x_1037_ = l_Lean_Syntax_matchesNull(v___x_1036_, v___x_1035_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; 
lean_dec(v___x_1036_);
lean_dec(v_x_950_);
lean_dec(v___x_918_);
lean_dec(v___x_917_);
v___x_1038_ = lean_unsigned_to_nat(4u);
v___x_1039_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1035_);
v___x_1040_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1038_);
lean_dec(v___x_483_);
v_____discr_810_ = v___x_1039_;
v_____discr_811_ = v___x_1040_;
v___y_812_ = v_a_471_;
v___y_813_ = v_a_472_;
goto v___jp_809_;
}
else
{
lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; 
v___x_1041_ = lean_unsigned_to_nat(3u);
v___x_1042_ = l_Lean_Syntax_getArg(v_x_753_, v___x_1041_);
v___x_1043_ = l_Lean_Syntax_matchesNull(v___x_1042_, v___x_481_);
if (v___x_1043_ == 0)
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; 
lean_dec(v___x_1036_);
lean_dec(v_x_950_);
lean_dec(v___x_918_);
lean_dec(v___x_917_);
v___x_1044_ = lean_unsigned_to_nat(4u);
v___x_1045_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1035_);
v___x_1046_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1044_);
lean_dec(v___x_483_);
v_____discr_810_ = v___x_1045_;
v_____discr_811_ = v___x_1046_;
v___y_812_ = v_a_471_;
v___y_813_ = v_a_472_;
goto v___jp_809_;
}
else
{
lean_object* v___x_1047_; lean_object* v___x_1048_; uint8_t v___x_1049_; 
v___x_1047_ = lean_unsigned_to_nat(4u);
v___x_1048_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1035_);
lean_inc(v___x_1048_);
v___x_1049_ = l_Lean_Syntax_matchesNull(v___x_1048_, v___x_481_);
if (v___x_1049_ == 0)
{
lean_object* v___x_1050_; 
lean_dec(v___x_1036_);
lean_dec(v_x_950_);
lean_dec(v___x_918_);
lean_dec(v___x_917_);
v___x_1050_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1047_);
lean_dec(v___x_483_);
v_____discr_810_ = v___x_1048_;
v_____discr_811_ = v___x_1050_;
v___y_812_ = v_a_471_;
v___y_813_ = v_a_472_;
goto v___jp_809_;
}
else
{
lean_object* v_quotContext_1051_; lean_object* v_currMacroScope_1052_; lean_object* v_ref_1053_; lean_object* v_tk_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v_xs_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_dec(v___x_1048_);
lean_dec(v_x_753_);
lean_dec(v___x_687_);
v_quotContext_1051_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_1052_ = lean_ctor_get(v_a_471_, 2);
v_ref_1053_ = lean_ctor_get(v_a_471_, 5);
v_tk_1054_ = l_Lean_Syntax_getArg(v_x_950_, v___x_481_);
lean_dec(v_x_950_);
v___x_1055_ = l_Lean_Syntax_getArgs(v___x_917_);
lean_dec(v___x_917_);
v___x_1056_ = l_Array_extract___redArg(v___x_1055_, v___x_482_, v___x_918_);
lean_dec_ref(v___x_1055_);
v___x_1057_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1058_ = lean_box(2);
v___x_1059_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1059_, 0, v___x_1058_);
lean_ctor_set(v___x_1059_, 1, v___x_1057_);
lean_ctor_set(v___x_1059_, 2, v___x_1056_);
v___x_1060_ = l_Lean_Syntax_getArg(v___x_1036_, v___x_482_);
lean_dec(v___x_1036_);
v___x_1061_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1047_);
lean_dec(v___x_483_);
v_xs_1062_ = l_Lean_Syntax_getArgs(v___x_1059_);
lean_dec_ref_known(v___x_1059_, 3);
v___x_1063_ = l_Lean_SourceInfo_fromRef(v_ref_1053_, v___x_755_);
v___x_1064_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_1065_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_1066_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc_n(v_currMacroScope_1052_, 2);
lean_inc_n(v_quotContext_1051_, 2);
v___x_1067_ = l_Lean_addMacroScope(v_quotContext_1051_, v___x_1066_, v_currMacroScope_1052_);
v___x_1068_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc_n(v___x_1063_, 27);
v___x_1069_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1069_, 0, v___x_1063_);
lean_ctor_set(v___x_1069_, 1, v___x_1065_);
lean_ctor_set(v___x_1069_, 2, v___x_1067_);
lean_ctor_set(v___x_1069_, 3, v___x_1068_);
v___x_1070_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_1071_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_1072_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
v___x_1073_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1063_);
lean_ctor_set(v___x_1073_, 1, v___x_1072_);
v___x_1074_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_1075_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_1076_ = lean_box(0);
v___x_1077_ = l_Lean_addMacroScope(v_quotContext_1051_, v___x_1076_, v_currMacroScope_1052_);
v___x_1078_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
v___x_1079_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1063_);
lean_ctor_set(v___x_1079_, 1, v___x_1075_);
lean_ctor_set(v___x_1079_, 2, v___x_1077_);
lean_ctor_set(v___x_1079_, 3, v___x_1078_);
v___x_1080_ = l_Lean_Syntax_node1(v___x_1063_, v___x_1074_, v___x_1079_);
lean_inc_ref(v___x_1073_);
v___x_1081_ = l_Lean_Syntax_node2(v___x_1063_, v___x_1071_, v___x_1073_, v___x_1080_);
v___x_1082_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_1083_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
v___x_1084_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1084_, 0, v___x_1063_);
lean_ctor_set(v___x_1084_, 1, v___x_1082_);
v___x_1085_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_1086_ = l_Lean_SourceInfo_fromRef(v_tk_1054_, v___x_688_);
lean_dec(v_tk_1054_);
v___x_1087_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__63));
v___x_1088_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1088_, 0, v___x_1086_);
lean_ctor_set(v___x_1088_, 1, v___x_1087_);
v___x_1089_ = l_Lean_Syntax_node1(v___x_1063_, v___x_754_, v___x_1088_);
v___x_1090_ = l_Lean_Syntax_node1(v___x_1063_, v___x_1057_, v___x_1089_);
v___x_1091_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55));
v___x_1092_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
v___x_1093_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1063_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
lean_inc(v___x_1060_);
lean_inc_ref(v___x_1093_);
v___x_1094_ = l_Lean_Syntax_node2(v___x_1063_, v___x_1091_, v___x_1093_, v___x_1060_);
v___x_1095_ = l_Lean_Syntax_node1(v___x_1063_, v___x_1057_, v___x_1094_);
v___x_1096_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_1097_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1063_);
lean_ctor_set(v___x_1097_, 1, v___x_1096_);
v___x_1098_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_1099_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1099_, 0, v___x_1063_);
lean_ctor_set(v___x_1099_, 1, v___x_1098_);
v___x_1100_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_1101_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1101_, 0, v___x_1063_);
lean_ctor_set(v___x_1101_, 1, v___x_1100_);
v___x_1102_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_1103_ = l_Array_append___redArg(v___x_1102_, v_xs_1062_);
lean_dec_ref(v_xs_1062_);
v___x_1104_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1063_);
lean_ctor_set(v___x_1104_, 1, v___x_1057_);
lean_ctor_set(v___x_1104_, 2, v___x_1103_);
v___x_1105_ = l_Lean_Syntax_node2(v___x_1063_, v___x_1057_, v___x_1093_, v___x_1060_);
v___x_1106_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1106_, 0, v___x_1063_);
lean_ctor_set(v___x_1106_, 1, v___x_1057_);
lean_ctor_set(v___x_1106_, 2, v___x_1102_);
v___x_1107_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1108_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1063_);
lean_ctor_set(v___x_1108_, 1, v___x_1107_);
lean_inc_ref_n(v___x_1108_, 2);
lean_inc_ref(v___x_1106_);
v___x_1109_ = l_Lean_Syntax_node5(v___x_1063_, v___x_808_, v___x_1073_, v___x_1104_, v___x_1105_, v___x_1106_, v___x_1108_);
v___x_1110_ = l_Lean_Syntax_node1(v___x_1063_, v___x_1057_, v___x_1109_);
v___x_1111_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_1112_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1112_, 0, v___x_1063_);
lean_ctor_set(v___x_1112_, 1, v___x_1111_);
v___x_1113_ = l_Lean_Syntax_node5(v___x_1063_, v___x_496_, v___x_1101_, v___x_1110_, v___x_1106_, v___x_1112_, v___x_1061_);
v___x_1114_ = l_Lean_Syntax_node3(v___x_1063_, v___x_477_, v___x_1099_, v___x_1113_, v___x_1108_);
v___x_1115_ = l_Lean_Syntax_node4(v___x_1063_, v___x_1085_, v___x_1090_, v___x_1095_, v___x_1097_, v___x_1114_);
v___x_1116_ = l_Lean_Syntax_node2(v___x_1063_, v___x_1083_, v___x_1084_, v___x_1115_);
v___x_1117_ = l_Lean_Syntax_node3(v___x_1063_, v___x_1070_, v___x_1081_, v___x_1116_, v___x_1108_);
v___x_1118_ = l_Lean_Syntax_node1(v___x_1063_, v___x_1057_, v___x_1117_);
v___x_1119_ = l_Lean_Syntax_node2(v___x_1063_, v___x_1064_, v___x_1069_, v___x_1118_);
v___x_1120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v_a_472_);
return v___x_1120_;
}
}
}
}
}
}
v___jp_809_:
{
lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_814_ = l_Lean_Syntax_getNumArgs(v___x_687_);
v___x_815_ = lean_nat_dec_le(v___x_482_, v___x_814_);
if (v___x_815_ == 0)
{
lean_dec(v___x_814_);
lean_dec(v_____discr_811_);
lean_dec(v_____discr_810_);
lean_dec(v_x_753_);
lean_dec(v___x_687_);
v___y_474_ = v___y_813_;
goto v___jp_473_;
}
else
{
lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_816_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_x_753_);
v___x_817_ = l_Lean_Syntax_isOfKind(v_x_753_, v___x_816_);
if (v___x_817_ == 0)
{
uint8_t v___x_818_; 
lean_inc(v_x_753_);
v___x_818_ = l_Lean_Syntax_isOfKind(v_x_753_, v___x_808_);
if (v___x_818_ == 0)
{
lean_dec(v___x_814_);
lean_dec(v_____discr_811_);
lean_dec(v_____discr_810_);
lean_dec(v_x_753_);
lean_dec(v___x_687_);
v___y_474_ = v___y_813_;
goto v___jp_473_;
}
else
{
lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_819_ = l_Lean_Syntax_getArg(v_x_753_, v___x_482_);
lean_inc(v___x_819_);
v___x_820_ = l_Lean_Syntax_matchesNull(v___x_819_, v___x_482_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_821_ = l_Lean_Syntax_getNumArgs(v___x_819_);
v___x_822_ = lean_nat_dec_le(v___x_482_, v___x_821_);
if (v___x_822_ == 0)
{
lean_dec(v___x_821_);
lean_dec(v___x_819_);
lean_dec(v___x_814_);
lean_dec(v_____discr_811_);
lean_dec(v_____discr_810_);
lean_dec(v_x_753_);
lean_dec(v___x_687_);
v___y_474_ = v___y_813_;
goto v___jp_473_;
}
else
{
lean_object* v_x_823_; uint8_t v___x_824_; 
v_x_823_ = l_Lean_Syntax_getArg(v___x_819_, v___x_481_);
lean_inc(v_x_823_);
v___x_824_ = l_Lean_Syntax_isOfKind(v_x_823_, v___x_816_);
if (v___x_824_ == 0)
{
lean_dec(v_x_823_);
lean_dec(v___x_821_);
lean_dec(v___x_819_);
lean_dec(v___x_814_);
lean_dec(v_____discr_811_);
lean_dec(v_____discr_810_);
lean_dec(v_x_753_);
lean_dec(v___x_687_);
v___y_474_ = v___y_813_;
goto v___jp_473_;
}
else
{
lean_object* v___x_825_; lean_object* v___x_826_; uint8_t v___x_827_; 
v___x_825_ = lean_unsigned_to_nat(2u);
v___x_826_ = l_Lean_Syntax_getArg(v_x_753_, v___x_825_);
lean_inc(v___x_826_);
v___x_827_ = l_Lean_Syntax_matchesNull(v___x_826_, v___x_825_);
if (v___x_827_ == 0)
{
lean_dec(v___x_826_);
lean_dec(v_x_823_);
lean_dec(v___x_821_);
lean_dec(v___x_819_);
lean_dec(v___x_814_);
lean_dec(v_____discr_811_);
lean_dec(v_____discr_810_);
lean_dec(v_x_753_);
lean_dec(v___x_687_);
v___y_474_ = v___y_813_;
goto v___jp_473_;
}
else
{
lean_object* v___x_828_; lean_object* v___x_829_; uint8_t v___x_830_; 
v___x_828_ = lean_unsigned_to_nat(3u);
v___x_829_ = l_Lean_Syntax_getArg(v_x_753_, v___x_828_);
lean_dec(v_x_753_);
v___x_830_ = l_Lean_Syntax_matchesNull(v___x_829_, v___x_481_);
if (v___x_830_ == 0)
{
lean_dec(v___x_826_);
lean_dec(v_x_823_);
lean_dec(v___x_821_);
lean_dec(v___x_819_);
lean_dec(v___x_814_);
lean_dec(v_____discr_811_);
lean_dec(v_____discr_810_);
lean_dec(v___x_687_);
v___y_474_ = v___y_813_;
goto v___jp_473_;
}
else
{
uint8_t v___x_831_; 
v___x_831_ = l_Lean_Syntax_matchesNull(v_____discr_810_, v___x_481_);
if (v___x_831_ == 0)
{
lean_dec(v___x_826_);
lean_dec(v_x_823_);
lean_dec(v___x_821_);
lean_dec(v___x_819_);
lean_dec(v___x_814_);
lean_dec(v_____discr_811_);
lean_dec(v___x_687_);
v___y_474_ = v___y_813_;
goto v___jp_473_;
}
else
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v_ty_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v_ys_841_; lean_object* v_xs_842_; 
v___x_832_ = l_Lean_Syntax_getArgs(v___x_819_);
lean_dec(v___x_819_);
v___x_833_ = l_Array_extract___redArg(v___x_832_, v___x_482_, v___x_821_);
lean_dec_ref(v___x_832_);
v_ty_834_ = l_Lean_Syntax_getArg(v___x_826_, v___x_482_);
lean_dec(v___x_826_);
v___x_835_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_836_ = lean_box(2);
v___x_837_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_837_, 0, v___x_836_);
lean_ctor_set(v___x_837_, 1, v___x_835_);
lean_ctor_set(v___x_837_, 2, v___x_833_);
v___x_838_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_839_ = l_Array_extract___redArg(v___x_838_, v___x_482_, v___x_814_);
lean_dec_ref(v___x_838_);
v___x_840_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_840_, 0, v___x_836_);
lean_ctor_set(v___x_840_, 1, v___x_835_);
lean_ctor_set(v___x_840_, 2, v___x_839_);
v_ys_841_ = l_Lean_Syntax_getArgs(v___x_840_);
lean_dec_ref_known(v___x_840_, 3);
v_xs_842_ = l_Lean_Syntax_getArgs(v___x_837_);
lean_dec_ref_known(v___x_837_, 3);
v_x_616_ = v_x_823_;
v_xs_617_ = v_xs_842_;
v_ty_618_ = v_ty_834_;
v_ys_619_ = v_ys_841_;
v_P_620_ = v_____discr_811_;
v___y_621_ = v___y_812_;
v___y_622_ = v___y_813_;
goto v___jp_615_;
}
}
}
}
}
}
else
{
lean_object* v_x_843_; uint8_t v___x_844_; 
v_x_843_ = l_Lean_Syntax_getArg(v___x_819_, v___x_481_);
lean_dec(v___x_819_);
lean_inc(v_x_843_);
v___x_844_ = l_Lean_Syntax_isOfKind(v_x_843_, v___x_816_);
if (v___x_844_ == 0)
{
lean_dec(v_x_843_);
lean_dec(v___x_814_);
lean_dec(v_____discr_811_);
lean_dec(v_____discr_810_);
lean_dec(v_x_753_);
lean_dec(v___x_687_);
v___y_474_ = v___y_813_;
goto v___jp_473_;
}
else
{
lean_object* v___x_845_; lean_object* v___x_846_; uint8_t v___x_847_; 
v___x_845_ = lean_unsigned_to_nat(2u);
v___x_846_ = l_Lean_Syntax_getArg(v_x_753_, v___x_845_);
lean_inc(v___x_846_);
v___x_847_ = l_Lean_Syntax_matchesNull(v___x_846_, v___x_845_);
if (v___x_847_ == 0)
{
lean_dec(v___x_846_);
lean_dec(v_x_843_);
lean_dec(v___x_814_);
lean_dec(v_____discr_811_);
lean_dec(v_____discr_810_);
lean_dec(v_x_753_);
lean_dec(v___x_687_);
v___y_474_ = v___y_813_;
goto v___jp_473_;
}
else
{
lean_object* v___x_848_; lean_object* v___x_849_; uint8_t v___x_850_; 
v___x_848_ = lean_unsigned_to_nat(3u);
v___x_849_ = l_Lean_Syntax_getArg(v_x_753_, v___x_848_);
lean_dec(v_x_753_);
v___x_850_ = l_Lean_Syntax_matchesNull(v___x_849_, v___x_481_);
if (v___x_850_ == 0)
{
lean_dec(v___x_846_);
lean_dec(v_x_843_);
lean_dec(v___x_814_);
lean_dec(v_____discr_811_);
lean_dec(v_____discr_810_);
lean_dec(v___x_687_);
v___y_474_ = v___y_813_;
goto v___jp_473_;
}
else
{
uint8_t v___x_851_; 
v___x_851_ = l_Lean_Syntax_matchesNull(v_____discr_810_, v___x_481_);
if (v___x_851_ == 0)
{
lean_dec(v___x_846_);
lean_dec(v_x_843_);
lean_dec(v___x_814_);
lean_dec(v_____discr_811_);
lean_dec(v___x_687_);
v___y_474_ = v___y_813_;
goto v___jp_473_;
}
else
{
lean_object* v_ty_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v_xs_858_; 
v_ty_852_ = l_Lean_Syntax_getArg(v___x_846_, v___x_482_);
lean_dec(v___x_846_);
v___x_853_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_854_ = l_Array_extract___redArg(v___x_853_, v___x_482_, v___x_814_);
lean_dec_ref(v___x_853_);
v___x_855_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_856_ = lean_box(2);
v___x_857_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
lean_ctor_set(v___x_857_, 1, v___x_855_);
lean_ctor_set(v___x_857_, 2, v___x_854_);
v_xs_858_ = l_Lean_Syntax_getArgs(v___x_857_);
lean_dec_ref_known(v___x_857_, 3);
v_x_554_ = v_x_843_;
v_ty_555_ = v_ty_852_;
v_xs_556_ = v_xs_858_;
v_P_557_ = v_____discr_811_;
v___y_558_ = v___y_812_;
v___y_559_ = v___y_813_;
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
uint8_t v___x_859_; 
v___x_859_ = l_Lean_Syntax_matchesNull(v_____discr_810_, v___x_481_);
if (v___x_859_ == 0)
{
lean_dec(v___x_814_);
lean_dec(v_____discr_811_);
lean_dec(v_x_753_);
lean_dec(v___x_687_);
v___y_474_ = v___y_813_;
goto v___jp_473_;
}
else
{
lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v_xs_865_; 
v___x_860_ = l_Lean_Syntax_getArgs(v___x_687_);
lean_dec(v___x_687_);
v___x_861_ = l_Array_extract___redArg(v___x_860_, v___x_482_, v___x_814_);
lean_dec_ref(v___x_860_);
v___x_862_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_863_ = lean_box(2);
v___x_864_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_864_, 0, v___x_863_);
lean_ctor_set(v___x_864_, 1, v___x_862_);
lean_ctor_set(v___x_864_, 2, v___x_861_);
v_xs_865_ = l_Lean_Syntax_getArgs(v___x_864_);
lean_dec_ref_known(v___x_864_, 3);
v_x_498_ = v_x_753_;
v_xs_499_ = v_xs_865_;
v_P_500_ = v_____discr_811_;
v___y_501_ = v___y_812_;
v___y_502_ = v___y_813_;
goto v___jp_497_;
}
}
}
}
}
else
{
lean_object* v_tk_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; uint8_t v___x_1124_; 
lean_dec(v___x_687_);
v_tk_1121_ = l_Lean_Syntax_getArg(v_x_753_, v___x_481_);
lean_dec(v_x_753_);
v___x_1122_ = lean_unsigned_to_nat(2u);
v___x_1123_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1122_);
lean_inc(v___x_1123_);
v___x_1124_ = l_Lean_Syntax_matchesNull(v___x_1123_, v___x_481_);
if (v___x_1124_ == 0)
{
uint8_t v___x_1125_; 
lean_inc(v___x_1123_);
v___x_1125_ = l_Lean_Syntax_matchesNull(v___x_1123_, v___x_482_);
if (v___x_1125_ == 0)
{
lean_dec(v___x_1123_);
lean_dec(v_tk_1121_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v___x_1126_; lean_object* v___x_1127_; uint8_t v___x_1128_; 
v___x_1126_ = l_Lean_Syntax_getArg(v___x_1123_, v___x_481_);
lean_dec(v___x_1123_);
v___x_1127_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55));
lean_inc(v___x_1126_);
v___x_1128_ = l_Lean_Syntax_isOfKind(v___x_1126_, v___x_1127_);
if (v___x_1128_ == 0)
{
lean_dec(v___x_1126_);
lean_dec(v_tk_1121_);
lean_dec(v___x_483_);
v___y_474_ = v_a_472_;
goto v___jp_473_;
}
else
{
lean_object* v_quotContext_1129_; lean_object* v_currMacroScope_1130_; lean_object* v_ref_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; 
v_quotContext_1129_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_1130_ = lean_ctor_get(v_a_471_, 2);
v_ref_1131_ = lean_ctor_get(v_a_471_, 5);
v___x_1132_ = l_Lean_Syntax_getArg(v___x_1126_, v___x_482_);
lean_dec(v___x_1126_);
v___x_1133_ = lean_unsigned_to_nat(4u);
v___x_1134_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1133_);
lean_dec(v___x_483_);
v___x_1135_ = l_Lean_SourceInfo_fromRef(v_ref_1131_, v___x_1124_);
v___x_1136_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_1137_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_1138_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc_n(v_currMacroScope_1130_, 2);
lean_inc_n(v_quotContext_1129_, 2);
v___x_1139_ = l_Lean_addMacroScope(v_quotContext_1129_, v___x_1138_, v_currMacroScope_1130_);
v___x_1140_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc_n(v___x_1135_, 19);
v___x_1141_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1141_, 0, v___x_1135_);
lean_ctor_set(v___x_1141_, 1, v___x_1137_);
lean_ctor_set(v___x_1141_, 2, v___x_1139_);
lean_ctor_set(v___x_1141_, 3, v___x_1140_);
v___x_1142_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1143_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_1144_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_1145_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
v___x_1146_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1146_, 0, v___x_1135_);
lean_ctor_set(v___x_1146_, 1, v___x_1145_);
v___x_1147_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_1148_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_1149_ = lean_box(0);
v___x_1150_ = l_Lean_addMacroScope(v_quotContext_1129_, v___x_1149_, v_currMacroScope_1130_);
v___x_1151_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
v___x_1152_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1135_);
lean_ctor_set(v___x_1152_, 1, v___x_1148_);
lean_ctor_set(v___x_1152_, 2, v___x_1150_);
lean_ctor_set(v___x_1152_, 3, v___x_1151_);
v___x_1153_ = l_Lean_Syntax_node1(v___x_1135_, v___x_1147_, v___x_1152_);
v___x_1154_ = l_Lean_Syntax_node2(v___x_1135_, v___x_1144_, v___x_1146_, v___x_1153_);
v___x_1155_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_1156_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
v___x_1157_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1157_, 0, v___x_1135_);
lean_ctor_set(v___x_1157_, 1, v___x_1155_);
v___x_1158_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_1159_ = l_Lean_SourceInfo_fromRef(v_tk_1121_, v___x_688_);
lean_dec(v_tk_1121_);
v___x_1160_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__63));
v___x_1161_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1161_, 0, v___x_1159_);
lean_ctor_set(v___x_1161_, 1, v___x_1160_);
v___x_1162_ = l_Lean_Syntax_node1(v___x_1135_, v___x_754_, v___x_1161_);
v___x_1163_ = l_Lean_Syntax_node1(v___x_1135_, v___x_1142_, v___x_1162_);
v___x_1164_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
v___x_1165_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1135_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
v___x_1166_ = l_Lean_Syntax_node2(v___x_1135_, v___x_1127_, v___x_1165_, v___x_1132_);
v___x_1167_ = l_Lean_Syntax_node1(v___x_1135_, v___x_1142_, v___x_1166_);
v___x_1168_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_1169_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1169_, 0, v___x_1135_);
lean_ctor_set(v___x_1169_, 1, v___x_1168_);
v___x_1170_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_1171_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_1135_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1173_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1173_, 0, v___x_1135_);
lean_ctor_set(v___x_1173_, 1, v___x_1172_);
lean_inc_ref(v___x_1173_);
v___x_1174_ = l_Lean_Syntax_node3(v___x_1135_, v___x_477_, v___x_1171_, v___x_1134_, v___x_1173_);
v___x_1175_ = l_Lean_Syntax_node4(v___x_1135_, v___x_1158_, v___x_1163_, v___x_1167_, v___x_1169_, v___x_1174_);
v___x_1176_ = l_Lean_Syntax_node2(v___x_1135_, v___x_1156_, v___x_1157_, v___x_1175_);
v___x_1177_ = l_Lean_Syntax_node3(v___x_1135_, v___x_1143_, v___x_1154_, v___x_1176_, v___x_1173_);
v___x_1178_ = l_Lean_Syntax_node1(v___x_1135_, v___x_1142_, v___x_1177_);
v___x_1179_ = l_Lean_Syntax_node2(v___x_1135_, v___x_1136_, v___x_1141_, v___x_1178_);
v___x_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1180_, 0, v___x_1179_);
lean_ctor_set(v___x_1180_, 1, v_a_472_);
return v___x_1180_;
}
}
}
else
{
lean_object* v_quotContext_1181_; lean_object* v_currMacroScope_1182_; lean_object* v_ref_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; 
lean_dec(v___x_1123_);
v_quotContext_1181_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_1182_ = lean_ctor_get(v_a_471_, 2);
v_ref_1183_ = lean_ctor_get(v_a_471_, 5);
v___x_1184_ = lean_unsigned_to_nat(4u);
v___x_1185_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1184_);
lean_dec(v___x_483_);
v___x_1186_ = l_Lean_SourceInfo_fromRef(v_ref_1183_, v___x_495_);
v___x_1187_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_1188_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_1189_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc_n(v_currMacroScope_1182_, 2);
lean_inc_n(v_quotContext_1181_, 2);
v___x_1190_ = l_Lean_addMacroScope(v_quotContext_1181_, v___x_1189_, v_currMacroScope_1182_);
v___x_1191_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc_n(v___x_1186_, 17);
v___x_1192_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1192_, 0, v___x_1186_);
lean_ctor_set(v___x_1192_, 1, v___x_1188_);
lean_ctor_set(v___x_1192_, 2, v___x_1190_);
lean_ctor_set(v___x_1192_, 3, v___x_1191_);
v___x_1193_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1194_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_1195_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_1196_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
v___x_1197_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1186_);
lean_ctor_set(v___x_1197_, 1, v___x_1196_);
v___x_1198_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_1199_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_1200_ = lean_box(0);
v___x_1201_ = l_Lean_addMacroScope(v_quotContext_1181_, v___x_1200_, v_currMacroScope_1182_);
v___x_1202_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
v___x_1203_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1203_, 0, v___x_1186_);
lean_ctor_set(v___x_1203_, 1, v___x_1199_);
lean_ctor_set(v___x_1203_, 2, v___x_1201_);
lean_ctor_set(v___x_1203_, 3, v___x_1202_);
v___x_1204_ = l_Lean_Syntax_node1(v___x_1186_, v___x_1198_, v___x_1203_);
v___x_1205_ = l_Lean_Syntax_node2(v___x_1186_, v___x_1195_, v___x_1197_, v___x_1204_);
v___x_1206_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_1207_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
v___x_1208_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1208_, 0, v___x_1186_);
lean_ctor_set(v___x_1208_, 1, v___x_1206_);
v___x_1209_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_1210_ = l_Lean_SourceInfo_fromRef(v_tk_1121_, v___x_688_);
lean_dec(v_tk_1121_);
v___x_1211_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__63));
v___x_1212_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1212_, 0, v___x_1210_);
lean_ctor_set(v___x_1212_, 1, v___x_1211_);
v___x_1213_ = l_Lean_Syntax_node1(v___x_1186_, v___x_754_, v___x_1212_);
v___x_1214_ = l_Lean_Syntax_node1(v___x_1186_, v___x_1193_, v___x_1213_);
v___x_1215_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_1216_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1216_, 0, v___x_1186_);
lean_ctor_set(v___x_1216_, 1, v___x_1193_);
lean_ctor_set(v___x_1216_, 2, v___x_1215_);
v___x_1217_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_1218_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1218_, 0, v___x_1186_);
lean_ctor_set(v___x_1218_, 1, v___x_1217_);
v___x_1219_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_1220_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1186_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
v___x_1221_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1222_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1186_);
lean_ctor_set(v___x_1222_, 1, v___x_1221_);
lean_inc_ref(v___x_1222_);
v___x_1223_ = l_Lean_Syntax_node3(v___x_1186_, v___x_477_, v___x_1220_, v___x_1185_, v___x_1222_);
v___x_1224_ = l_Lean_Syntax_node4(v___x_1186_, v___x_1209_, v___x_1214_, v___x_1216_, v___x_1218_, v___x_1223_);
v___x_1225_ = l_Lean_Syntax_node2(v___x_1186_, v___x_1207_, v___x_1208_, v___x_1224_);
v___x_1226_ = l_Lean_Syntax_node3(v___x_1186_, v___x_1194_, v___x_1205_, v___x_1225_, v___x_1222_);
v___x_1227_ = l_Lean_Syntax_node1(v___x_1186_, v___x_1193_, v___x_1226_);
v___x_1228_ = l_Lean_Syntax_node2(v___x_1186_, v___x_1187_, v___x_1192_, v___x_1227_);
v___x_1229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1228_);
lean_ctor_set(v___x_1229_, 1, v_a_472_);
return v___x_1229_;
}
}
v___jp_756_:
{
lean_object* v_quotContext_762_; lean_object* v_currMacroScope_763_; lean_object* v_ref_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v_quotContext_762_ = lean_ctor_get(v___y_760_, 1);
v_currMacroScope_763_ = lean_ctor_get(v___y_760_, 2);
v_ref_764_ = lean_ctor_get(v___y_760_, 5);
v___x_765_ = l_Lean_SourceInfo_fromRef(v_ref_764_, v___x_755_);
v___x_766_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_767_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__15);
v___x_768_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__16));
lean_inc_n(v_currMacroScope_763_, 2);
lean_inc_n(v_quotContext_762_, 2);
v___x_769_ = l_Lean_addMacroScope(v_quotContext_762_, v___x_768_, v_currMacroScope_763_);
v___x_770_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__19));
lean_inc_n(v___x_765_, 18);
v___x_771_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_771_, 0, v___x_765_);
lean_ctor_set(v___x_771_, 1, v___x_767_);
lean_ctor_set(v___x_771_, 2, v___x_769_);
lean_ctor_set(v___x_771_, 3, v___x_770_);
v___x_772_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_773_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
v___x_774_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
v___x_775_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
v___x_776_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_776_, 0, v___x_765_);
lean_ctor_set(v___x_776_, 1, v___x_775_);
v___x_777_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
v___x_778_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_779_ = lean_box(0);
v___x_780_ = l_Lean_addMacroScope(v_quotContext_762_, v___x_779_, v_currMacroScope_763_);
v___x_781_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__45));
v___x_782_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_782_, 0, v___x_765_);
lean_ctor_set(v___x_782_, 1, v___x_778_);
lean_ctor_set(v___x_782_, 2, v___x_780_);
lean_ctor_set(v___x_782_, 3, v___x_781_);
v___x_783_ = l_Lean_Syntax_node1(v___x_765_, v___x_777_, v___x_782_);
v___x_784_ = l_Lean_Syntax_node2(v___x_765_, v___x_774_, v___x_776_, v___x_783_);
v___x_785_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_786_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
v___x_787_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_787_, 0, v___x_765_);
lean_ctor_set(v___x_787_, 1, v___x_785_);
v___x_788_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
v___x_789_ = l_Lean_Syntax_node1(v___x_765_, v___x_772_, v_x_757_);
v___x_790_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__55));
v___x_791_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
v___x_792_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_792_, 0, v___x_765_);
lean_ctor_set(v___x_792_, 1, v___x_791_);
v___x_793_ = l_Lean_Syntax_node2(v___x_765_, v___x_790_, v___x_792_, v_ty_758_);
v___x_794_ = l_Lean_Syntax_node1(v___x_765_, v___x_772_, v___x_793_);
v___x_795_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_796_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_796_, 0, v___x_765_);
lean_ctor_set(v___x_796_, 1, v___x_795_);
v___x_797_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_798_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_798_, 0, v___x_765_);
lean_ctor_set(v___x_798_, 1, v___x_797_);
v___x_799_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_765_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
lean_inc_ref(v___x_800_);
v___x_801_ = l_Lean_Syntax_node3(v___x_765_, v___x_477_, v___x_798_, v_P_759_, v___x_800_);
v___x_802_ = l_Lean_Syntax_node4(v___x_765_, v___x_788_, v___x_789_, v___x_794_, v___x_796_, v___x_801_);
v___x_803_ = l_Lean_Syntax_node2(v___x_765_, v___x_786_, v___x_787_, v___x_802_);
v___x_804_ = l_Lean_Syntax_node3(v___x_765_, v___x_773_, v___x_784_, v___x_803_, v___x_800_);
v___x_805_ = l_Lean_Syntax_node1(v___x_765_, v___x_772_, v___x_804_);
v___x_806_ = l_Lean_Syntax_node2(v___x_765_, v___x_766_, v___x_771_, v___x_805_);
v___x_807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_806_);
lean_ctor_set(v___x_807_, 1, v___y_761_);
return v___x_807_;
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
lean_object* v___x_1230_; lean_object* v___x_1231_; uint8_t v___x_1232_; 
v___x_1230_ = l_Lean_Syntax_getArg(v___x_483_, v___x_482_);
v___x_1231_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65));
lean_inc(v___x_1230_);
v___x_1232_ = l_Lean_Syntax_isOfKind(v___x_1230_, v___x_1231_);
if (v___x_1232_ == 0)
{
lean_object* v___x_1233_; lean_object* v___x_1234_; 
lean_dec(v___x_1230_);
lean_dec(v___x_483_);
v___x_1233_ = lean_box(1);
v___x_1234_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1234_, 0, v___x_1233_);
lean_ctor_set(v___x_1234_, 1, v_a_472_);
return v___x_1234_;
}
else
{
lean_object* v_ref_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v_ref_1235_ = lean_ctor_get(v_a_471_, 5);
v___x_1236_ = lean_unsigned_to_nat(3u);
v___x_1237_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1236_);
lean_dec(v___x_483_);
v___x_1238_ = l_Lean_SourceInfo_fromRef(v_ref_1235_, v___x_493_);
v___x_1239_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_1238_, 2);
v___x_1240_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1240_, 0, v___x_1238_);
lean_ctor_set(v___x_1240_, 1, v___x_1239_);
v___x_1241_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1242_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1242_, 0, v___x_1238_);
lean_ctor_set(v___x_1242_, 1, v___x_1241_);
v___x_1243_ = l_Lean_Syntax_node3(v___x_1238_, v___x_477_, v___x_1240_, v___x_1237_, v___x_1242_);
v___x_1244_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__67));
v___x_1245_ = l_Lean_expandExplicitBinders(v___x_1244_, v___x_1230_, v___x_1243_, v_a_471_, v_a_472_);
lean_dec(v___x_1230_);
return v___x_1245_;
}
}
}
else
{
lean_object* v_quotContext_1246_; lean_object* v_currMacroScope_1247_; lean_object* v_ref_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v_quotContext_1246_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_1247_ = lean_ctor_get(v_a_471_, 2);
v_ref_1248_ = lean_ctor_get(v_a_471_, 5);
v___x_1249_ = l_Lean_Syntax_getArg(v___x_483_, v___x_481_);
v___x_1250_ = lean_unsigned_to_nat(2u);
v___x_1251_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1250_);
lean_dec(v___x_483_);
v___x_1252_ = l_Lean_SourceInfo_fromRef(v_ref_1248_, v___x_491_);
v___x_1253_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_1254_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__69, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__69_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__69);
v___x_1255_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__71));
lean_inc(v_currMacroScope_1247_);
lean_inc(v_quotContext_1246_);
v___x_1256_ = l_Lean_addMacroScope(v_quotContext_1246_, v___x_1255_, v_currMacroScope_1247_);
v___x_1257_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__74));
lean_inc_n(v___x_1252_, 6);
v___x_1258_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1252_);
lean_ctor_set(v___x_1258_, 1, v___x_1254_);
lean_ctor_set(v___x_1258_, 2, v___x_1256_);
lean_ctor_set(v___x_1258_, 3, v___x_1257_);
v___x_1259_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1260_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_1261_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1252_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
v___x_1262_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1263_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1263_, 0, v___x_1252_);
lean_ctor_set(v___x_1263_, 1, v___x_1262_);
lean_inc_ref(v___x_1263_);
lean_inc_ref(v___x_1261_);
v___x_1264_ = l_Lean_Syntax_node3(v___x_1252_, v___x_477_, v___x_1261_, v___x_1249_, v___x_1263_);
v___x_1265_ = l_Lean_Syntax_node3(v___x_1252_, v___x_477_, v___x_1261_, v___x_1251_, v___x_1263_);
v___x_1266_ = l_Lean_Syntax_node2(v___x_1252_, v___x_1259_, v___x_1264_, v___x_1265_);
v___x_1267_ = l_Lean_Syntax_node2(v___x_1252_, v___x_1253_, v___x_1258_, v___x_1266_);
v___x_1268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1268_, 0, v___x_1267_);
lean_ctor_set(v___x_1268_, 1, v_a_472_);
return v___x_1268_;
}
}
else
{
lean_object* v_quotContext_1269_; lean_object* v_currMacroScope_1270_; lean_object* v_ref_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; lean_object* v___x_1277_; lean_object* v___x_1278_; lean_object* v___x_1279_; lean_object* v___x_1280_; lean_object* v___x_1281_; lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
v_quotContext_1269_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_1270_ = lean_ctor_get(v_a_471_, 2);
v_ref_1271_ = lean_ctor_get(v_a_471_, 5);
v___x_1272_ = l_Lean_Syntax_getArg(v___x_483_, v___x_481_);
v___x_1273_ = lean_unsigned_to_nat(2u);
v___x_1274_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1273_);
lean_dec(v___x_483_);
v___x_1275_ = l_Lean_SourceInfo_fromRef(v_ref_1271_, v___x_489_);
v___x_1276_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_1277_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__76, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__76_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__76);
v___x_1278_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__78));
lean_inc(v_currMacroScope_1270_);
lean_inc(v_quotContext_1269_);
v___x_1279_ = l_Lean_addMacroScope(v_quotContext_1269_, v___x_1278_, v_currMacroScope_1270_);
v___x_1280_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__81));
lean_inc_n(v___x_1275_, 6);
v___x_1281_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1281_, 0, v___x_1275_);
lean_ctor_set(v___x_1281_, 1, v___x_1277_);
lean_ctor_set(v___x_1281_, 2, v___x_1279_);
lean_ctor_set(v___x_1281_, 3, v___x_1280_);
v___x_1282_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1283_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_1284_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1284_, 0, v___x_1275_);
lean_ctor_set(v___x_1284_, 1, v___x_1283_);
v___x_1285_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1286_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1286_, 0, v___x_1275_);
lean_ctor_set(v___x_1286_, 1, v___x_1285_);
lean_inc_ref(v___x_1286_);
lean_inc_ref(v___x_1284_);
v___x_1287_ = l_Lean_Syntax_node3(v___x_1275_, v___x_477_, v___x_1284_, v___x_1272_, v___x_1286_);
v___x_1288_ = l_Lean_Syntax_node3(v___x_1275_, v___x_477_, v___x_1284_, v___x_1274_, v___x_1286_);
v___x_1289_ = l_Lean_Syntax_node2(v___x_1275_, v___x_1282_, v___x_1287_, v___x_1288_);
v___x_1290_ = l_Lean_Syntax_node2(v___x_1275_, v___x_1276_, v___x_1281_, v___x_1289_);
v___x_1291_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1291_, 0, v___x_1290_);
lean_ctor_set(v___x_1291_, 1, v_a_472_);
return v___x_1291_;
}
}
else
{
lean_object* v_quotContext_1292_; lean_object* v_currMacroScope_1293_; lean_object* v_ref_1294_; lean_object* v___x_1295_; lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1303_; lean_object* v___x_1304_; lean_object* v___x_1305_; lean_object* v___x_1306_; lean_object* v___x_1307_; lean_object* v___x_1308_; lean_object* v___x_1309_; lean_object* v___x_1310_; lean_object* v___x_1311_; 
v_quotContext_1292_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_1293_ = lean_ctor_get(v_a_471_, 2);
v_ref_1294_ = lean_ctor_get(v_a_471_, 5);
v___x_1295_ = l_Lean_Syntax_getArg(v___x_483_, v___x_482_);
lean_dec(v___x_483_);
v___x_1296_ = l_Lean_SourceInfo_fromRef(v_ref_1294_, v___x_487_);
v___x_1297_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_1298_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__83, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__83_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__83);
v___x_1299_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__85));
lean_inc(v_currMacroScope_1293_);
lean_inc(v_quotContext_1292_);
v___x_1300_ = l_Lean_addMacroScope(v_quotContext_1292_, v___x_1299_, v_currMacroScope_1293_);
v___x_1301_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__90));
lean_inc_n(v___x_1296_, 5);
v___x_1302_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1302_, 0, v___x_1296_);
lean_ctor_set(v___x_1302_, 1, v___x_1298_);
lean_ctor_set(v___x_1302_, 2, v___x_1300_);
lean_ctor_set(v___x_1302_, 3, v___x_1301_);
v___x_1303_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1304_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_1305_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1305_, 0, v___x_1296_);
lean_ctor_set(v___x_1305_, 1, v___x_1304_);
v___x_1306_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1307_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1307_, 0, v___x_1296_);
lean_ctor_set(v___x_1307_, 1, v___x_1306_);
v___x_1308_ = l_Lean_Syntax_node3(v___x_1296_, v___x_477_, v___x_1305_, v___x_1295_, v___x_1307_);
v___x_1309_ = l_Lean_Syntax_node1(v___x_1296_, v___x_1303_, v___x_1308_);
v___x_1310_ = l_Lean_Syntax_node2(v___x_1296_, v___x_1297_, v___x_1302_, v___x_1309_);
v___x_1311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1311_, 0, v___x_1310_);
lean_ctor_set(v___x_1311_, 1, v_a_472_);
return v___x_1311_;
}
}
else
{
lean_object* v_quotContext_1312_; lean_object* v_currMacroScope_1313_; lean_object* v_ref_1314_; lean_object* v___x_1315_; lean_object* v___x_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; 
v_quotContext_1312_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_1313_ = lean_ctor_get(v_a_471_, 2);
v_ref_1314_ = lean_ctor_get(v_a_471_, 5);
v___x_1315_ = l_Lean_Syntax_getArg(v___x_483_, v___x_481_);
v___x_1316_ = lean_unsigned_to_nat(2u);
v___x_1317_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1316_);
lean_dec(v___x_483_);
v___x_1318_ = l_Lean_SourceInfo_fromRef(v_ref_1314_, v___x_485_);
v___x_1319_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_1320_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__92, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__92_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__92);
v___x_1321_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__94));
lean_inc(v_currMacroScope_1313_);
lean_inc(v_quotContext_1312_);
v___x_1322_ = l_Lean_addMacroScope(v_quotContext_1312_, v___x_1321_, v_currMacroScope_1313_);
v___x_1323_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__97));
lean_inc_n(v___x_1318_, 6);
v___x_1324_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1318_);
lean_ctor_set(v___x_1324_, 1, v___x_1320_);
lean_ctor_set(v___x_1324_, 2, v___x_1322_);
lean_ctor_set(v___x_1324_, 3, v___x_1323_);
v___x_1325_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1326_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_1327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1318_);
lean_ctor_set(v___x_1327_, 1, v___x_1326_);
v___x_1328_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1329_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1329_, 0, v___x_1318_);
lean_ctor_set(v___x_1329_, 1, v___x_1328_);
lean_inc_ref(v___x_1329_);
lean_inc_ref(v___x_1327_);
v___x_1330_ = l_Lean_Syntax_node3(v___x_1318_, v___x_477_, v___x_1327_, v___x_1315_, v___x_1329_);
v___x_1331_ = l_Lean_Syntax_node3(v___x_1318_, v___x_477_, v___x_1327_, v___x_1317_, v___x_1329_);
v___x_1332_ = l_Lean_Syntax_node2(v___x_1318_, v___x_1325_, v___x_1330_, v___x_1331_);
v___x_1333_ = l_Lean_Syntax_node2(v___x_1318_, v___x_1319_, v___x_1324_, v___x_1332_);
v___x_1334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1334_, 0, v___x_1333_);
lean_ctor_set(v___x_1334_, 1, v_a_472_);
return v___x_1334_;
}
}
else
{
lean_object* v_quotContext_1335_; lean_object* v_currMacroScope_1336_; lean_object* v_ref_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; uint8_t v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v_quotContext_1335_ = lean_ctor_get(v_a_471_, 1);
v_currMacroScope_1336_ = lean_ctor_get(v_a_471_, 2);
v_ref_1337_ = lean_ctor_get(v_a_471_, 5);
v___x_1338_ = l_Lean_Syntax_getArg(v___x_483_, v___x_481_);
v___x_1339_ = lean_unsigned_to_nat(2u);
v___x_1340_ = l_Lean_Syntax_getArg(v___x_483_, v___x_1339_);
lean_dec(v___x_483_);
v___x_1341_ = 0;
v___x_1342_ = l_Lean_SourceInfo_fromRef(v_ref_1337_, v___x_1341_);
v___x_1343_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_1344_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__99, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__99_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__99);
v___x_1345_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__101));
lean_inc(v_currMacroScope_1336_);
lean_inc(v_quotContext_1335_);
v___x_1346_ = l_Lean_addMacroScope(v_quotContext_1335_, v___x_1345_, v_currMacroScope_1336_);
v___x_1347_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__104));
lean_inc_n(v___x_1342_, 6);
v___x_1348_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1348_, 0, v___x_1342_);
lean_ctor_set(v___x_1348_, 1, v___x_1344_);
lean_ctor_set(v___x_1348_, 2, v___x_1346_);
lean_ctor_set(v___x_1348_, 3, v___x_1347_);
v___x_1349_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1350_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_1351_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1351_, 0, v___x_1342_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
v___x_1352_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1353_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1342_);
lean_ctor_set(v___x_1353_, 1, v___x_1352_);
lean_inc_ref(v___x_1353_);
lean_inc_ref(v___x_1351_);
v___x_1354_ = l_Lean_Syntax_node3(v___x_1342_, v___x_477_, v___x_1351_, v___x_1338_, v___x_1353_);
v___x_1355_ = l_Lean_Syntax_node3(v___x_1342_, v___x_477_, v___x_1351_, v___x_1340_, v___x_1353_);
v___x_1356_ = l_Lean_Syntax_node2(v___x_1342_, v___x_1349_, v___x_1354_, v___x_1355_);
v___x_1357_ = l_Lean_Syntax_node2(v___x_1342_, v___x_1343_, v___x_1348_, v___x_1356_);
v___x_1358_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
lean_ctor_set(v___x_1358_, 1, v_a_472_);
return v___x_1358_;
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
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___boxed(lean_object* v_x_1359_, lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1(v_x_1359_, v_a_1360_, v_a_1361_);
lean_dec_ref(v_a_1360_);
return v_res_1362_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__1(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__0));
v___x_1365_ = l_String_toRawSubstring_x27(v___x_1364_);
return v___x_1365_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1(lean_object* v_x_1379_, lean_object* v_a_1380_, lean_object* v_a_1381_){
_start:
{
lean_object* v___x_1382_; uint8_t v___x_1383_; 
v___x_1382_ = ((lean_object*)(l_Std_Do_term_u22a2_u209b___00__closed__1));
lean_inc(v_x_1379_);
v___x_1383_ = l_Lean_Syntax_isOfKind(v_x_1379_, v___x_1382_);
if (v___x_1383_ == 0)
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
lean_dec(v_x_1379_);
v___x_1384_ = lean_box(1);
v___x_1385_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
lean_ctor_set(v___x_1385_, 1, v_a_1381_);
return v___x_1385_;
}
else
{
lean_object* v_quotContext_1386_; lean_object* v_currMacroScope_1387_; lean_object* v_ref_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; uint8_t v___x_1391_; lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v_quotContext_1386_ = lean_ctor_get(v_a_1380_, 1);
v_currMacroScope_1387_ = lean_ctor_get(v_a_1380_, 2);
v_ref_1388_ = lean_ctor_get(v_a_1380_, 5);
v___x_1389_ = lean_unsigned_to_nat(1u);
v___x_1390_ = l_Lean_Syntax_getArg(v_x_1379_, v___x_1389_);
lean_dec(v_x_1379_);
v___x_1391_ = 0;
v___x_1392_ = l_Lean_SourceInfo_fromRef(v_ref_1388_, v___x_1391_);
v___x_1393_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_1394_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__1, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__1);
v___x_1395_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__3));
lean_inc_n(v_currMacroScope_1387_, 2);
lean_inc_n(v_quotContext_1386_, 2);
v___x_1396_ = l_Lean_addMacroScope(v_quotContext_1386_, v___x_1395_, v_currMacroScope_1387_);
v___x_1397_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__8));
lean_inc_n(v___x_1392_, 9);
v___x_1398_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1398_, 0, v___x_1392_);
lean_ctor_set(v___x_1398_, 1, v___x_1394_);
lean_ctor_set(v___x_1398_, 2, v___x_1396_);
lean_ctor_set(v___x_1398_, 3, v___x_1397_);
v___x_1399_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1400_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__3));
v___x_1401_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__6));
v___x_1402_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1392_);
lean_ctor_set(v___x_1402_, 1, v___x_1401_);
v___x_1403_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__1, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__1);
v___x_1404_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__2));
v___x_1405_ = l_Lean_addMacroScope(v_quotContext_1386_, v___x_1404_, v_currMacroScope_1387_);
v___x_1406_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__6));
v___x_1407_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1407_, 0, v___x_1392_);
lean_ctor_set(v___x_1407_, 1, v___x_1403_);
lean_ctor_set(v___x_1407_, 2, v___x_1405_);
lean_ctor_set(v___x_1407_, 3, v___x_1406_);
v___x_1408_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__12));
v___x_1409_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1392_);
lean_ctor_set(v___x_1409_, 1, v___x_1408_);
v___x_1410_ = l_Lean_Syntax_node3(v___x_1392_, v___x_1400_, v___x_1402_, v___x_1407_, v___x_1409_);
v___x_1411_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_1412_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_1413_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1413_, 0, v___x_1392_);
lean_ctor_set(v___x_1413_, 1, v___x_1412_);
v___x_1414_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1415_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1415_, 0, v___x_1392_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
v___x_1416_ = l_Lean_Syntax_node3(v___x_1392_, v___x_1411_, v___x_1413_, v___x_1390_, v___x_1415_);
v___x_1417_ = l_Lean_Syntax_node2(v___x_1392_, v___x_1399_, v___x_1410_, v___x_1416_);
v___x_1418_ = l_Lean_Syntax_node2(v___x_1392_, v___x_1393_, v___x_1398_, v___x_1417_);
v___x_1419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1419_, 0, v___x_1418_);
lean_ctor_set(v___x_1419_, 1, v_a_1381_);
return v___x_1419_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___boxed(lean_object* v_x_1420_, lean_object* v_a_1421_, lean_object* v_a_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1(v_x_1420_, v_a_1421_, v_a_1422_);
lean_dec_ref(v_a_1421_);
return v_res_1423_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__1(void){
_start:
{
lean_object* v___x_1425_; lean_object* v___x_1426_; 
v___x_1425_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__0));
v___x_1426_ = l_String_toRawSubstring_x27(v___x_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1(lean_object* v_x_1442_, lean_object* v_a_1443_, lean_object* v_a_1444_){
_start:
{
lean_object* v___x_1445_; uint8_t v___x_1446_; 
v___x_1445_ = ((lean_object*)(l_Std_Do_term___u22a3_u22a2_u209b___00__closed__1));
lean_inc(v_x_1442_);
v___x_1446_ = l_Lean_Syntax_isOfKind(v_x_1442_, v___x_1445_);
if (v___x_1446_ == 0)
{
lean_object* v___x_1447_; lean_object* v___x_1448_; 
lean_dec(v_x_1442_);
v___x_1447_ = lean_box(1);
v___x_1448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1448_, 0, v___x_1447_);
lean_ctor_set(v___x_1448_, 1, v_a_1444_);
return v___x_1448_;
}
else
{
lean_object* v_quotContext_1449_; lean_object* v_currMacroScope_1450_; lean_object* v_ref_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; uint8_t v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; lean_object* v___x_1474_; 
v_quotContext_1449_ = lean_ctor_get(v_a_1443_, 1);
v_currMacroScope_1450_ = lean_ctor_get(v_a_1443_, 2);
v_ref_1451_ = lean_ctor_get(v_a_1443_, 5);
v___x_1452_ = lean_unsigned_to_nat(0u);
v___x_1453_ = l_Lean_Syntax_getArg(v_x_1442_, v___x_1452_);
v___x_1454_ = lean_unsigned_to_nat(2u);
v___x_1455_ = l_Lean_Syntax_getArg(v_x_1442_, v___x_1454_);
lean_dec(v_x_1442_);
v___x_1456_ = 0;
v___x_1457_ = l_Lean_SourceInfo_fromRef(v_ref_1451_, v___x_1456_);
v___x_1458_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
v___x_1459_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__1, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__1);
v___x_1460_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__3));
lean_inc(v_currMacroScope_1450_);
lean_inc(v_quotContext_1449_);
v___x_1461_ = l_Lean_addMacroScope(v_quotContext_1449_, v___x_1460_, v_currMacroScope_1450_);
v___x_1462_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___closed__6));
lean_inc_n(v___x_1457_, 6);
v___x_1463_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1463_, 0, v___x_1457_);
lean_ctor_set(v___x_1463_, 1, v___x_1459_);
lean_ctor_set(v___x_1463_, 2, v___x_1461_);
lean_ctor_set(v___x_1463_, 3, v___x_1462_);
v___x_1464_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1465_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_1466_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
v___x_1467_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1467_, 0, v___x_1457_);
lean_ctor_set(v___x_1467_, 1, v___x_1466_);
v___x_1468_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1469_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1469_, 0, v___x_1457_);
lean_ctor_set(v___x_1469_, 1, v___x_1468_);
lean_inc_ref(v___x_1469_);
lean_inc_ref(v___x_1467_);
v___x_1470_ = l_Lean_Syntax_node3(v___x_1457_, v___x_1465_, v___x_1467_, v___x_1453_, v___x_1469_);
v___x_1471_ = l_Lean_Syntax_node3(v___x_1457_, v___x_1465_, v___x_1467_, v___x_1455_, v___x_1469_);
v___x_1472_ = l_Lean_Syntax_node2(v___x_1457_, v___x_1464_, v___x_1470_, v___x_1471_);
v___x_1473_ = l_Lean_Syntax_node2(v___x_1457_, v___x_1458_, v___x_1463_, v___x_1472_);
v___x_1474_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1474_, 0, v___x_1473_);
lean_ctor_set(v___x_1474_, 1, v_a_1444_);
return v___x_1474_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1___boxed(lean_object* v_x_1475_, lean_object* v_a_1476_, lean_object* v_a_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a3_u22a2_u209b____1(v_x_1475_, v_a_1476_, v_a_1477_);
lean_dec_ref(v_a_1476_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandPure(lean_object* v_x_1479_, lean_object* v_a_1480_, lean_object* v_a_1481_){
_start:
{
lean_object* v___x_1482_; uint8_t v___x_1483_; 
v___x_1482_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_1479_);
v___x_1483_ = l_Lean_Syntax_isOfKind(v_x_1479_, v___x_1482_);
if (v___x_1483_ == 0)
{
lean_object* v___x_1484_; lean_object* v___x_1485_; 
lean_dec(v_x_1479_);
v___x_1484_ = lean_box(0);
v___x_1485_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___x_1484_);
lean_ctor_set(v___x_1485_, 1, v_a_1481_);
return v___x_1485_;
}
else
{
lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; uint8_t v___x_1489_; 
v___x_1486_ = lean_unsigned_to_nat(1u);
v___x_1487_ = l_Lean_Syntax_getArg(v_x_1479_, v___x_1486_);
lean_dec(v_x_1479_);
v___x_1488_ = l_Lean_Syntax_getNumArgs(v___x_1487_);
v___x_1489_ = lean_nat_dec_le(v___x_1486_, v___x_1488_);
if (v___x_1489_ == 0)
{
lean_object* v___x_1490_; lean_object* v___x_1491_; 
lean_dec(v___x_1488_);
lean_dec(v___x_1487_);
v___x_1490_ = lean_box(0);
v___x_1491_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1491_, 0, v___x_1490_);
lean_ctor_set(v___x_1491_, 1, v_a_1481_);
return v___x_1491_;
}
else
{
lean_object* v___x_1492_; lean_object* v___x_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v_ts_1499_; lean_object* v___x_1500_; uint8_t v___x_1501_; 
v___x_1492_ = lean_unsigned_to_nat(0u);
v___x_1493_ = l_Lean_Syntax_getArg(v___x_1487_, v___x_1492_);
v___x_1494_ = l_Lean_Syntax_getArgs(v___x_1487_);
lean_dec(v___x_1487_);
v___x_1495_ = l_Array_extract___redArg(v___x_1494_, v___x_1486_, v___x_1488_);
lean_dec_ref(v___x_1494_);
v___x_1496_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1497_ = lean_box(2);
v___x_1498_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1498_, 0, v___x_1497_);
lean_ctor_set(v___x_1498_, 1, v___x_1496_);
lean_ctor_set(v___x_1498_, 2, v___x_1495_);
v_ts_1499_ = l_Lean_Syntax_getArgs(v___x_1498_);
lean_dec_ref_known(v___x_1498_, 3);
v___x_1500_ = lean_array_get_size(v_ts_1499_);
v___x_1501_ = lean_nat_dec_eq(v___x_1500_, v___x_1492_);
if (v___x_1501_ == 0)
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; 
v___x_1502_ = l_Lean_SourceInfo_fromRef(v_a_1480_, v___x_1501_);
v___x_1503_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__3));
v___x_1504_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__6));
lean_inc_n(v___x_1502_, 4);
v___x_1505_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1505_, 0, v___x_1502_);
lean_ctor_set(v___x_1505_, 1, v___x_1504_);
v___x_1506_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__12));
v___x_1507_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1507_, 0, v___x_1502_);
lean_ctor_set(v___x_1507_, 1, v___x_1506_);
v___x_1508_ = l_Lean_Syntax_node3(v___x_1502_, v___x_1503_, v___x_1505_, v___x_1493_, v___x_1507_);
v___x_1509_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_1510_ = l_Array_append___redArg(v___x_1509_, v_ts_1499_);
lean_dec_ref(v_ts_1499_);
v___x_1511_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1502_);
lean_ctor_set(v___x_1511_, 1, v___x_1496_);
lean_ctor_set(v___x_1511_, 2, v___x_1510_);
v___x_1512_ = l_Lean_Syntax_node2(v___x_1502_, v___x_1482_, v___x_1508_, v___x_1511_);
v___x_1513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1513_, 0, v___x_1512_);
lean_ctor_set(v___x_1513_, 1, v_a_1481_);
return v___x_1513_;
}
else
{
uint8_t v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
lean_dec_ref(v_ts_1499_);
v___x_1514_ = 0;
v___x_1515_ = l_Lean_SourceInfo_fromRef(v_a_1480_, v___x_1514_);
v___x_1516_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__3));
v___x_1517_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__6));
lean_inc_n(v___x_1515_, 2);
v___x_1518_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1518_, 0, v___x_1515_);
lean_ctor_set(v___x_1518_, 1, v___x_1517_);
v___x_1519_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__12));
v___x_1520_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1515_);
lean_ctor_set(v___x_1520_, 1, v___x_1519_);
v___x_1521_ = l_Lean_Syntax_node3(v___x_1515_, v___x_1516_, v___x_1518_, v___x_1493_, v___x_1520_);
v___x_1522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1522_, 0, v___x_1521_);
lean_ctor_set(v___x_1522_, 1, v_a_1481_);
return v___x_1522_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandPure___boxed(lean_object* v_x_1523_, lean_object* v_a_1524_, lean_object* v_a_1525_){
_start:
{
lean_object* v_res_1526_; 
v_res_1526_ = l_Std_Do_SPred_Notation_unexpandPure(v_x_1523_, v_a_1524_, v_a_1525_);
lean_dec(v_a_1524_);
return v_res_1526_;
}
}
static lean_object* _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6(void){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1539_ = lean_unsigned_to_nat(0u);
v___x_1540_ = lean_box(0);
v___x_1541_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__5));
v___x_1542_ = l_Lean_addMacroScope(v___x_1541_, v___x_1540_, v___x_1539_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(lean_object* v_x_1569_, lean_object* v___y_1570_, lean_object* v___y_1571_){
_start:
{
lean_object* v___x_1572_; uint8_t v___x_1573_; 
v___x_1572_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
lean_inc(v_x_1569_);
v___x_1573_ = l_Lean_Syntax_isOfKind(v_x_1569_, v___x_1572_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; uint8_t v___x_1575_; 
v___x_1574_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__21));
lean_inc(v_x_1569_);
v___x_1575_ = l_Lean_Syntax_isOfKind(v_x_1569_, v___x_1574_);
if (v___x_1575_ == 0)
{
lean_object* v___x_1576_; uint8_t v___x_1577_; 
v___x_1576_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__1));
lean_inc(v_x_1569_);
v___x_1577_ = l_Lean_Syntax_isOfKind(v_x_1569_, v___x_1576_);
if (v___x_1577_ == 0)
{
lean_object* v___x_1578_; lean_object* v___x_1579_; uint8_t v___x_1580_; 
v___x_1578_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__46));
v___x_1579_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
lean_inc(v_x_1569_);
v___x_1580_ = l_Lean_Syntax_isOfKind(v_x_1569_, v___x_1579_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1581_; uint8_t v___x_1582_; 
v___x_1581_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__3));
lean_inc(v_x_1569_);
v___x_1582_ = l_Lean_Syntax_isOfKind(v_x_1569_, v___x_1581_);
if (v___x_1582_ == 0)
{
lean_object* v___x_1583_; 
v___x_1583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1583_, 0, v_x_1569_);
lean_ctor_set(v___x_1583_, 1, v___y_1571_);
return v___x_1583_;
}
else
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; uint8_t v___x_1587_; 
v___x_1584_ = lean_unsigned_to_nat(0u);
v___x_1585_ = l_Lean_Syntax_getArg(v_x_1569_, v___x_1584_);
v___x_1586_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
lean_inc(v___x_1585_);
v___x_1587_ = l_Lean_Syntax_isOfKind(v___x_1585_, v___x_1586_);
if (v___x_1587_ == 0)
{
lean_object* v___x_1588_; 
lean_dec(v___x_1585_);
v___x_1588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1588_, 0, v_x_1569_);
lean_ctor_set(v___x_1588_, 1, v___y_1571_);
return v___x_1588_;
}
else
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; uint8_t v___x_1592_; 
v___x_1589_ = lean_unsigned_to_nat(1u);
v___x_1590_ = l_Lean_Syntax_getArg(v___x_1585_, v___x_1589_);
lean_dec(v___x_1585_);
v___x_1591_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
lean_inc(v___x_1590_);
v___x_1592_ = l_Lean_Syntax_isOfKind(v___x_1590_, v___x_1591_);
if (v___x_1592_ == 0)
{
lean_object* v___x_1593_; 
lean_dec(v___x_1590_);
v___x_1593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1593_, 0, v_x_1569_);
lean_ctor_set(v___x_1593_, 1, v___y_1571_);
return v___x_1593_;
}
else
{
lean_object* v___x_1594_; lean_object* v___x_1595_; uint8_t v___x_1596_; 
v___x_1594_ = l_Lean_Syntax_getArg(v___x_1590_, v___x_1584_);
lean_dec(v___x_1590_);
v___x_1595_ = lean_box(0);
v___x_1596_ = l_Lean_Syntax_matchesIdent(v___x_1594_, v___x_1595_);
lean_dec(v___x_1594_);
if (v___x_1596_ == 0)
{
lean_object* v___x_1597_; 
v___x_1597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1597_, 0, v_x_1569_);
lean_ctor_set(v___x_1597_, 1, v___y_1571_);
return v___x_1597_;
}
else
{
lean_object* v___x_1598_; lean_object* v___x_1599_; uint8_t v___x_1600_; 
v___x_1598_ = lean_unsigned_to_nat(3u);
v___x_1599_ = l_Lean_Syntax_getArg(v_x_1569_, v___x_1598_);
lean_inc(v___x_1599_);
v___x_1600_ = l_Lean_Syntax_matchesNull(v___x_1599_, v___x_1589_);
if (v___x_1600_ == 0)
{
lean_object* v___x_1601_; 
lean_dec(v___x_1599_);
v___x_1601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1601_, 0, v_x_1569_);
lean_ctor_set(v___x_1601_, 1, v___y_1571_);
return v___x_1601_;
}
else
{
lean_object* v_P_1602_; lean_object* v___x_1603_; 
v_P_1602_ = l_Lean_Syntax_getArg(v_x_1569_, v___x_1589_);
lean_dec(v_x_1569_);
v___x_1603_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_1602_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1603_) == 0)
{
lean_object* v_a_1604_; lean_object* v_a_1605_; lean_object* v___x_1607_; uint8_t v_isShared_1608_; uint8_t v_isSharedCheck_1629_; 
v_a_1604_ = lean_ctor_get(v___x_1603_, 0);
v_a_1605_ = lean_ctor_get(v___x_1603_, 1);
v_isSharedCheck_1629_ = !lean_is_exclusive(v___x_1603_);
if (v_isSharedCheck_1629_ == 0)
{
v___x_1607_ = v___x_1603_;
v_isShared_1608_ = v_isSharedCheck_1629_;
goto v_resetjp_1606_;
}
else
{
lean_inc(v_a_1605_);
lean_inc(v_a_1604_);
lean_dec(v___x_1603_);
v___x_1607_ = lean_box(0);
v_isShared_1608_ = v_isSharedCheck_1629_;
goto v_resetjp_1606_;
}
v_resetjp_1606_:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1627_; 
v___x_1609_ = l_Lean_Syntax_getArg(v___x_1599_, v___x_1584_);
lean_dec(v___x_1599_);
v___x_1610_ = l_Lean_SourceInfo_fromRef(v___y_1570_, v___x_1580_);
v___x_1611_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
lean_inc_n(v___x_1610_, 7);
v___x_1612_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1612_, 0, v___x_1610_);
lean_ctor_set(v___x_1612_, 1, v___x_1611_);
v___x_1613_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_1614_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6, &l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6_once, _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6);
v___x_1615_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__14));
v___x_1616_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1616_, 0, v___x_1610_);
lean_ctor_set(v___x_1616_, 1, v___x_1613_);
lean_ctor_set(v___x_1616_, 2, v___x_1614_);
lean_ctor_set(v___x_1616_, 3, v___x_1615_);
v___x_1617_ = l_Lean_Syntax_node1(v___x_1610_, v___x_1591_, v___x_1616_);
v___x_1618_ = l_Lean_Syntax_node2(v___x_1610_, v___x_1586_, v___x_1612_, v___x_1617_);
v___x_1619_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__56));
v___x_1620_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1620_, 0, v___x_1610_);
lean_ctor_set(v___x_1620_, 1, v___x_1619_);
v___x_1621_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1622_ = l_Lean_Syntax_node1(v___x_1610_, v___x_1621_, v___x_1609_);
v___x_1623_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1624_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1624_, 0, v___x_1610_);
lean_ctor_set(v___x_1624_, 1, v___x_1623_);
v___x_1625_ = l_Lean_Syntax_node5(v___x_1610_, v___x_1581_, v___x_1618_, v_a_1604_, v___x_1620_, v___x_1622_, v___x_1624_);
if (v_isShared_1608_ == 0)
{
lean_ctor_set(v___x_1607_, 0, v___x_1625_);
v___x_1627_ = v___x_1607_;
goto v_reusejp_1626_;
}
else
{
lean_object* v_reuseFailAlloc_1628_; 
v_reuseFailAlloc_1628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1628_, 0, v___x_1625_);
lean_ctor_set(v_reuseFailAlloc_1628_, 1, v_a_1605_);
v___x_1627_ = v_reuseFailAlloc_1628_;
goto v_reusejp_1626_;
}
v_reusejp_1626_:
{
return v___x_1627_;
}
}
}
else
{
lean_dec(v___x_1599_);
return v___x_1603_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; uint8_t v___x_1633_; 
v___x_1630_ = lean_unsigned_to_nat(1u);
v___x_1631_ = l_Lean_Syntax_getArg(v_x_1569_, v___x_1630_);
v___x_1632_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
lean_inc(v___x_1631_);
v___x_1633_ = l_Lean_Syntax_isOfKind(v___x_1631_, v___x_1632_);
if (v___x_1633_ == 0)
{
lean_object* v___x_1634_; 
lean_dec(v___x_1631_);
v___x_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1634_, 0, v_x_1569_);
lean_ctor_set(v___x_1634_, 1, v___y_1571_);
return v___x_1634_;
}
else
{
lean_object* v___x_1635_; lean_object* v___x_1636_; uint8_t v___x_1637_; 
v___x_1635_ = lean_unsigned_to_nat(0u);
v___x_1636_ = l_Lean_Syntax_getArg(v___x_1631_, v___x_1630_);
v___x_1637_ = l_Lean_Syntax_matchesNull(v___x_1636_, v___x_1635_);
if (v___x_1637_ == 0)
{
lean_object* v___x_1638_; 
lean_dec(v___x_1631_);
v___x_1638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1638_, 0, v_x_1569_);
lean_ctor_set(v___x_1638_, 1, v___y_1571_);
return v___x_1638_;
}
else
{
lean_object* v___x_1639_; lean_object* v_b_1640_; lean_object* v___x_1641_; 
lean_dec(v_x_1569_);
v___x_1639_ = lean_unsigned_to_nat(3u);
v_b_1640_ = l_Lean_Syntax_getArg(v___x_1631_, v___x_1639_);
v___x_1641_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_b_1640_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1641_) == 0)
{
lean_object* v_a_1642_; lean_object* v_a_1643_; lean_object* v___x_1645_; uint8_t v_isShared_1646_; uint8_t v_isSharedCheck_1663_; 
v_a_1642_ = lean_ctor_get(v___x_1641_, 0);
v_a_1643_ = lean_ctor_get(v___x_1641_, 1);
v_isSharedCheck_1663_ = !lean_is_exclusive(v___x_1641_);
if (v_isSharedCheck_1663_ == 0)
{
v___x_1645_ = v___x_1641_;
v_isShared_1646_ = v_isSharedCheck_1663_;
goto v_resetjp_1644_;
}
else
{
lean_inc(v_a_1643_);
lean_inc(v_a_1642_);
lean_dec(v___x_1641_);
v___x_1645_ = lean_box(0);
v_isShared_1646_ = v_isSharedCheck_1663_;
goto v_resetjp_1644_;
}
v_resetjp_1644_:
{
lean_object* v___x_1647_; lean_object* v_xs_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1661_; 
v___x_1647_ = l_Lean_Syntax_getArg(v___x_1631_, v___x_1635_);
lean_dec(v___x_1631_);
v_xs_1648_ = l_Lean_Syntax_getArgs(v___x_1647_);
lean_dec(v___x_1647_);
v___x_1649_ = l_Lean_SourceInfo_fromRef(v___y_1570_, v___x_1577_);
lean_inc_n(v___x_1649_, 5);
v___x_1650_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1650_, 0, v___x_1649_);
lean_ctor_set(v___x_1650_, 1, v___x_1578_);
v___x_1651_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_1652_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_1653_ = l_Array_append___redArg(v___x_1652_, v_xs_1648_);
lean_dec_ref(v_xs_1648_);
v___x_1654_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1654_, 0, v___x_1649_);
lean_ctor_set(v___x_1654_, 1, v___x_1651_);
lean_ctor_set(v___x_1654_, 2, v___x_1653_);
v___x_1655_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1655_, 0, v___x_1649_);
lean_ctor_set(v___x_1655_, 1, v___x_1651_);
lean_ctor_set(v___x_1655_, 2, v___x_1652_);
v___x_1656_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__51));
v___x_1657_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1657_, 0, v___x_1649_);
lean_ctor_set(v___x_1657_, 1, v___x_1656_);
v___x_1658_ = l_Lean_Syntax_node4(v___x_1649_, v___x_1632_, v___x_1654_, v___x_1655_, v___x_1657_, v_a_1642_);
v___x_1659_ = l_Lean_Syntax_node2(v___x_1649_, v___x_1579_, v___x_1650_, v___x_1658_);
if (v_isShared_1646_ == 0)
{
lean_ctor_set(v___x_1645_, 0, v___x_1659_);
v___x_1661_ = v___x_1645_;
goto v_reusejp_1660_;
}
else
{
lean_object* v_reuseFailAlloc_1662_; 
v_reuseFailAlloc_1662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1662_, 0, v___x_1659_);
lean_ctor_set(v_reuseFailAlloc_1662_, 1, v_a_1643_);
v___x_1661_ = v_reuseFailAlloc_1662_;
goto v_reusejp_1660_;
}
v_reusejp_1660_:
{
return v___x_1661_;
}
}
}
else
{
lean_dec(v___x_1631_);
return v___x_1641_;
}
}
}
}
}
else
{
lean_object* v___x_1664_; lean_object* v_t_1665_; lean_object* v___x_1666_; 
v___x_1664_ = lean_unsigned_to_nat(3u);
v_t_1665_ = l_Lean_Syntax_getArg(v_x_1569_, v___x_1664_);
v___x_1666_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_t_1665_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1666_) == 0)
{
lean_object* v_a_1667_; lean_object* v_a_1668_; lean_object* v___x_1670_; uint8_t v_isShared_1671_; uint8_t v_isSharedCheck_1696_; 
v_a_1667_ = lean_ctor_get(v___x_1666_, 0);
v_a_1668_ = lean_ctor_get(v___x_1666_, 1);
v_isSharedCheck_1696_ = !lean_is_exclusive(v___x_1666_);
if (v_isSharedCheck_1696_ == 0)
{
v___x_1670_ = v___x_1666_;
v_isShared_1671_ = v_isSharedCheck_1696_;
goto v_resetjp_1669_;
}
else
{
lean_inc(v_a_1668_);
lean_inc(v_a_1667_);
lean_dec(v___x_1666_);
v___x_1670_ = lean_box(0);
v_isShared_1671_ = v_isSharedCheck_1696_;
goto v_resetjp_1669_;
}
v_resetjp_1669_:
{
lean_object* v___x_1672_; lean_object* v_e_1673_; lean_object* v___x_1674_; 
v___x_1672_ = lean_unsigned_to_nat(5u);
v_e_1673_ = l_Lean_Syntax_getArg(v_x_1569_, v___x_1672_);
v___x_1674_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_e_1673_, v___y_1570_, v_a_1668_);
if (lean_obj_tag(v___x_1674_) == 0)
{
lean_object* v_a_1675_; lean_object* v_a_1676_; lean_object* v___x_1678_; uint8_t v_isShared_1679_; uint8_t v_isSharedCheck_1695_; 
v_a_1675_ = lean_ctor_get(v___x_1674_, 0);
v_a_1676_ = lean_ctor_get(v___x_1674_, 1);
v_isSharedCheck_1695_ = !lean_is_exclusive(v___x_1674_);
if (v_isSharedCheck_1695_ == 0)
{
v___x_1678_ = v___x_1674_;
v_isShared_1679_ = v_isSharedCheck_1695_;
goto v_resetjp_1677_;
}
else
{
lean_inc(v_a_1676_);
lean_inc(v_a_1675_);
lean_dec(v___x_1674_);
v___x_1678_ = lean_box(0);
v_isShared_1679_ = v_isSharedCheck_1695_;
goto v_resetjp_1677_;
}
v_resetjp_1677_:
{
lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1685_; 
v___x_1680_ = lean_unsigned_to_nat(1u);
v___x_1681_ = l_Lean_Syntax_getArg(v_x_1569_, v___x_1680_);
lean_dec(v_x_1569_);
v___x_1682_ = l_Lean_SourceInfo_fromRef(v___y_1570_, v___x_1575_);
v___x_1683_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__15));
lean_inc(v___x_1682_);
if (v_isShared_1671_ == 0)
{
lean_ctor_set_tag(v___x_1670_, 2);
lean_ctor_set(v___x_1670_, 1, v___x_1683_);
lean_ctor_set(v___x_1670_, 0, v___x_1682_);
v___x_1685_ = v___x_1670_;
goto v_reusejp_1684_;
}
else
{
lean_object* v_reuseFailAlloc_1694_; 
v_reuseFailAlloc_1694_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1694_, 0, v___x_1682_);
lean_ctor_set(v_reuseFailAlloc_1694_, 1, v___x_1683_);
v___x_1685_ = v_reuseFailAlloc_1694_;
goto v_reusejp_1684_;
}
v_reusejp_1684_:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1692_; 
v___x_1686_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__16));
lean_inc_n(v___x_1682_, 2);
v___x_1687_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1687_, 0, v___x_1682_);
lean_ctor_set(v___x_1687_, 1, v___x_1686_);
v___x_1688_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__17));
v___x_1689_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1689_, 0, v___x_1682_);
lean_ctor_set(v___x_1689_, 1, v___x_1688_);
v___x_1690_ = l_Lean_Syntax_node6(v___x_1682_, v___x_1576_, v___x_1685_, v___x_1681_, v___x_1687_, v_a_1667_, v___x_1689_, v_a_1675_);
if (v_isShared_1679_ == 0)
{
lean_ctor_set(v___x_1678_, 0, v___x_1690_);
v___x_1692_ = v___x_1678_;
goto v_reusejp_1691_;
}
else
{
lean_object* v_reuseFailAlloc_1693_; 
v_reuseFailAlloc_1693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1693_, 0, v___x_1690_);
lean_ctor_set(v_reuseFailAlloc_1693_, 1, v_a_1676_);
v___x_1692_ = v_reuseFailAlloc_1693_;
goto v_reusejp_1691_;
}
v_reusejp_1691_:
{
return v___x_1692_;
}
}
}
}
else
{
lean_del_object(v___x_1670_);
lean_dec(v_a_1667_);
lean_dec(v_x_1569_);
return v___x_1674_;
}
}
}
else
{
lean_dec(v_x_1569_);
return v___x_1666_;
}
}
}
else
{
lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; uint8_t v___x_1700_; 
v___x_1697_ = lean_unsigned_to_nat(0u);
v___x_1698_ = l_Lean_Syntax_getArg(v_x_1569_, v___x_1697_);
v___x_1699_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__23));
lean_inc(v___x_1698_);
v___x_1700_ = l_Lean_Syntax_isOfKind(v___x_1698_, v___x_1699_);
if (v___x_1700_ == 0)
{
lean_object* v___x_1701_; 
lean_dec(v___x_1698_);
v___x_1701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1701_, 0, v_x_1569_);
lean_ctor_set(v___x_1701_, 1, v___y_1571_);
return v___x_1701_;
}
else
{
lean_object* v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; uint8_t v___x_1705_; 
v___x_1702_ = lean_unsigned_to_nat(1u);
v___x_1703_ = l_Lean_Syntax_getArg(v___x_1698_, v___x_1702_);
lean_dec(v___x_1698_);
v___x_1704_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__26));
lean_inc(v___x_1703_);
v___x_1705_ = l_Lean_Syntax_isOfKind(v___x_1703_, v___x_1704_);
if (v___x_1705_ == 0)
{
lean_object* v___x_1706_; 
lean_dec(v___x_1703_);
v___x_1706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1706_, 0, v_x_1569_);
lean_ctor_set(v___x_1706_, 1, v___y_1571_);
return v___x_1706_;
}
else
{
lean_object* v___x_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v___x_1707_ = l_Lean_Syntax_getArg(v___x_1703_, v___x_1697_);
lean_dec(v___x_1703_);
v___x_1708_ = lean_box(0);
v___x_1709_ = l_Lean_Syntax_matchesIdent(v___x_1707_, v___x_1708_);
lean_dec(v___x_1707_);
if (v___x_1709_ == 0)
{
lean_object* v___x_1710_; 
v___x_1710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1710_, 0, v_x_1569_);
lean_ctor_set(v___x_1710_, 1, v___y_1571_);
return v___x_1710_;
}
else
{
lean_object* v_P_1711_; lean_object* v___x_1712_; 
v_P_1711_ = l_Lean_Syntax_getArg(v_x_1569_, v___x_1702_);
lean_dec(v_x_1569_);
v___x_1712_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_1711_, v___y_1570_, v___y_1571_);
if (lean_obj_tag(v___x_1712_) == 0)
{
lean_object* v_a_1713_; lean_object* v_a_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1733_; 
v_a_1713_ = lean_ctor_get(v___x_1712_, 0);
v_a_1714_ = lean_ctor_get(v___x_1712_, 1);
v_isSharedCheck_1733_ = !lean_is_exclusive(v___x_1712_);
if (v_isSharedCheck_1733_ == 0)
{
v___x_1716_ = v___x_1712_;
v_isShared_1717_ = v_isSharedCheck_1733_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_a_1714_);
lean_inc(v_a_1713_);
lean_dec(v___x_1712_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1733_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1731_; 
v___x_1718_ = l_Lean_SourceInfo_fromRef(v___y_1570_, v___x_1573_);
v___x_1719_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__24));
lean_inc_n(v___x_1718_, 5);
v___x_1720_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1718_);
lean_ctor_set(v___x_1720_, 1, v___x_1719_);
v___x_1721_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__28);
v___x_1722_ = lean_obj_once(&l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6, &l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6_once, _init_l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__6);
v___x_1723_ = ((lean_object*)(l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___closed__14));
v___x_1724_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1724_, 0, v___x_1718_);
lean_ctor_set(v___x_1724_, 1, v___x_1721_);
lean_ctor_set(v___x_1724_, 2, v___x_1722_);
lean_ctor_set(v___x_1724_, 3, v___x_1723_);
v___x_1725_ = l_Lean_Syntax_node1(v___x_1718_, v___x_1704_, v___x_1724_);
v___x_1726_ = l_Lean_Syntax_node2(v___x_1718_, v___x_1699_, v___x_1720_, v___x_1725_);
v___x_1727_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1728_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1728_, 0, v___x_1718_);
lean_ctor_set(v___x_1728_, 1, v___x_1727_);
v___x_1729_ = l_Lean_Syntax_node3(v___x_1718_, v___x_1574_, v___x_1726_, v_a_1713_, v___x_1728_);
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 0, v___x_1729_);
v___x_1731_ = v___x_1716_;
goto v_reusejp_1730_;
}
else
{
lean_object* v_reuseFailAlloc_1732_; 
v_reuseFailAlloc_1732_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1732_, 0, v___x_1729_);
lean_ctor_set(v_reuseFailAlloc_1732_, 1, v_a_1714_);
v___x_1731_ = v_reuseFailAlloc_1732_;
goto v_reusejp_1730_;
}
v_reusejp_1730_:
{
return v___x_1731_;
}
}
}
else
{
return v___x_1712_;
}
}
}
}
}
}
else
{
lean_object* v___x_1734_; lean_object* v___x_1735_; lean_object* v___x_1736_; 
v___x_1734_ = lean_unsigned_to_nat(1u);
v___x_1735_ = l_Lean_Syntax_getArg(v_x_1569_, v___x_1734_);
lean_dec(v_x_1569_);
v___x_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1736_, 0, v___x_1735_);
lean_ctor_set(v___x_1736_, 1, v___y_1571_);
return v___x_1736_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0___boxed(lean_object* v_x_1737_, lean_object* v___y_1738_, lean_object* v___y_1739_){
_start:
{
lean_object* v_res_1740_; 
v_res_1740_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_x_1737_, v___y_1738_, v___y_1739_);
lean_dec(v___y_1738_);
return v_res_1740_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandEntails(lean_object* v_x_1742_, lean_object* v_a_1743_, lean_object* v_a_1744_){
_start:
{
lean_object* v___x_1745_; uint8_t v___x_1746_; 
v___x_1745_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_1742_);
v___x_1746_ = l_Lean_Syntax_isOfKind(v_x_1742_, v___x_1745_);
if (v___x_1746_ == 0)
{
lean_object* v___x_1747_; lean_object* v___x_1748_; 
lean_dec(v_x_1742_);
v___x_1747_ = lean_box(0);
v___x_1748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1748_, 0, v___x_1747_);
lean_ctor_set(v___x_1748_, 1, v_a_1744_);
return v___x_1748_;
}
else
{
lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; uint8_t v___x_1752_; 
v___x_1749_ = lean_unsigned_to_nat(1u);
v___x_1750_ = l_Lean_Syntax_getArg(v_x_1742_, v___x_1749_);
lean_dec(v_x_1742_);
v___x_1751_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1750_);
v___x_1752_ = l_Lean_Syntax_matchesNull(v___x_1750_, v___x_1751_);
if (v___x_1752_ == 0)
{
lean_object* v___x_1753_; lean_object* v___x_1754_; 
lean_dec(v___x_1750_);
v___x_1753_ = lean_box(0);
v___x_1754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1754_, 0, v___x_1753_);
lean_ctor_set(v___x_1754_, 1, v_a_1744_);
return v___x_1754_;
}
else
{
lean_object* v___x_1755_; lean_object* v_P_1756_; lean_object* v___x_1757_; 
v___x_1755_ = lean_unsigned_to_nat(0u);
v_P_1756_ = l_Lean_Syntax_getArg(v___x_1750_, v___x_1755_);
v___x_1757_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_1756_, v_a_1743_, v_a_1744_);
if (lean_obj_tag(v___x_1757_) == 0)
{
lean_object* v_a_1758_; lean_object* v_a_1759_; lean_object* v_Q_1760_; lean_object* v___x_1761_; 
v_a_1758_ = lean_ctor_get(v___x_1757_, 0);
lean_inc(v_a_1758_);
v_a_1759_ = lean_ctor_get(v___x_1757_, 1);
lean_inc(v_a_1759_);
lean_dec_ref_known(v___x_1757_, 2);
v_Q_1760_ = l_Lean_Syntax_getArg(v___x_1750_, v___x_1749_);
lean_dec(v___x_1750_);
v___x_1761_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_1760_, v_a_1743_, v_a_1759_);
if (lean_obj_tag(v___x_1761_) == 0)
{
lean_object* v_a_1762_; lean_object* v_a_1763_; lean_object* v___x_1765_; uint8_t v_isShared_1766_; uint8_t v_isSharedCheck_1797_; 
v_a_1762_ = lean_ctor_get(v___x_1761_, 0);
v_a_1763_ = lean_ctor_get(v___x_1761_, 1);
v_isSharedCheck_1797_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1797_ == 0)
{
v___x_1765_ = v___x_1761_;
v_isShared_1766_ = v_isSharedCheck_1797_;
goto v_resetjp_1764_;
}
else
{
lean_inc(v_a_1763_);
lean_inc(v_a_1762_);
lean_dec(v___x_1761_);
v___x_1765_ = lean_box(0);
v_isShared_1766_ = v_isSharedCheck_1797_;
goto v_resetjp_1764_;
}
v_resetjp_1764_:
{
lean_object* v___x_1767_; uint8_t v___x_1768_; 
v___x_1767_ = ((lean_object*)(l_Std_Do_term_u231c___u231d___closed__3));
lean_inc(v_a_1758_);
v___x_1768_ = l_Lean_Syntax_isOfKind(v_a_1758_, v___x_1767_);
if (v___x_1768_ == 0)
{
lean_object* v___x_1769_; lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1775_; 
v___x_1769_ = l_Lean_SourceInfo_fromRef(v_a_1743_, v___x_1768_);
v___x_1770_ = ((lean_object*)(l_Std_Do_term___u22a2_u209b___00__closed__1));
v___x_1771_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandEntails___closed__0));
lean_inc(v___x_1769_);
v___x_1772_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1772_, 0, v___x_1769_);
lean_ctor_set(v___x_1772_, 1, v___x_1771_);
v___x_1773_ = l_Lean_Syntax_node3(v___x_1769_, v___x_1770_, v_a_1758_, v___x_1772_, v_a_1762_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1773_);
v___x_1775_ = v___x_1765_;
goto v_reusejp_1774_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v___x_1773_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v_a_1763_);
v___x_1775_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1774_;
}
v_reusejp_1774_:
{
return v___x_1775_;
}
}
else
{
lean_object* v___x_1777_; lean_object* v___x_1778_; uint8_t v___x_1779_; 
v___x_1777_ = l_Lean_Syntax_getArg(v_a_1758_, v___x_1749_);
v___x_1778_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u22a2_u209b____1___closed__2));
v___x_1779_ = l_Lean_Syntax_matchesIdent(v___x_1777_, v___x_1778_);
lean_dec(v___x_1777_);
if (v___x_1779_ == 0)
{
lean_object* v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1786_; 
v___x_1780_ = l_Lean_SourceInfo_fromRef(v_a_1743_, v___x_1779_);
v___x_1781_ = ((lean_object*)(l_Std_Do_term___u22a2_u209b___00__closed__1));
v___x_1782_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandEntails___closed__0));
lean_inc(v___x_1780_);
v___x_1783_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1783_, 0, v___x_1780_);
lean_ctor_set(v___x_1783_, 1, v___x_1782_);
v___x_1784_ = l_Lean_Syntax_node3(v___x_1780_, v___x_1781_, v_a_1758_, v___x_1783_, v_a_1762_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1784_);
v___x_1786_ = v___x_1765_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v___x_1784_);
lean_ctor_set(v_reuseFailAlloc_1787_, 1, v_a_1763_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
else
{
uint8_t v___x_1788_; lean_object* v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1795_; 
lean_dec(v_a_1758_);
v___x_1788_ = 0;
v___x_1789_ = l_Lean_SourceInfo_fromRef(v_a_1743_, v___x_1788_);
v___x_1790_ = ((lean_object*)(l_Std_Do_term_u22a2_u209b___00__closed__1));
v___x_1791_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandEntails___closed__0));
lean_inc(v___x_1789_);
v___x_1792_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1792_, 0, v___x_1789_);
lean_ctor_set(v___x_1792_, 1, v___x_1791_);
v___x_1793_ = l_Lean_Syntax_node2(v___x_1789_, v___x_1790_, v___x_1792_, v_a_1762_);
if (v_isShared_1766_ == 0)
{
lean_ctor_set(v___x_1765_, 0, v___x_1793_);
v___x_1795_ = v___x_1765_;
goto v_reusejp_1794_;
}
else
{
lean_object* v_reuseFailAlloc_1796_; 
v_reuseFailAlloc_1796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1796_, 0, v___x_1793_);
lean_ctor_set(v_reuseFailAlloc_1796_, 1, v_a_1763_);
v___x_1795_ = v_reuseFailAlloc_1796_;
goto v_reusejp_1794_;
}
v_reusejp_1794_:
{
return v___x_1795_;
}
}
}
}
}
else
{
lean_object* v_a_1798_; lean_object* v_a_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1806_; 
lean_dec(v_a_1758_);
v_a_1798_ = lean_ctor_get(v___x_1761_, 0);
v_a_1799_ = lean_ctor_get(v___x_1761_, 1);
v_isSharedCheck_1806_ = !lean_is_exclusive(v___x_1761_);
if (v_isSharedCheck_1806_ == 0)
{
v___x_1801_ = v___x_1761_;
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_a_1799_);
lean_inc(v_a_1798_);
lean_dec(v___x_1761_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1806_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1804_; 
if (v_isShared_1802_ == 0)
{
v___x_1804_ = v___x_1801_;
goto v_reusejp_1803_;
}
else
{
lean_object* v_reuseFailAlloc_1805_; 
v_reuseFailAlloc_1805_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1805_, 0, v_a_1798_);
lean_ctor_set(v_reuseFailAlloc_1805_, 1, v_a_1799_);
v___x_1804_ = v_reuseFailAlloc_1805_;
goto v_reusejp_1803_;
}
v_reusejp_1803_:
{
return v___x_1804_;
}
}
}
}
else
{
lean_object* v_a_1807_; lean_object* v_a_1808_; lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
lean_dec(v___x_1750_);
v_a_1807_ = lean_ctor_get(v___x_1757_, 0);
v_a_1808_ = lean_ctor_get(v___x_1757_, 1);
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1757_);
if (v_isSharedCheck_1815_ == 0)
{
v___x_1810_ = v___x_1757_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_inc(v_a_1808_);
lean_inc(v_a_1807_);
lean_dec(v___x_1757_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v_a_1807_);
lean_ctor_set(v_reuseFailAlloc_1814_, 1, v_a_1808_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandEntails___boxed(lean_object* v_x_1816_, lean_object* v_a_1817_, lean_object* v_a_1818_){
_start:
{
lean_object* v_res_1819_; 
v_res_1819_ = l_Std_Do_SPred_Notation_unexpandEntails(v_x_1816_, v_a_1817_, v_a_1818_);
lean_dec(v_a_1817_);
return v_res_1819_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandBientails(lean_object* v_x_1821_, lean_object* v_a_1822_, lean_object* v_a_1823_){
_start:
{
lean_object* v___x_1824_; uint8_t v___x_1825_; 
v___x_1824_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_1821_);
v___x_1825_ = l_Lean_Syntax_isOfKind(v_x_1821_, v___x_1824_);
if (v___x_1825_ == 0)
{
lean_object* v___x_1826_; lean_object* v___x_1827_; 
lean_dec(v_x_1821_);
v___x_1826_ = lean_box(0);
v___x_1827_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1827_, 0, v___x_1826_);
lean_ctor_set(v___x_1827_, 1, v_a_1823_);
return v___x_1827_;
}
else
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; uint8_t v___x_1831_; 
v___x_1828_ = lean_unsigned_to_nat(1u);
v___x_1829_ = l_Lean_Syntax_getArg(v_x_1821_, v___x_1828_);
lean_dec(v_x_1821_);
v___x_1830_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1829_);
v___x_1831_ = l_Lean_Syntax_matchesNull(v___x_1829_, v___x_1830_);
if (v___x_1831_ == 0)
{
lean_object* v___x_1832_; lean_object* v___x_1833_; 
lean_dec(v___x_1829_);
v___x_1832_ = lean_box(0);
v___x_1833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1833_, 0, v___x_1832_);
lean_ctor_set(v___x_1833_, 1, v_a_1823_);
return v___x_1833_;
}
else
{
lean_object* v___x_1834_; lean_object* v_P_1835_; lean_object* v___x_1836_; 
v___x_1834_ = lean_unsigned_to_nat(0u);
v_P_1835_ = l_Lean_Syntax_getArg(v___x_1829_, v___x_1834_);
v___x_1836_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_1835_, v_a_1822_, v_a_1823_);
if (lean_obj_tag(v___x_1836_) == 0)
{
lean_object* v_a_1837_; lean_object* v_a_1838_; lean_object* v_Q_1839_; lean_object* v___x_1840_; 
v_a_1837_ = lean_ctor_get(v___x_1836_, 0);
lean_inc(v_a_1837_);
v_a_1838_ = lean_ctor_get(v___x_1836_, 1);
lean_inc(v_a_1838_);
lean_dec_ref_known(v___x_1836_, 2);
v_Q_1839_ = l_Lean_Syntax_getArg(v___x_1829_, v___x_1828_);
lean_dec(v___x_1829_);
v___x_1840_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_1839_, v_a_1822_, v_a_1838_);
if (lean_obj_tag(v___x_1840_) == 0)
{
lean_object* v_a_1841_; lean_object* v_a_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1855_; 
v_a_1841_ = lean_ctor_get(v___x_1840_, 0);
v_a_1842_ = lean_ctor_get(v___x_1840_, 1);
v_isSharedCheck_1855_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1855_ == 0)
{
v___x_1844_ = v___x_1840_;
v_isShared_1845_ = v_isSharedCheck_1855_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_a_1842_);
lean_inc(v_a_1841_);
lean_dec(v___x_1840_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1855_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
uint8_t v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1853_; 
v___x_1846_ = 0;
v___x_1847_ = l_Lean_SourceInfo_fromRef(v_a_1822_, v___x_1846_);
v___x_1848_ = ((lean_object*)(l_Std_Do_term___u22a3_u22a2_u209b___00__closed__1));
v___x_1849_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandBientails___closed__0));
lean_inc(v___x_1847_);
v___x_1850_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1847_);
lean_ctor_set(v___x_1850_, 1, v___x_1849_);
v___x_1851_ = l_Lean_Syntax_node3(v___x_1847_, v___x_1848_, v_a_1837_, v___x_1850_, v_a_1841_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 0, v___x_1851_);
v___x_1853_ = v___x_1844_;
goto v_reusejp_1852_;
}
else
{
lean_object* v_reuseFailAlloc_1854_; 
v_reuseFailAlloc_1854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1854_, 0, v___x_1851_);
lean_ctor_set(v_reuseFailAlloc_1854_, 1, v_a_1842_);
v___x_1853_ = v_reuseFailAlloc_1854_;
goto v_reusejp_1852_;
}
v_reusejp_1852_:
{
return v___x_1853_;
}
}
}
else
{
lean_object* v_a_1856_; lean_object* v_a_1857_; lean_object* v___x_1859_; uint8_t v_isShared_1860_; uint8_t v_isSharedCheck_1864_; 
lean_dec(v_a_1837_);
v_a_1856_ = lean_ctor_get(v___x_1840_, 0);
v_a_1857_ = lean_ctor_get(v___x_1840_, 1);
v_isSharedCheck_1864_ = !lean_is_exclusive(v___x_1840_);
if (v_isSharedCheck_1864_ == 0)
{
v___x_1859_ = v___x_1840_;
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
else
{
lean_inc(v_a_1857_);
lean_inc(v_a_1856_);
lean_dec(v___x_1840_);
v___x_1859_ = lean_box(0);
v_isShared_1860_ = v_isSharedCheck_1864_;
goto v_resetjp_1858_;
}
v_resetjp_1858_:
{
lean_object* v___x_1862_; 
if (v_isShared_1860_ == 0)
{
v___x_1862_ = v___x_1859_;
goto v_reusejp_1861_;
}
else
{
lean_object* v_reuseFailAlloc_1863_; 
v_reuseFailAlloc_1863_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1863_, 0, v_a_1856_);
lean_ctor_set(v_reuseFailAlloc_1863_, 1, v_a_1857_);
v___x_1862_ = v_reuseFailAlloc_1863_;
goto v_reusejp_1861_;
}
v_reusejp_1861_:
{
return v___x_1862_;
}
}
}
}
else
{
lean_object* v_a_1865_; lean_object* v_a_1866_; lean_object* v___x_1868_; uint8_t v_isShared_1869_; uint8_t v_isSharedCheck_1873_; 
lean_dec(v___x_1829_);
v_a_1865_ = lean_ctor_get(v___x_1836_, 0);
v_a_1866_ = lean_ctor_get(v___x_1836_, 1);
v_isSharedCheck_1873_ = !lean_is_exclusive(v___x_1836_);
if (v_isSharedCheck_1873_ == 0)
{
v___x_1868_ = v___x_1836_;
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
else
{
lean_inc(v_a_1866_);
lean_inc(v_a_1865_);
lean_dec(v___x_1836_);
v___x_1868_ = lean_box(0);
v_isShared_1869_ = v_isSharedCheck_1873_;
goto v_resetjp_1867_;
}
v_resetjp_1867_:
{
lean_object* v___x_1871_; 
if (v_isShared_1869_ == 0)
{
v___x_1871_ = v___x_1868_;
goto v_reusejp_1870_;
}
else
{
lean_object* v_reuseFailAlloc_1872_; 
v_reuseFailAlloc_1872_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1872_, 0, v_a_1865_);
lean_ctor_set(v_reuseFailAlloc_1872_, 1, v_a_1866_);
v___x_1871_ = v_reuseFailAlloc_1872_;
goto v_reusejp_1870_;
}
v_reusejp_1870_:
{
return v___x_1871_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandBientails___boxed(lean_object* v_x_1874_, lean_object* v_a_1875_, lean_object* v_a_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_Std_Do_SPred_Notation_unexpandBientails(v_x_1874_, v_a_1875_, v_a_1876_);
lean_dec(v_a_1875_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandAnd(lean_object* v_x_1879_, lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
lean_object* v___x_1882_; uint8_t v___x_1883_; 
v___x_1882_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_1879_);
v___x_1883_ = l_Lean_Syntax_isOfKind(v_x_1879_, v___x_1882_);
if (v___x_1883_ == 0)
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
lean_dec(v_x_1879_);
v___x_1884_ = lean_box(0);
v___x_1885_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1885_, 0, v___x_1884_);
lean_ctor_set(v___x_1885_, 1, v_a_1881_);
return v___x_1885_;
}
else
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; uint8_t v___x_1889_; 
v___x_1886_ = lean_unsigned_to_nat(1u);
v___x_1887_ = l_Lean_Syntax_getArg(v_x_1879_, v___x_1886_);
lean_dec(v_x_1879_);
v___x_1888_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1887_);
v___x_1889_ = l_Lean_Syntax_matchesNull(v___x_1887_, v___x_1888_);
if (v___x_1889_ == 0)
{
lean_object* v___x_1890_; lean_object* v___x_1891_; 
lean_dec(v___x_1887_);
v___x_1890_ = lean_box(0);
v___x_1891_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1891_, 0, v___x_1890_);
lean_ctor_set(v___x_1891_, 1, v_a_1881_);
return v___x_1891_;
}
else
{
lean_object* v___x_1892_; lean_object* v_P_1893_; lean_object* v___x_1894_; 
v___x_1892_ = lean_unsigned_to_nat(0u);
v_P_1893_ = l_Lean_Syntax_getArg(v___x_1887_, v___x_1892_);
v___x_1894_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_1893_, v_a_1880_, v_a_1881_);
if (lean_obj_tag(v___x_1894_) == 0)
{
lean_object* v_a_1895_; lean_object* v_a_1896_; lean_object* v_Q_1897_; lean_object* v___x_1898_; 
v_a_1895_ = lean_ctor_get(v___x_1894_, 0);
lean_inc(v_a_1895_);
v_a_1896_ = lean_ctor_get(v___x_1894_, 1);
lean_inc(v_a_1896_);
lean_dec_ref_known(v___x_1894_, 2);
v_Q_1897_ = l_Lean_Syntax_getArg(v___x_1887_, v___x_1886_);
lean_dec(v___x_1887_);
v___x_1898_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_1897_, v_a_1880_, v_a_1896_);
if (lean_obj_tag(v___x_1898_) == 0)
{
lean_object* v_a_1899_; lean_object* v_a_1900_; lean_object* v___x_1902_; uint8_t v_isShared_1903_; uint8_t v_isSharedCheck_1919_; 
v_a_1899_ = lean_ctor_get(v___x_1898_, 0);
v_a_1900_ = lean_ctor_get(v___x_1898_, 1);
v_isSharedCheck_1919_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1919_ == 0)
{
v___x_1902_ = v___x_1898_;
v_isShared_1903_ = v_isSharedCheck_1919_;
goto v_resetjp_1901_;
}
else
{
lean_inc(v_a_1900_);
lean_inc(v_a_1899_);
lean_dec(v___x_1898_);
v___x_1902_ = lean_box(0);
v_isShared_1903_ = v_isSharedCheck_1919_;
goto v_resetjp_1901_;
}
v_resetjp_1901_:
{
uint8_t v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1917_; 
v___x_1904_ = 0;
v___x_1905_ = l_Lean_SourceInfo_fromRef(v_a_1880_, v___x_1904_);
v___x_1906_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_1907_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_1905_, 4);
v___x_1908_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1908_, 0, v___x_1905_);
lean_ctor_set(v___x_1908_, 1, v___x_1907_);
v___x_1909_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__1));
v___x_1910_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandAnd___closed__0));
v___x_1911_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1905_);
lean_ctor_set(v___x_1911_, 1, v___x_1910_);
v___x_1912_ = l_Lean_Syntax_node3(v___x_1905_, v___x_1909_, v_a_1895_, v___x_1911_, v_a_1899_);
v___x_1913_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1914_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1914_, 0, v___x_1905_);
lean_ctor_set(v___x_1914_, 1, v___x_1913_);
v___x_1915_ = l_Lean_Syntax_node3(v___x_1905_, v___x_1906_, v___x_1908_, v___x_1912_, v___x_1914_);
if (v_isShared_1903_ == 0)
{
lean_ctor_set(v___x_1902_, 0, v___x_1915_);
v___x_1917_ = v___x_1902_;
goto v_reusejp_1916_;
}
else
{
lean_object* v_reuseFailAlloc_1918_; 
v_reuseFailAlloc_1918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1918_, 0, v___x_1915_);
lean_ctor_set(v_reuseFailAlloc_1918_, 1, v_a_1900_);
v___x_1917_ = v_reuseFailAlloc_1918_;
goto v_reusejp_1916_;
}
v_reusejp_1916_:
{
return v___x_1917_;
}
}
}
else
{
lean_object* v_a_1920_; lean_object* v_a_1921_; lean_object* v___x_1923_; uint8_t v_isShared_1924_; uint8_t v_isSharedCheck_1928_; 
lean_dec(v_a_1895_);
v_a_1920_ = lean_ctor_get(v___x_1898_, 0);
v_a_1921_ = lean_ctor_get(v___x_1898_, 1);
v_isSharedCheck_1928_ = !lean_is_exclusive(v___x_1898_);
if (v_isSharedCheck_1928_ == 0)
{
v___x_1923_ = v___x_1898_;
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
else
{
lean_inc(v_a_1921_);
lean_inc(v_a_1920_);
lean_dec(v___x_1898_);
v___x_1923_ = lean_box(0);
v_isShared_1924_ = v_isSharedCheck_1928_;
goto v_resetjp_1922_;
}
v_resetjp_1922_:
{
lean_object* v___x_1926_; 
if (v_isShared_1924_ == 0)
{
v___x_1926_ = v___x_1923_;
goto v_reusejp_1925_;
}
else
{
lean_object* v_reuseFailAlloc_1927_; 
v_reuseFailAlloc_1927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1927_, 0, v_a_1920_);
lean_ctor_set(v_reuseFailAlloc_1927_, 1, v_a_1921_);
v___x_1926_ = v_reuseFailAlloc_1927_;
goto v_reusejp_1925_;
}
v_reusejp_1925_:
{
return v___x_1926_;
}
}
}
}
else
{
lean_object* v_a_1929_; lean_object* v_a_1930_; lean_object* v___x_1932_; uint8_t v_isShared_1933_; uint8_t v_isSharedCheck_1937_; 
lean_dec(v___x_1887_);
v_a_1929_ = lean_ctor_get(v___x_1894_, 0);
v_a_1930_ = lean_ctor_get(v___x_1894_, 1);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1894_);
if (v_isSharedCheck_1937_ == 0)
{
v___x_1932_ = v___x_1894_;
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
else
{
lean_inc(v_a_1930_);
lean_inc(v_a_1929_);
lean_dec(v___x_1894_);
v___x_1932_ = lean_box(0);
v_isShared_1933_ = v_isSharedCheck_1937_;
goto v_resetjp_1931_;
}
v_resetjp_1931_:
{
lean_object* v___x_1935_; 
if (v_isShared_1933_ == 0)
{
v___x_1935_ = v___x_1932_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_a_1929_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_a_1930_);
v___x_1935_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
return v___x_1935_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandAnd___boxed(lean_object* v_x_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Std_Do_SPred_Notation_unexpandAnd(v_x_1938_, v_a_1939_, v_a_1940_);
lean_dec(v_a_1939_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandOr(lean_object* v_x_1943_, lean_object* v_a_1944_, lean_object* v_a_1945_){
_start:
{
lean_object* v___x_1946_; uint8_t v___x_1947_; 
v___x_1946_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_1943_);
v___x_1947_ = l_Lean_Syntax_isOfKind(v_x_1943_, v___x_1946_);
if (v___x_1947_ == 0)
{
lean_object* v___x_1948_; lean_object* v___x_1949_; 
lean_dec(v_x_1943_);
v___x_1948_ = lean_box(0);
v___x_1949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1949_, 0, v___x_1948_);
lean_ctor_set(v___x_1949_, 1, v_a_1945_);
return v___x_1949_;
}
else
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; uint8_t v___x_1953_; 
v___x_1950_ = lean_unsigned_to_nat(1u);
v___x_1951_ = l_Lean_Syntax_getArg(v_x_1943_, v___x_1950_);
lean_dec(v_x_1943_);
v___x_1952_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1951_);
v___x_1953_ = l_Lean_Syntax_matchesNull(v___x_1951_, v___x_1952_);
if (v___x_1953_ == 0)
{
lean_object* v___x_1954_; lean_object* v___x_1955_; 
lean_dec(v___x_1951_);
v___x_1954_ = lean_box(0);
v___x_1955_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1955_, 0, v___x_1954_);
lean_ctor_set(v___x_1955_, 1, v_a_1945_);
return v___x_1955_;
}
else
{
lean_object* v___x_1956_; lean_object* v_P_1957_; lean_object* v___x_1958_; 
v___x_1956_ = lean_unsigned_to_nat(0u);
v_P_1957_ = l_Lean_Syntax_getArg(v___x_1951_, v___x_1956_);
v___x_1958_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_1957_, v_a_1944_, v_a_1945_);
if (lean_obj_tag(v___x_1958_) == 0)
{
lean_object* v_a_1959_; lean_object* v_a_1960_; lean_object* v_Q_1961_; lean_object* v___x_1962_; 
v_a_1959_ = lean_ctor_get(v___x_1958_, 0);
lean_inc(v_a_1959_);
v_a_1960_ = lean_ctor_get(v___x_1958_, 1);
lean_inc(v_a_1960_);
lean_dec_ref_known(v___x_1958_, 2);
v_Q_1961_ = l_Lean_Syntax_getArg(v___x_1951_, v___x_1950_);
lean_dec(v___x_1951_);
v___x_1962_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_1961_, v_a_1944_, v_a_1960_);
if (lean_obj_tag(v___x_1962_) == 0)
{
lean_object* v_a_1963_; lean_object* v_a_1964_; lean_object* v___x_1966_; uint8_t v_isShared_1967_; uint8_t v_isSharedCheck_1983_; 
v_a_1963_ = lean_ctor_get(v___x_1962_, 0);
v_a_1964_ = lean_ctor_get(v___x_1962_, 1);
v_isSharedCheck_1983_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1983_ == 0)
{
v___x_1966_ = v___x_1962_;
v_isShared_1967_ = v_isSharedCheck_1983_;
goto v_resetjp_1965_;
}
else
{
lean_inc(v_a_1964_);
lean_inc(v_a_1963_);
lean_dec(v___x_1962_);
v___x_1966_ = lean_box(0);
v_isShared_1967_ = v_isSharedCheck_1983_;
goto v_resetjp_1965_;
}
v_resetjp_1965_:
{
uint8_t v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1981_; 
v___x_1968_ = 0;
v___x_1969_ = l_Lean_SourceInfo_fromRef(v_a_1944_, v___x_1968_);
v___x_1970_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_1971_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_1969_, 4);
v___x_1972_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1972_, 0, v___x_1969_);
lean_ctor_set(v___x_1972_, 1, v___x_1971_);
v___x_1973_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__3));
v___x_1974_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandOr___closed__0));
v___x_1975_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1975_, 0, v___x_1969_);
lean_ctor_set(v___x_1975_, 1, v___x_1974_);
v___x_1976_ = l_Lean_Syntax_node3(v___x_1969_, v___x_1973_, v_a_1959_, v___x_1975_, v_a_1963_);
v___x_1977_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_1978_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1978_, 0, v___x_1969_);
lean_ctor_set(v___x_1978_, 1, v___x_1977_);
v___x_1979_ = l_Lean_Syntax_node3(v___x_1969_, v___x_1970_, v___x_1972_, v___x_1976_, v___x_1978_);
if (v_isShared_1967_ == 0)
{
lean_ctor_set(v___x_1966_, 0, v___x_1979_);
v___x_1981_ = v___x_1966_;
goto v_reusejp_1980_;
}
else
{
lean_object* v_reuseFailAlloc_1982_; 
v_reuseFailAlloc_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1982_, 0, v___x_1979_);
lean_ctor_set(v_reuseFailAlloc_1982_, 1, v_a_1964_);
v___x_1981_ = v_reuseFailAlloc_1982_;
goto v_reusejp_1980_;
}
v_reusejp_1980_:
{
return v___x_1981_;
}
}
}
else
{
lean_object* v_a_1984_; lean_object* v_a_1985_; lean_object* v___x_1987_; uint8_t v_isShared_1988_; uint8_t v_isSharedCheck_1992_; 
lean_dec(v_a_1959_);
v_a_1984_ = lean_ctor_get(v___x_1962_, 0);
v_a_1985_ = lean_ctor_get(v___x_1962_, 1);
v_isSharedCheck_1992_ = !lean_is_exclusive(v___x_1962_);
if (v_isSharedCheck_1992_ == 0)
{
v___x_1987_ = v___x_1962_;
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
else
{
lean_inc(v_a_1985_);
lean_inc(v_a_1984_);
lean_dec(v___x_1962_);
v___x_1987_ = lean_box(0);
v_isShared_1988_ = v_isSharedCheck_1992_;
goto v_resetjp_1986_;
}
v_resetjp_1986_:
{
lean_object* v___x_1990_; 
if (v_isShared_1988_ == 0)
{
v___x_1990_ = v___x_1987_;
goto v_reusejp_1989_;
}
else
{
lean_object* v_reuseFailAlloc_1991_; 
v_reuseFailAlloc_1991_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1991_, 0, v_a_1984_);
lean_ctor_set(v_reuseFailAlloc_1991_, 1, v_a_1985_);
v___x_1990_ = v_reuseFailAlloc_1991_;
goto v_reusejp_1989_;
}
v_reusejp_1989_:
{
return v___x_1990_;
}
}
}
}
else
{
lean_object* v_a_1993_; lean_object* v_a_1994_; lean_object* v___x_1996_; uint8_t v_isShared_1997_; uint8_t v_isSharedCheck_2001_; 
lean_dec(v___x_1951_);
v_a_1993_ = lean_ctor_get(v___x_1958_, 0);
v_a_1994_ = lean_ctor_get(v___x_1958_, 1);
v_isSharedCheck_2001_ = !lean_is_exclusive(v___x_1958_);
if (v_isSharedCheck_2001_ == 0)
{
v___x_1996_ = v___x_1958_;
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
else
{
lean_inc(v_a_1994_);
lean_inc(v_a_1993_);
lean_dec(v___x_1958_);
v___x_1996_ = lean_box(0);
v_isShared_1997_ = v_isSharedCheck_2001_;
goto v_resetjp_1995_;
}
v_resetjp_1995_:
{
lean_object* v___x_1999_; 
if (v_isShared_1997_ == 0)
{
v___x_1999_ = v___x_1996_;
goto v_reusejp_1998_;
}
else
{
lean_object* v_reuseFailAlloc_2000_; 
v_reuseFailAlloc_2000_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2000_, 0, v_a_1993_);
lean_ctor_set(v_reuseFailAlloc_2000_, 1, v_a_1994_);
v___x_1999_ = v_reuseFailAlloc_2000_;
goto v_reusejp_1998_;
}
v_reusejp_1998_:
{
return v___x_1999_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandOr___boxed(lean_object* v_x_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_){
_start:
{
lean_object* v_res_2005_; 
v_res_2005_ = l_Std_Do_SPred_Notation_unexpandOr(v_x_2002_, v_a_2003_, v_a_2004_);
lean_dec(v_a_2003_);
return v_res_2005_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandNot(lean_object* v_x_2007_, lean_object* v_a_2008_, lean_object* v_a_2009_){
_start:
{
lean_object* v___x_2010_; uint8_t v___x_2011_; 
v___x_2010_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2007_);
v___x_2011_ = l_Lean_Syntax_isOfKind(v_x_2007_, v___x_2010_);
if (v___x_2011_ == 0)
{
lean_object* v___x_2012_; lean_object* v___x_2013_; 
lean_dec(v_x_2007_);
v___x_2012_ = lean_box(0);
v___x_2013_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
lean_ctor_set(v___x_2013_, 1, v_a_2009_);
return v___x_2013_;
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; uint8_t v___x_2016_; 
v___x_2014_ = lean_unsigned_to_nat(1u);
v___x_2015_ = l_Lean_Syntax_getArg(v_x_2007_, v___x_2014_);
lean_dec(v_x_2007_);
lean_inc(v___x_2015_);
v___x_2016_ = l_Lean_Syntax_matchesNull(v___x_2015_, v___x_2014_);
if (v___x_2016_ == 0)
{
lean_object* v___x_2017_; lean_object* v___x_2018_; 
lean_dec(v___x_2015_);
v___x_2017_ = lean_box(0);
v___x_2018_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2018_, 0, v___x_2017_);
lean_ctor_set(v___x_2018_, 1, v_a_2009_);
return v___x_2018_;
}
else
{
lean_object* v___x_2019_; lean_object* v_P_2020_; lean_object* v___x_2021_; 
v___x_2019_ = lean_unsigned_to_nat(0u);
v_P_2020_ = l_Lean_Syntax_getArg(v___x_2015_, v___x_2019_);
lean_dec(v___x_2015_);
v___x_2021_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2020_, v_a_2008_, v_a_2009_);
if (lean_obj_tag(v___x_2021_) == 0)
{
lean_object* v_a_2022_; lean_object* v_a_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2042_; 
v_a_2022_ = lean_ctor_get(v___x_2021_, 0);
v_a_2023_ = lean_ctor_get(v___x_2021_, 1);
v_isSharedCheck_2042_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2042_ == 0)
{
v___x_2025_ = v___x_2021_;
v_isShared_2026_ = v_isSharedCheck_2042_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_a_2023_);
lean_inc(v_a_2022_);
lean_dec(v___x_2021_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2042_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
uint8_t v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; lean_object* v___x_2040_; 
v___x_2027_ = 0;
v___x_2028_ = l_Lean_SourceInfo_fromRef(v_a_2008_, v___x_2027_);
v___x_2029_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2030_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2028_, 4);
v___x_2031_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2031_, 0, v___x_2028_);
lean_ctor_set(v___x_2031_, 1, v___x_2030_);
v___x_2032_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__5));
v___x_2033_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandNot___closed__0));
v___x_2034_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2028_);
lean_ctor_set(v___x_2034_, 1, v___x_2033_);
v___x_2035_ = l_Lean_Syntax_node2(v___x_2028_, v___x_2032_, v___x_2034_, v_a_2022_);
v___x_2036_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2037_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2037_, 0, v___x_2028_);
lean_ctor_set(v___x_2037_, 1, v___x_2036_);
v___x_2038_ = l_Lean_Syntax_node3(v___x_2028_, v___x_2029_, v___x_2031_, v___x_2035_, v___x_2037_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2038_);
v___x_2040_ = v___x_2025_;
goto v_reusejp_2039_;
}
else
{
lean_object* v_reuseFailAlloc_2041_; 
v_reuseFailAlloc_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2041_, 0, v___x_2038_);
lean_ctor_set(v_reuseFailAlloc_2041_, 1, v_a_2023_);
v___x_2040_ = v_reuseFailAlloc_2041_;
goto v_reusejp_2039_;
}
v_reusejp_2039_:
{
return v___x_2040_;
}
}
}
else
{
lean_object* v_a_2043_; lean_object* v_a_2044_; lean_object* v___x_2046_; uint8_t v_isShared_2047_; uint8_t v_isSharedCheck_2051_; 
v_a_2043_ = lean_ctor_get(v___x_2021_, 0);
v_a_2044_ = lean_ctor_get(v___x_2021_, 1);
v_isSharedCheck_2051_ = !lean_is_exclusive(v___x_2021_);
if (v_isSharedCheck_2051_ == 0)
{
v___x_2046_ = v___x_2021_;
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
else
{
lean_inc(v_a_2044_);
lean_inc(v_a_2043_);
lean_dec(v___x_2021_);
v___x_2046_ = lean_box(0);
v_isShared_2047_ = v_isSharedCheck_2051_;
goto v_resetjp_2045_;
}
v_resetjp_2045_:
{
lean_object* v___x_2049_; 
if (v_isShared_2047_ == 0)
{
v___x_2049_ = v___x_2046_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v_a_2043_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_a_2044_);
v___x_2049_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
return v___x_2049_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandNot___boxed(lean_object* v_x_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l_Std_Do_SPred_Notation_unexpandNot(v_x_2052_, v_a_2053_, v_a_2054_);
lean_dec(v_a_2053_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandImp(lean_object* v_x_2057_, lean_object* v_a_2058_, lean_object* v_a_2059_){
_start:
{
lean_object* v___x_2060_; uint8_t v___x_2061_; 
v___x_2060_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2057_);
v___x_2061_ = l_Lean_Syntax_isOfKind(v_x_2057_, v___x_2060_);
if (v___x_2061_ == 0)
{
lean_object* v___x_2062_; lean_object* v___x_2063_; 
lean_dec(v_x_2057_);
v___x_2062_ = lean_box(0);
v___x_2063_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2063_, 0, v___x_2062_);
lean_ctor_set(v___x_2063_, 1, v_a_2059_);
return v___x_2063_;
}
else
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; uint8_t v___x_2067_; 
v___x_2064_ = lean_unsigned_to_nat(1u);
v___x_2065_ = l_Lean_Syntax_getArg(v_x_2057_, v___x_2064_);
lean_dec(v_x_2057_);
v___x_2066_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2065_);
v___x_2067_ = l_Lean_Syntax_matchesNull(v___x_2065_, v___x_2066_);
if (v___x_2067_ == 0)
{
lean_object* v___x_2068_; lean_object* v___x_2069_; 
lean_dec(v___x_2065_);
v___x_2068_ = lean_box(0);
v___x_2069_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2069_, 0, v___x_2068_);
lean_ctor_set(v___x_2069_, 1, v_a_2059_);
return v___x_2069_;
}
else
{
lean_object* v___x_2070_; lean_object* v_P_2071_; lean_object* v___x_2072_; 
v___x_2070_ = lean_unsigned_to_nat(0u);
v_P_2071_ = l_Lean_Syntax_getArg(v___x_2065_, v___x_2070_);
v___x_2072_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2071_, v_a_2058_, v_a_2059_);
if (lean_obj_tag(v___x_2072_) == 0)
{
lean_object* v_a_2073_; lean_object* v_a_2074_; lean_object* v_Q_2075_; lean_object* v___x_2076_; 
v_a_2073_ = lean_ctor_get(v___x_2072_, 0);
lean_inc(v_a_2073_);
v_a_2074_ = lean_ctor_get(v___x_2072_, 1);
lean_inc(v_a_2074_);
lean_dec_ref_known(v___x_2072_, 2);
v_Q_2075_ = l_Lean_Syntax_getArg(v___x_2065_, v___x_2064_);
lean_dec(v___x_2065_);
v___x_2076_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_2075_, v_a_2058_, v_a_2074_);
if (lean_obj_tag(v___x_2076_) == 0)
{
lean_object* v_a_2077_; lean_object* v_a_2078_; lean_object* v___x_2080_; uint8_t v_isShared_2081_; uint8_t v_isSharedCheck_2097_; 
v_a_2077_ = lean_ctor_get(v___x_2076_, 0);
v_a_2078_ = lean_ctor_get(v___x_2076_, 1);
v_isSharedCheck_2097_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2097_ == 0)
{
v___x_2080_ = v___x_2076_;
v_isShared_2081_ = v_isSharedCheck_2097_;
goto v_resetjp_2079_;
}
else
{
lean_inc(v_a_2078_);
lean_inc(v_a_2077_);
lean_dec(v___x_2076_);
v___x_2080_ = lean_box(0);
v_isShared_2081_ = v_isSharedCheck_2097_;
goto v_resetjp_2079_;
}
v_resetjp_2079_:
{
uint8_t v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2095_; 
v___x_2082_ = 0;
v___x_2083_ = l_Lean_SourceInfo_fromRef(v_a_2058_, v___x_2082_);
v___x_2084_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2085_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2083_, 4);
v___x_2086_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2086_, 0, v___x_2083_);
lean_ctor_set(v___x_2086_, 1, v___x_2085_);
v___x_2087_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__7));
v___x_2088_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandImp___closed__0));
v___x_2089_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2089_, 0, v___x_2083_);
lean_ctor_set(v___x_2089_, 1, v___x_2088_);
v___x_2090_ = l_Lean_Syntax_node3(v___x_2083_, v___x_2087_, v_a_2073_, v___x_2089_, v_a_2077_);
v___x_2091_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2092_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2092_, 0, v___x_2083_);
lean_ctor_set(v___x_2092_, 1, v___x_2091_);
v___x_2093_ = l_Lean_Syntax_node3(v___x_2083_, v___x_2084_, v___x_2086_, v___x_2090_, v___x_2092_);
if (v_isShared_2081_ == 0)
{
lean_ctor_set(v___x_2080_, 0, v___x_2093_);
v___x_2095_ = v___x_2080_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2096_; 
v_reuseFailAlloc_2096_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2096_, 0, v___x_2093_);
lean_ctor_set(v_reuseFailAlloc_2096_, 1, v_a_2078_);
v___x_2095_ = v_reuseFailAlloc_2096_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
return v___x_2095_;
}
}
}
else
{
lean_object* v_a_2098_; lean_object* v_a_2099_; lean_object* v___x_2101_; uint8_t v_isShared_2102_; uint8_t v_isSharedCheck_2106_; 
lean_dec(v_a_2073_);
v_a_2098_ = lean_ctor_get(v___x_2076_, 0);
v_a_2099_ = lean_ctor_get(v___x_2076_, 1);
v_isSharedCheck_2106_ = !lean_is_exclusive(v___x_2076_);
if (v_isSharedCheck_2106_ == 0)
{
v___x_2101_ = v___x_2076_;
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
else
{
lean_inc(v_a_2099_);
lean_inc(v_a_2098_);
lean_dec(v___x_2076_);
v___x_2101_ = lean_box(0);
v_isShared_2102_ = v_isSharedCheck_2106_;
goto v_resetjp_2100_;
}
v_resetjp_2100_:
{
lean_object* v___x_2104_; 
if (v_isShared_2102_ == 0)
{
v___x_2104_ = v___x_2101_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2105_; 
v_reuseFailAlloc_2105_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2105_, 0, v_a_2098_);
lean_ctor_set(v_reuseFailAlloc_2105_, 1, v_a_2099_);
v___x_2104_ = v_reuseFailAlloc_2105_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
return v___x_2104_;
}
}
}
}
else
{
lean_object* v_a_2107_; lean_object* v_a_2108_; lean_object* v___x_2110_; uint8_t v_isShared_2111_; uint8_t v_isSharedCheck_2115_; 
lean_dec(v___x_2065_);
v_a_2107_ = lean_ctor_get(v___x_2072_, 0);
v_a_2108_ = lean_ctor_get(v___x_2072_, 1);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2072_);
if (v_isSharedCheck_2115_ == 0)
{
v___x_2110_ = v___x_2072_;
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
else
{
lean_inc(v_a_2108_);
lean_inc(v_a_2107_);
lean_dec(v___x_2072_);
v___x_2110_ = lean_box(0);
v_isShared_2111_ = v_isSharedCheck_2115_;
goto v_resetjp_2109_;
}
v_resetjp_2109_:
{
lean_object* v___x_2113_; 
if (v_isShared_2111_ == 0)
{
v___x_2113_ = v___x_2110_;
goto v_reusejp_2112_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_a_2107_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v_a_2108_);
v___x_2113_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2112_;
}
v_reusejp_2112_:
{
return v___x_2113_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandImp___boxed(lean_object* v_x_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_){
_start:
{
lean_object* v_res_2119_; 
v_res_2119_ = l_Std_Do_SPred_Notation_unexpandImp(v_x_2116_, v_a_2117_, v_a_2118_);
lean_dec(v_a_2117_);
return v_res_2119_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__1(size_t v_sz_2120_, size_t v_i_2121_, lean_object* v_bs_2122_){
_start:
{
uint8_t v___x_2123_; 
v___x_2123_ = lean_usize_dec_lt(v_i_2121_, v_sz_2120_);
if (v___x_2123_ == 0)
{
return v_bs_2122_;
}
else
{
lean_object* v_v_2124_; lean_object* v___x_2125_; lean_object* v_bs_x27_2126_; size_t v___x_2127_; size_t v___x_2128_; lean_object* v___x_2129_; 
v_v_2124_ = lean_array_uget(v_bs_2122_, v_i_2121_);
v___x_2125_ = lean_unsigned_to_nat(0u);
v_bs_x27_2126_ = lean_array_uset(v_bs_2122_, v_i_2121_, v___x_2125_);
v___x_2127_ = ((size_t)1ULL);
v___x_2128_ = lean_usize_add(v_i_2121_, v___x_2127_);
v___x_2129_ = lean_array_uset(v_bs_x27_2126_, v_i_2121_, v_v_2124_);
v_i_2121_ = v___x_2128_;
v_bs_2122_ = v___x_2129_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__1___boxed(lean_object* v_sz_2131_, lean_object* v_i_2132_, lean_object* v_bs_2133_){
_start:
{
size_t v_sz_boxed_2134_; size_t v_i_boxed_2135_; lean_object* v_res_2136_; 
v_sz_boxed_2134_ = lean_unbox_usize(v_sz_2131_);
lean_dec(v_sz_2131_);
v_i_boxed_2135_ = lean_unbox_usize(v_i_2132_);
lean_dec(v_i_2132_);
v_res_2136_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__1(v_sz_boxed_2134_, v_i_boxed_2135_, v_bs_2133_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__0(size_t v_sz_2137_, size_t v_i_2138_, lean_object* v_bs_2139_){
_start:
{
uint8_t v___x_2140_; 
v___x_2140_ = lean_usize_dec_lt(v_i_2138_, v_sz_2137_);
if (v___x_2140_ == 0)
{
lean_object* v___x_2141_; 
v___x_2141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2141_, 0, v_bs_2139_);
return v___x_2141_;
}
else
{
lean_object* v_v_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; 
v_v_2142_ = lean_array_uget(v_bs_2139_, v_i_2138_);
v___x_2143_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_v_2142_);
v___x_2144_ = l_Lean_Syntax_isOfKind(v_v_2142_, v___x_2143_);
if (v___x_2144_ == 0)
{
lean_object* v___x_2145_; 
lean_dec(v_v_2142_);
lean_dec_ref(v_bs_2139_);
v___x_2145_ = lean_box(0);
return v___x_2145_;
}
else
{
lean_object* v___x_2146_; lean_object* v_bs_x27_2147_; size_t v___x_2148_; size_t v___x_2149_; lean_object* v___x_2150_; 
v___x_2146_ = lean_unsigned_to_nat(0u);
v_bs_x27_2147_ = lean_array_uset(v_bs_2139_, v_i_2138_, v___x_2146_);
v___x_2148_ = ((size_t)1ULL);
v___x_2149_ = lean_usize_add(v_i_2138_, v___x_2148_);
v___x_2150_ = lean_array_uset(v_bs_x27_2147_, v_i_2138_, v_v_2142_);
v_i_2138_ = v___x_2149_;
v_bs_2139_ = v___x_2150_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__0___boxed(lean_object* v_sz_2152_, lean_object* v_i_2153_, lean_object* v_bs_2154_){
_start:
{
size_t v_sz_boxed_2155_; size_t v_i_boxed_2156_; lean_object* v_res_2157_; 
v_sz_boxed_2155_ = lean_unbox_usize(v_sz_2152_);
lean_dec(v_sz_2152_);
v_i_boxed_2156_ = lean_unbox_usize(v_i_2153_);
lean_dec(v_i_2153_);
v_res_2157_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__0(v_sz_boxed_2155_, v_i_boxed_2156_, v_bs_2154_);
return v_res_2157_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandForall(lean_object* v_x_2158_, lean_object* v_a_2159_, lean_object* v_a_2160_){
_start:
{
lean_object* v___x_2161_; uint8_t v___x_2162_; 
v___x_2161_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2158_);
v___x_2162_ = l_Lean_Syntax_isOfKind(v_x_2158_, v___x_2161_);
if (v___x_2162_ == 0)
{
lean_object* v___x_2163_; lean_object* v___x_2164_; 
lean_dec(v_x_2158_);
v___x_2163_ = lean_box(0);
v___x_2164_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2164_, 0, v___x_2163_);
lean_ctor_set(v___x_2164_, 1, v_a_2160_);
return v___x_2164_;
}
else
{
lean_object* v___x_2165_; lean_object* v___x_2166_; uint8_t v___x_2167_; 
v___x_2165_ = lean_unsigned_to_nat(1u);
v___x_2166_ = l_Lean_Syntax_getArg(v_x_2158_, v___x_2165_);
lean_dec(v_x_2158_);
lean_inc(v___x_2166_);
v___x_2167_ = l_Lean_Syntax_matchesNull(v___x_2166_, v___x_2165_);
if (v___x_2167_ == 0)
{
lean_object* v___x_2168_; lean_object* v___x_2169_; 
lean_dec(v___x_2166_);
v___x_2168_ = lean_box(0);
v___x_2169_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2169_, 0, v___x_2168_);
lean_ctor_set(v___x_2169_, 1, v_a_2160_);
return v___x_2169_;
}
else
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; uint8_t v___x_2173_; 
v___x_2170_ = lean_unsigned_to_nat(0u);
v___x_2171_ = l_Lean_Syntax_getArg(v___x_2166_, v___x_2170_);
lean_dec(v___x_2166_);
v___x_2172_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
lean_inc(v___x_2171_);
v___x_2173_ = l_Lean_Syntax_isOfKind(v___x_2171_, v___x_2172_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; lean_object* v___x_2175_; 
lean_dec(v___x_2171_);
v___x_2174_ = lean_box(0);
v___x_2175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2175_, 0, v___x_2174_);
lean_ctor_set(v___x_2175_, 1, v_a_2160_);
return v___x_2175_;
}
else
{
lean_object* v___x_2176_; lean_object* v___x_2177_; uint8_t v___x_2178_; 
v___x_2176_ = l_Lean_Syntax_getArg(v___x_2171_, v___x_2165_);
lean_dec(v___x_2171_);
v___x_2177_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
lean_inc(v___x_2176_);
v___x_2178_ = l_Lean_Syntax_isOfKind(v___x_2176_, v___x_2177_);
if (v___x_2178_ == 0)
{
lean_object* v___x_2179_; lean_object* v___x_2180_; 
lean_dec(v___x_2176_);
v___x_2179_ = lean_box(0);
v___x_2180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2180_, 0, v___x_2179_);
lean_ctor_set(v___x_2180_, 1, v_a_2160_);
return v___x_2180_;
}
else
{
lean_object* v___x_2181_; uint8_t v___x_2182_; 
v___x_2181_ = l_Lean_Syntax_getArg(v___x_2176_, v___x_2170_);
lean_inc(v___x_2181_);
v___x_2182_ = l_Lean_Syntax_matchesNull(v___x_2181_, v___x_2165_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; lean_object* v___x_2184_; 
lean_dec(v___x_2181_);
lean_dec(v___x_2176_);
v___x_2183_ = lean_box(0);
v___x_2184_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2184_, 0, v___x_2183_);
lean_ctor_set(v___x_2184_, 1, v_a_2160_);
return v___x_2184_;
}
else
{
lean_object* v___x_2185_; lean_object* v___x_2186_; uint8_t v___x_2187_; 
v___x_2185_ = l_Lean_Syntax_getArg(v___x_2181_, v___x_2170_);
lean_dec(v___x_2181_);
v___x_2186_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v___x_2185_);
v___x_2187_ = l_Lean_Syntax_isOfKind(v___x_2185_, v___x_2186_);
if (v___x_2187_ == 0)
{
lean_object* v___x_2188_; lean_object* v___x_2189_; 
lean_dec(v___x_2185_);
lean_dec(v___x_2176_);
v___x_2188_ = lean_box(0);
v___x_2189_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2189_, 0, v___x_2188_);
lean_ctor_set(v___x_2189_, 1, v_a_2160_);
return v___x_2189_;
}
else
{
lean_object* v___x_2190_; uint8_t v___x_2191_; 
v___x_2190_ = l_Lean_Syntax_getArg(v___x_2176_, v___x_2165_);
v___x_2191_ = l_Lean_Syntax_matchesNull(v___x_2190_, v___x_2170_);
if (v___x_2191_ == 0)
{
lean_object* v___x_2192_; lean_object* v___x_2193_; 
lean_dec(v___x_2185_);
lean_dec(v___x_2176_);
v___x_2192_ = lean_box(0);
v___x_2193_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2193_, 0, v___x_2192_);
lean_ctor_set(v___x_2193_, 1, v_a_2160_);
return v___x_2193_;
}
else
{
lean_object* v___x_2194_; lean_object* v_00_u03a8_2195_; lean_object* v___x_2196_; uint8_t v___x_2197_; 
v___x_2194_ = lean_unsigned_to_nat(3u);
v_00_u03a8_2195_ = l_Lean_Syntax_getArg(v___x_2176_, v___x_2194_);
lean_dec(v___x_2176_);
v___x_2196_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__13));
lean_inc(v_00_u03a8_2195_);
v___x_2197_ = l_Lean_Syntax_isOfKind(v_00_u03a8_2195_, v___x_2196_);
if (v___x_2197_ == 0)
{
lean_object* v___x_2198_; 
v___x_2198_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2195_, v_a_2159_, v_a_2160_);
if (lean_obj_tag(v___x_2198_) == 0)
{
lean_object* v_a_2199_; lean_object* v_a_2200_; lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2223_; 
v_a_2199_ = lean_ctor_get(v___x_2198_, 0);
v_a_2200_ = lean_ctor_get(v___x_2198_, 1);
v_isSharedCheck_2223_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2223_ == 0)
{
v___x_2202_ = v___x_2198_;
v_isShared_2203_ = v_isSharedCheck_2223_;
goto v_resetjp_2201_;
}
else
{
lean_inc(v_a_2200_);
lean_inc(v_a_2199_);
lean_dec(v___x_2198_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2223_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2221_; 
v___x_2204_ = l_Lean_SourceInfo_fromRef(v_a_2159_, v___x_2197_);
v___x_2205_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2206_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2204_, 7);
v___x_2207_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2204_);
lean_ctor_set(v___x_2207_, 1, v___x_2206_);
v___x_2208_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_2209_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2204_);
lean_ctor_set(v___x_2209_, 1, v___x_2208_);
v___x_2210_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2211_ = l_Lean_Syntax_node1(v___x_2204_, v___x_2210_, v___x_2185_);
v___x_2212_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2213_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2213_, 0, v___x_2204_);
lean_ctor_set(v___x_2213_, 1, v___x_2210_);
lean_ctor_set(v___x_2213_, 2, v___x_2212_);
v___x_2214_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_2215_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2204_);
lean_ctor_set(v___x_2215_, 1, v___x_2214_);
v___x_2216_ = l_Lean_Syntax_node5(v___x_2204_, v___x_2196_, v___x_2209_, v___x_2211_, v___x_2213_, v___x_2215_, v_a_2199_);
v___x_2217_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2218_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2218_, 0, v___x_2204_);
lean_ctor_set(v___x_2218_, 1, v___x_2217_);
v___x_2219_ = l_Lean_Syntax_node3(v___x_2204_, v___x_2205_, v___x_2207_, v___x_2216_, v___x_2218_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 0, v___x_2219_);
v___x_2221_ = v___x_2202_;
goto v_reusejp_2220_;
}
else
{
lean_object* v_reuseFailAlloc_2222_; 
v_reuseFailAlloc_2222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2222_, 0, v___x_2219_);
lean_ctor_set(v_reuseFailAlloc_2222_, 1, v_a_2200_);
v___x_2221_ = v_reuseFailAlloc_2222_;
goto v_reusejp_2220_;
}
v_reusejp_2220_:
{
return v___x_2221_;
}
}
}
else
{
lean_object* v_a_2224_; lean_object* v_a_2225_; lean_object* v___x_2227_; uint8_t v_isShared_2228_; uint8_t v_isSharedCheck_2232_; 
lean_dec(v___x_2185_);
v_a_2224_ = lean_ctor_get(v___x_2198_, 0);
v_a_2225_ = lean_ctor_get(v___x_2198_, 1);
v_isSharedCheck_2232_ = !lean_is_exclusive(v___x_2198_);
if (v_isSharedCheck_2232_ == 0)
{
v___x_2227_ = v___x_2198_;
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
else
{
lean_inc(v_a_2225_);
lean_inc(v_a_2224_);
lean_dec(v___x_2198_);
v___x_2227_ = lean_box(0);
v_isShared_2228_ = v_isSharedCheck_2232_;
goto v_resetjp_2226_;
}
v_resetjp_2226_:
{
lean_object* v___x_2230_; 
if (v_isShared_2228_ == 0)
{
v___x_2230_ = v___x_2227_;
goto v_reusejp_2229_;
}
else
{
lean_object* v_reuseFailAlloc_2231_; 
v_reuseFailAlloc_2231_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2231_, 0, v_a_2224_);
lean_ctor_set(v_reuseFailAlloc_2231_, 1, v_a_2225_);
v___x_2230_ = v_reuseFailAlloc_2231_;
goto v_reusejp_2229_;
}
v_reusejp_2229_:
{
return v___x_2230_;
}
}
}
}
else
{
lean_object* v___x_2233_; lean_object* v___x_2234_; uint8_t v___x_2235_; 
v___x_2233_ = l_Lean_Syntax_getArg(v_00_u03a8_2195_, v___x_2165_);
v___x_2234_ = l_Lean_Syntax_getNumArgs(v___x_2233_);
v___x_2235_ = lean_nat_dec_le(v___x_2165_, v___x_2234_);
if (v___x_2235_ == 0)
{
lean_object* v___x_2236_; 
lean_dec(v___x_2234_);
lean_dec(v___x_2233_);
v___x_2236_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2195_, v_a_2159_, v_a_2160_);
if (lean_obj_tag(v___x_2236_) == 0)
{
lean_object* v_a_2237_; lean_object* v_a_2238_; lean_object* v___x_2240_; uint8_t v_isShared_2241_; uint8_t v_isSharedCheck_2261_; 
v_a_2237_ = lean_ctor_get(v___x_2236_, 0);
v_a_2238_ = lean_ctor_get(v___x_2236_, 1);
v_isSharedCheck_2261_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2261_ == 0)
{
v___x_2240_ = v___x_2236_;
v_isShared_2241_ = v_isSharedCheck_2261_;
goto v_resetjp_2239_;
}
else
{
lean_inc(v_a_2238_);
lean_inc(v_a_2237_);
lean_dec(v___x_2236_);
v___x_2240_ = lean_box(0);
v_isShared_2241_ = v_isSharedCheck_2261_;
goto v_resetjp_2239_;
}
v_resetjp_2239_:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2259_; 
v___x_2242_ = l_Lean_SourceInfo_fromRef(v_a_2159_, v___x_2235_);
v___x_2243_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2244_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2242_, 7);
v___x_2245_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2242_);
lean_ctor_set(v___x_2245_, 1, v___x_2244_);
v___x_2246_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_2247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2247_, 0, v___x_2242_);
lean_ctor_set(v___x_2247_, 1, v___x_2246_);
v___x_2248_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2249_ = l_Lean_Syntax_node1(v___x_2242_, v___x_2248_, v___x_2185_);
v___x_2250_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2251_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2242_);
lean_ctor_set(v___x_2251_, 1, v___x_2248_);
lean_ctor_set(v___x_2251_, 2, v___x_2250_);
v___x_2252_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_2253_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2253_, 0, v___x_2242_);
lean_ctor_set(v___x_2253_, 1, v___x_2252_);
v___x_2254_ = l_Lean_Syntax_node5(v___x_2242_, v___x_2196_, v___x_2247_, v___x_2249_, v___x_2251_, v___x_2253_, v_a_2237_);
v___x_2255_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2256_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2256_, 0, v___x_2242_);
lean_ctor_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = l_Lean_Syntax_node3(v___x_2242_, v___x_2243_, v___x_2245_, v___x_2254_, v___x_2256_);
if (v_isShared_2241_ == 0)
{
lean_ctor_set(v___x_2240_, 0, v___x_2257_);
v___x_2259_ = v___x_2240_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2257_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_a_2238_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
}
else
{
lean_object* v_a_2262_; lean_object* v_a_2263_; lean_object* v___x_2265_; uint8_t v_isShared_2266_; uint8_t v_isSharedCheck_2270_; 
lean_dec(v___x_2185_);
v_a_2262_ = lean_ctor_get(v___x_2236_, 0);
v_a_2263_ = lean_ctor_get(v___x_2236_, 1);
v_isSharedCheck_2270_ = !lean_is_exclusive(v___x_2236_);
if (v_isSharedCheck_2270_ == 0)
{
v___x_2265_ = v___x_2236_;
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
else
{
lean_inc(v_a_2263_);
lean_inc(v_a_2262_);
lean_dec(v___x_2236_);
v___x_2265_ = lean_box(0);
v_isShared_2266_ = v_isSharedCheck_2270_;
goto v_resetjp_2264_;
}
v_resetjp_2264_:
{
lean_object* v___x_2268_; 
if (v_isShared_2266_ == 0)
{
v___x_2268_ = v___x_2265_;
goto v_reusejp_2267_;
}
else
{
lean_object* v_reuseFailAlloc_2269_; 
v_reuseFailAlloc_2269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2269_, 0, v_a_2262_);
lean_ctor_set(v_reuseFailAlloc_2269_, 1, v_a_2263_);
v___x_2268_ = v_reuseFailAlloc_2269_;
goto v_reusejp_2267_;
}
v_reusejp_2267_:
{
return v___x_2268_;
}
}
}
}
else
{
lean_object* v___x_2271_; uint8_t v___x_2272_; 
v___x_2271_ = l_Lean_Syntax_getArg(v___x_2233_, v___x_2170_);
lean_inc(v___x_2271_);
v___x_2272_ = l_Lean_Syntax_isOfKind(v___x_2271_, v___x_2186_);
if (v___x_2272_ == 0)
{
lean_object* v___x_2273_; 
lean_dec(v___x_2271_);
lean_dec(v___x_2234_);
lean_dec(v___x_2233_);
v___x_2273_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2195_, v_a_2159_, v_a_2160_);
if (lean_obj_tag(v___x_2273_) == 0)
{
lean_object* v_a_2274_; lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2298_; 
v_a_2274_ = lean_ctor_get(v___x_2273_, 0);
v_a_2275_ = lean_ctor_get(v___x_2273_, 1);
v_isSharedCheck_2298_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2298_ == 0)
{
v___x_2277_ = v___x_2273_;
v_isShared_2278_ = v_isSharedCheck_2298_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_inc(v_a_2274_);
lean_dec(v___x_2273_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2298_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2296_; 
v___x_2279_ = l_Lean_SourceInfo_fromRef(v_a_2159_, v___x_2272_);
v___x_2280_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2281_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2279_, 7);
v___x_2282_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2282_, 0, v___x_2279_);
lean_ctor_set(v___x_2282_, 1, v___x_2281_);
v___x_2283_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_2284_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2284_, 0, v___x_2279_);
lean_ctor_set(v___x_2284_, 1, v___x_2283_);
v___x_2285_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2286_ = l_Lean_Syntax_node1(v___x_2279_, v___x_2285_, v___x_2185_);
v___x_2287_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2288_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2288_, 0, v___x_2279_);
lean_ctor_set(v___x_2288_, 1, v___x_2285_);
lean_ctor_set(v___x_2288_, 2, v___x_2287_);
v___x_2289_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_2290_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2290_, 0, v___x_2279_);
lean_ctor_set(v___x_2290_, 1, v___x_2289_);
v___x_2291_ = l_Lean_Syntax_node5(v___x_2279_, v___x_2196_, v___x_2284_, v___x_2286_, v___x_2288_, v___x_2290_, v_a_2274_);
v___x_2292_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2293_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2293_, 0, v___x_2279_);
lean_ctor_set(v___x_2293_, 1, v___x_2292_);
v___x_2294_ = l_Lean_Syntax_node3(v___x_2279_, v___x_2280_, v___x_2282_, v___x_2291_, v___x_2293_);
if (v_isShared_2278_ == 0)
{
lean_ctor_set(v___x_2277_, 0, v___x_2294_);
v___x_2296_ = v___x_2277_;
goto v_reusejp_2295_;
}
else
{
lean_object* v_reuseFailAlloc_2297_; 
v_reuseFailAlloc_2297_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2297_, 0, v___x_2294_);
lean_ctor_set(v_reuseFailAlloc_2297_, 1, v_a_2275_);
v___x_2296_ = v_reuseFailAlloc_2297_;
goto v_reusejp_2295_;
}
v_reusejp_2295_:
{
return v___x_2296_;
}
}
}
else
{
lean_object* v_a_2299_; lean_object* v_a_2300_; lean_object* v___x_2302_; uint8_t v_isShared_2303_; uint8_t v_isSharedCheck_2307_; 
lean_dec(v___x_2185_);
v_a_2299_ = lean_ctor_get(v___x_2273_, 0);
v_a_2300_ = lean_ctor_get(v___x_2273_, 1);
v_isSharedCheck_2307_ = !lean_is_exclusive(v___x_2273_);
if (v_isSharedCheck_2307_ == 0)
{
v___x_2302_ = v___x_2273_;
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
else
{
lean_inc(v_a_2300_);
lean_inc(v_a_2299_);
lean_dec(v___x_2273_);
v___x_2302_ = lean_box(0);
v_isShared_2303_ = v_isSharedCheck_2307_;
goto v_resetjp_2301_;
}
v_resetjp_2301_:
{
lean_object* v___x_2305_; 
if (v_isShared_2303_ == 0)
{
v___x_2305_ = v___x_2302_;
goto v_reusejp_2304_;
}
else
{
lean_object* v_reuseFailAlloc_2306_; 
v_reuseFailAlloc_2306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2306_, 0, v_a_2299_);
lean_ctor_set(v_reuseFailAlloc_2306_, 1, v_a_2300_);
v___x_2305_ = v_reuseFailAlloc_2306_;
goto v_reusejp_2304_;
}
v_reusejp_2304_:
{
return v___x_2305_;
}
}
}
}
else
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; size_t v_sz_2314_; size_t v___x_2315_; lean_object* v___x_2316_; 
v___x_2308_ = l_Lean_Syntax_getArgs(v___x_2233_);
lean_dec(v___x_2233_);
v___x_2309_ = l_Array_extract___redArg(v___x_2308_, v___x_2165_, v___x_2234_);
lean_dec_ref(v___x_2308_);
v___x_2310_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2311_ = lean_box(2);
v___x_2312_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2312_, 0, v___x_2311_);
lean_ctor_set(v___x_2312_, 1, v___x_2310_);
lean_ctor_set(v___x_2312_, 2, v___x_2309_);
v___x_2313_ = l_Lean_Syntax_getArgs(v___x_2312_);
lean_dec_ref_known(v___x_2312_, 3);
v_sz_2314_ = lean_array_size(v___x_2313_);
v___x_2315_ = ((size_t)0ULL);
v___x_2316_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__0(v_sz_2314_, v___x_2315_, v___x_2313_);
if (lean_obj_tag(v___x_2316_) == 0)
{
lean_object* v___x_2317_; 
lean_dec(v___x_2271_);
v___x_2317_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2195_, v_a_2159_, v_a_2160_);
if (lean_obj_tag(v___x_2317_) == 0)
{
lean_object* v_a_2318_; lean_object* v_a_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2342_; 
v_a_2318_ = lean_ctor_get(v___x_2317_, 0);
v_a_2319_ = lean_ctor_get(v___x_2317_, 1);
v_isSharedCheck_2342_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2342_ == 0)
{
v___x_2321_ = v___x_2317_;
v_isShared_2322_ = v_isSharedCheck_2342_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_a_2319_);
lean_inc(v_a_2318_);
lean_dec(v___x_2317_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2342_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
uint8_t v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2340_; 
v___x_2323_ = 0;
v___x_2324_ = l_Lean_SourceInfo_fromRef(v_a_2159_, v___x_2323_);
v___x_2325_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2326_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2324_, 7);
v___x_2327_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2327_, 0, v___x_2324_);
lean_ctor_set(v___x_2327_, 1, v___x_2326_);
v___x_2328_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_2329_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2324_);
lean_ctor_set(v___x_2329_, 1, v___x_2328_);
v___x_2330_ = l_Lean_Syntax_node1(v___x_2324_, v___x_2310_, v___x_2185_);
v___x_2331_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2332_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2324_);
lean_ctor_set(v___x_2332_, 1, v___x_2310_);
lean_ctor_set(v___x_2332_, 2, v___x_2331_);
v___x_2333_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_2334_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2324_);
lean_ctor_set(v___x_2334_, 1, v___x_2333_);
v___x_2335_ = l_Lean_Syntax_node5(v___x_2324_, v___x_2196_, v___x_2329_, v___x_2330_, v___x_2332_, v___x_2334_, v_a_2318_);
v___x_2336_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2337_, 0, v___x_2324_);
lean_ctor_set(v___x_2337_, 1, v___x_2336_);
v___x_2338_ = l_Lean_Syntax_node3(v___x_2324_, v___x_2325_, v___x_2327_, v___x_2335_, v___x_2337_);
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2338_);
v___x_2340_ = v___x_2321_;
goto v_reusejp_2339_;
}
else
{
lean_object* v_reuseFailAlloc_2341_; 
v_reuseFailAlloc_2341_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2341_, 0, v___x_2338_);
lean_ctor_set(v_reuseFailAlloc_2341_, 1, v_a_2319_);
v___x_2340_ = v_reuseFailAlloc_2341_;
goto v_reusejp_2339_;
}
v_reusejp_2339_:
{
return v___x_2340_;
}
}
}
else
{
lean_object* v_a_2343_; lean_object* v_a_2344_; lean_object* v___x_2346_; uint8_t v_isShared_2347_; uint8_t v_isSharedCheck_2351_; 
lean_dec(v___x_2185_);
v_a_2343_ = lean_ctor_get(v___x_2317_, 0);
v_a_2344_ = lean_ctor_get(v___x_2317_, 1);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2317_);
if (v_isSharedCheck_2351_ == 0)
{
v___x_2346_ = v___x_2317_;
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
else
{
lean_inc(v_a_2344_);
lean_inc(v_a_2343_);
lean_dec(v___x_2317_);
v___x_2346_ = lean_box(0);
v_isShared_2347_ = v_isSharedCheck_2351_;
goto v_resetjp_2345_;
}
v_resetjp_2345_:
{
lean_object* v___x_2349_; 
if (v_isShared_2347_ == 0)
{
v___x_2349_ = v___x_2346_;
goto v_reusejp_2348_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_a_2343_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v_a_2344_);
v___x_2349_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2348_;
}
v_reusejp_2348_:
{
return v___x_2349_;
}
}
}
}
else
{
lean_object* v_val_2352_; lean_object* v___x_2353_; lean_object* v___x_2354_; uint8_t v___x_2355_; 
v_val_2352_ = lean_ctor_get(v___x_2316_, 0);
lean_inc(v_val_2352_);
lean_dec_ref_known(v___x_2316_, 1);
v___x_2353_ = lean_unsigned_to_nat(2u);
v___x_2354_ = l_Lean_Syntax_getArg(v_00_u03a8_2195_, v___x_2353_);
v___x_2355_ = l_Lean_Syntax_matchesNull(v___x_2354_, v___x_2170_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2356_; 
lean_dec(v_val_2352_);
lean_dec(v___x_2271_);
v___x_2356_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2195_, v_a_2159_, v_a_2160_);
if (lean_obj_tag(v___x_2356_) == 0)
{
lean_object* v_a_2357_; lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2380_; 
v_a_2357_ = lean_ctor_get(v___x_2356_, 0);
v_a_2358_ = lean_ctor_get(v___x_2356_, 1);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2360_ = v___x_2356_;
v_isShared_2361_ = v_isSharedCheck_2380_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_inc(v_a_2357_);
lean_dec(v___x_2356_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2380_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; lean_object* v___x_2378_; 
v___x_2362_ = l_Lean_SourceInfo_fromRef(v_a_2159_, v___x_2355_);
v___x_2363_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2364_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2362_, 7);
v___x_2365_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2362_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
v___x_2366_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_2367_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2362_);
lean_ctor_set(v___x_2367_, 1, v___x_2366_);
v___x_2368_ = l_Lean_Syntax_node1(v___x_2362_, v___x_2310_, v___x_2185_);
v___x_2369_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2370_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2370_, 0, v___x_2362_);
lean_ctor_set(v___x_2370_, 1, v___x_2310_);
lean_ctor_set(v___x_2370_, 2, v___x_2369_);
v___x_2371_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_2372_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2372_, 0, v___x_2362_);
lean_ctor_set(v___x_2372_, 1, v___x_2371_);
v___x_2373_ = l_Lean_Syntax_node5(v___x_2362_, v___x_2196_, v___x_2367_, v___x_2368_, v___x_2370_, v___x_2372_, v_a_2357_);
v___x_2374_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2375_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2375_, 0, v___x_2362_);
lean_ctor_set(v___x_2375_, 1, v___x_2374_);
v___x_2376_ = l_Lean_Syntax_node3(v___x_2362_, v___x_2363_, v___x_2365_, v___x_2373_, v___x_2375_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 0, v___x_2376_);
v___x_2378_ = v___x_2360_;
goto v_reusejp_2377_;
}
else
{
lean_object* v_reuseFailAlloc_2379_; 
v_reuseFailAlloc_2379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2379_, 0, v___x_2376_);
lean_ctor_set(v_reuseFailAlloc_2379_, 1, v_a_2358_);
v___x_2378_ = v_reuseFailAlloc_2379_;
goto v_reusejp_2377_;
}
v_reusejp_2377_:
{
return v___x_2378_;
}
}
}
else
{
lean_object* v_a_2381_; lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_dec(v___x_2185_);
v_a_2381_ = lean_ctor_get(v___x_2356_, 0);
v_a_2382_ = lean_ctor_get(v___x_2356_, 1);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2356_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2356_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_inc(v_a_2381_);
lean_dec(v___x_2356_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2381_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
else
{
lean_object* v___x_2390_; lean_object* v_00_u03a8_2391_; lean_object* v___x_2392_; 
v___x_2390_ = lean_unsigned_to_nat(4u);
v_00_u03a8_2391_ = l_Lean_Syntax_getArg(v_00_u03a8_2195_, v___x_2390_);
lean_dec(v_00_u03a8_2195_);
v___x_2392_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2391_, v_a_2159_, v_a_2160_);
if (lean_obj_tag(v___x_2392_) == 0)
{
lean_object* v_a_2393_; lean_object* v_a_2394_; lean_object* v___x_2396_; uint8_t v_isShared_2397_; uint8_t v_isSharedCheck_2421_; 
v_a_2393_ = lean_ctor_get(v___x_2392_, 0);
v_a_2394_ = lean_ctor_get(v___x_2392_, 1);
v_isSharedCheck_2421_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2396_ = v___x_2392_;
v_isShared_2397_ = v_isSharedCheck_2421_;
goto v_resetjp_2395_;
}
else
{
lean_inc(v_a_2394_);
lean_inc(v_a_2393_);
lean_dec(v___x_2392_);
v___x_2396_ = lean_box(0);
v_isShared_2397_ = v_isSharedCheck_2421_;
goto v_resetjp_2395_;
}
v_resetjp_2395_:
{
uint8_t v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; lean_object* v___x_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; size_t v_sz_2406_; lean_object* v___x_2407_; lean_object* v___x_2408_; lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2419_; 
v___x_2398_ = 0;
v___x_2399_ = l_Lean_SourceInfo_fromRef(v_a_2159_, v___x_2398_);
v___x_2400_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2401_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2399_, 7);
v___x_2402_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2402_, 0, v___x_2399_);
lean_ctor_set(v___x_2402_, 1, v___x_2401_);
v___x_2403_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__52));
v___x_2404_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2404_, 0, v___x_2399_);
lean_ctor_set(v___x_2404_, 1, v___x_2403_);
v___x_2405_ = l_Array_mkArray2___redArg(v___x_2185_, v___x_2271_);
v_sz_2406_ = lean_array_size(v_val_2352_);
v___x_2407_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandForall_spec__1(v_sz_2406_, v___x_2315_, v_val_2352_);
v___x_2408_ = l_Array_append___redArg(v___x_2405_, v___x_2407_);
lean_dec_ref(v___x_2407_);
v___x_2409_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2409_, 0, v___x_2399_);
lean_ctor_set(v___x_2409_, 1, v___x_2310_);
lean_ctor_set(v___x_2409_, 2, v___x_2408_);
v___x_2410_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2411_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2411_, 0, v___x_2399_);
lean_ctor_set(v___x_2411_, 1, v___x_2310_);
lean_ctor_set(v___x_2411_, 2, v___x_2410_);
v___x_2412_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_2413_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2399_);
lean_ctor_set(v___x_2413_, 1, v___x_2412_);
v___x_2414_ = l_Lean_Syntax_node5(v___x_2399_, v___x_2196_, v___x_2404_, v___x_2409_, v___x_2411_, v___x_2413_, v_a_2393_);
v___x_2415_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2416_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2399_);
lean_ctor_set(v___x_2416_, 1, v___x_2415_);
v___x_2417_ = l_Lean_Syntax_node3(v___x_2399_, v___x_2400_, v___x_2402_, v___x_2414_, v___x_2416_);
if (v_isShared_2397_ == 0)
{
lean_ctor_set(v___x_2396_, 0, v___x_2417_);
v___x_2419_ = v___x_2396_;
goto v_reusejp_2418_;
}
else
{
lean_object* v_reuseFailAlloc_2420_; 
v_reuseFailAlloc_2420_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2420_, 0, v___x_2417_);
lean_ctor_set(v_reuseFailAlloc_2420_, 1, v_a_2394_);
v___x_2419_ = v_reuseFailAlloc_2420_;
goto v_reusejp_2418_;
}
v_reusejp_2418_:
{
return v___x_2419_;
}
}
}
else
{
lean_object* v_a_2422_; lean_object* v_a_2423_; lean_object* v___x_2425_; uint8_t v_isShared_2426_; uint8_t v_isSharedCheck_2430_; 
lean_dec(v_val_2352_);
lean_dec(v___x_2271_);
lean_dec(v___x_2185_);
v_a_2422_ = lean_ctor_get(v___x_2392_, 0);
v_a_2423_ = lean_ctor_get(v___x_2392_, 1);
v_isSharedCheck_2430_ = !lean_is_exclusive(v___x_2392_);
if (v_isSharedCheck_2430_ == 0)
{
v___x_2425_ = v___x_2392_;
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
else
{
lean_inc(v_a_2423_);
lean_inc(v_a_2422_);
lean_dec(v___x_2392_);
v___x_2425_ = lean_box(0);
v_isShared_2426_ = v_isSharedCheck_2430_;
goto v_resetjp_2424_;
}
v_resetjp_2424_:
{
lean_object* v___x_2428_; 
if (v_isShared_2426_ == 0)
{
v___x_2428_ = v___x_2425_;
goto v_reusejp_2427_;
}
else
{
lean_object* v_reuseFailAlloc_2429_; 
v_reuseFailAlloc_2429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2429_, 0, v_a_2422_);
lean_ctor_set(v_reuseFailAlloc_2429_, 1, v_a_2423_);
v___x_2428_ = v_reuseFailAlloc_2429_;
goto v_reusejp_2427_;
}
v_reusejp_2427_:
{
return v___x_2428_;
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
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandForall___boxed(lean_object* v_x_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_){
_start:
{
lean_object* v_res_2434_; 
v_res_2434_ = l_Std_Do_SPred_Notation_unexpandForall(v_x_2431_, v_a_2432_, v_a_2433_);
lean_dec(v_a_2432_);
return v_res_2434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1(lean_object* v___x_2439_, size_t v_sz_2440_, size_t v_i_2441_, lean_object* v_bs_2442_){
_start:
{
uint8_t v___x_2443_; 
v___x_2443_ = lean_usize_dec_lt(v_i_2441_, v_sz_2440_);
if (v___x_2443_ == 0)
{
lean_dec(v___x_2439_);
return v_bs_2442_;
}
else
{
lean_object* v___x_2444_; lean_object* v_v_2445_; lean_object* v___x_2446_; lean_object* v_bs_x27_2447_; lean_object* v___x_2448_; size_t v___x_2449_; size_t v___x_2450_; lean_object* v___x_2451_; 
v___x_2444_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
v_v_2445_ = lean_array_uget(v_bs_2442_, v_i_2441_);
v___x_2446_ = lean_unsigned_to_nat(0u);
v_bs_x27_2447_ = lean_array_uset(v_bs_2442_, v_i_2441_, v___x_2446_);
lean_inc(v___x_2439_);
v___x_2448_ = l_Lean_Syntax_node1(v___x_2439_, v___x_2444_, v_v_2445_);
v___x_2449_ = ((size_t)1ULL);
v___x_2450_ = lean_usize_add(v_i_2441_, v___x_2449_);
v___x_2451_ = lean_array_uset(v_bs_x27_2447_, v_i_2441_, v___x_2448_);
v_i_2441_ = v___x_2450_;
v_bs_2442_ = v___x_2451_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___boxed(lean_object* v___x_2453_, lean_object* v_sz_2454_, lean_object* v_i_2455_, lean_object* v_bs_2456_){
_start:
{
size_t v_sz_boxed_2457_; size_t v_i_boxed_2458_; lean_object* v_res_2459_; 
v_sz_boxed_2457_ = lean_unbox_usize(v_sz_2454_);
lean_dec(v_sz_2454_);
v_i_boxed_2458_ = lean_unbox_usize(v_i_2455_);
lean_dec(v_i_2455_);
v_res_2459_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1(v___x_2453_, v_sz_boxed_2457_, v_i_boxed_2458_, v_bs_2456_);
return v_res_2459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__0(size_t v_sz_2460_, size_t v_i_2461_, lean_object* v_bs_2462_){
_start:
{
uint8_t v___x_2463_; 
v___x_2463_ = lean_usize_dec_lt(v_i_2461_, v_sz_2460_);
if (v___x_2463_ == 0)
{
lean_object* v___x_2464_; 
v___x_2464_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2464_, 0, v_bs_2462_);
return v___x_2464_;
}
else
{
lean_object* v___x_2465_; lean_object* v_v_2466_; uint8_t v___x_2467_; 
v___x_2465_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
v_v_2466_ = lean_array_uget_borrowed(v_bs_2462_, v_i_2461_);
lean_inc(v_v_2466_);
v___x_2467_ = l_Lean_Syntax_isOfKind(v_v_2466_, v___x_2465_);
if (v___x_2467_ == 0)
{
lean_object* v___x_2468_; 
lean_dec_ref(v_bs_2462_);
v___x_2468_ = lean_box(0);
return v___x_2468_;
}
else
{
lean_object* v___x_2469_; lean_object* v_z_2470_; lean_object* v___x_2471_; uint8_t v___x_2472_; 
v___x_2469_ = lean_unsigned_to_nat(0u);
v_z_2470_ = l_Lean_Syntax_getArg(v_v_2466_, v___x_2469_);
v___x_2471_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v_z_2470_);
v___x_2472_ = l_Lean_Syntax_isOfKind(v_z_2470_, v___x_2471_);
if (v___x_2472_ == 0)
{
lean_object* v___x_2473_; 
lean_dec(v_z_2470_);
lean_dec_ref(v_bs_2462_);
v___x_2473_ = lean_box(0);
return v___x_2473_;
}
else
{
lean_object* v_bs_x27_2474_; size_t v___x_2475_; size_t v___x_2476_; lean_object* v___x_2477_; 
v_bs_x27_2474_ = lean_array_uset(v_bs_2462_, v_i_2461_, v___x_2469_);
v___x_2475_ = ((size_t)1ULL);
v___x_2476_ = lean_usize_add(v_i_2461_, v___x_2475_);
v___x_2477_ = lean_array_uset(v_bs_x27_2474_, v_i_2461_, v_z_2470_);
v_i_2461_ = v___x_2476_;
v_bs_2462_ = v___x_2477_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__0___boxed(lean_object* v_sz_2479_, lean_object* v_i_2480_, lean_object* v_bs_2481_){
_start:
{
size_t v_sz_boxed_2482_; size_t v_i_boxed_2483_; lean_object* v_res_2484_; 
v_sz_boxed_2482_ = lean_unbox_usize(v_sz_2479_);
lean_dec(v_sz_2479_);
v_i_boxed_2483_ = lean_unbox_usize(v_i_2480_);
lean_dec(v_i_2480_);
v_res_2484_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__0(v_sz_boxed_2482_, v_i_boxed_2483_, v_bs_2481_);
return v_res_2484_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandExists(lean_object* v_x_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_){
_start:
{
lean_object* v___x_2493_; uint8_t v___x_2494_; 
v___x_2493_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2490_);
v___x_2494_ = l_Lean_Syntax_isOfKind(v_x_2490_, v___x_2493_);
if (v___x_2494_ == 0)
{
lean_object* v___x_2495_; lean_object* v___x_2496_; 
lean_dec(v_x_2490_);
v___x_2495_ = lean_box(0);
v___x_2496_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2496_, 0, v___x_2495_);
lean_ctor_set(v___x_2496_, 1, v_a_2492_);
return v___x_2496_;
}
else
{
lean_object* v___x_2497_; lean_object* v___x_2498_; uint8_t v___x_2499_; 
v___x_2497_ = lean_unsigned_to_nat(1u);
v___x_2498_ = l_Lean_Syntax_getArg(v_x_2490_, v___x_2497_);
lean_dec(v_x_2490_);
lean_inc(v___x_2498_);
v___x_2499_ = l_Lean_Syntax_matchesNull(v___x_2498_, v___x_2497_);
if (v___x_2499_ == 0)
{
lean_object* v___x_2500_; lean_object* v___x_2501_; 
lean_dec(v___x_2498_);
v___x_2500_ = lean_box(0);
v___x_2501_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2501_, 0, v___x_2500_);
lean_ctor_set(v___x_2501_, 1, v_a_2492_);
return v___x_2501_;
}
else
{
lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; uint8_t v___x_2505_; 
v___x_2502_ = lean_unsigned_to_nat(0u);
v___x_2503_ = l_Lean_Syntax_getArg(v___x_2498_, v___x_2502_);
lean_dec(v___x_2498_);
v___x_2504_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__47));
lean_inc(v___x_2503_);
v___x_2505_ = l_Lean_Syntax_isOfKind(v___x_2503_, v___x_2504_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2506_; lean_object* v___x_2507_; 
lean_dec(v___x_2503_);
v___x_2506_ = lean_box(0);
v___x_2507_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2507_, 0, v___x_2506_);
lean_ctor_set(v___x_2507_, 1, v_a_2492_);
return v___x_2507_;
}
else
{
lean_object* v___x_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; 
v___x_2508_ = l_Lean_Syntax_getArg(v___x_2503_, v___x_2497_);
lean_dec(v___x_2503_);
v___x_2509_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__49));
lean_inc(v___x_2508_);
v___x_2510_ = l_Lean_Syntax_isOfKind(v___x_2508_, v___x_2509_);
if (v___x_2510_ == 0)
{
lean_object* v___x_2511_; lean_object* v___x_2512_; 
lean_dec(v___x_2508_);
v___x_2511_ = lean_box(0);
v___x_2512_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2512_, 0, v___x_2511_);
lean_ctor_set(v___x_2512_, 1, v_a_2492_);
return v___x_2512_;
}
else
{
lean_object* v___x_2513_; uint8_t v___x_2514_; 
v___x_2513_ = l_Lean_Syntax_getArg(v___x_2508_, v___x_2502_);
lean_inc(v___x_2513_);
v___x_2514_ = l_Lean_Syntax_matchesNull(v___x_2513_, v___x_2497_);
if (v___x_2514_ == 0)
{
lean_object* v___x_2515_; lean_object* v___x_2516_; 
lean_dec(v___x_2513_);
lean_dec(v___x_2508_);
v___x_2515_ = lean_box(0);
v___x_2516_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2516_, 0, v___x_2515_);
lean_ctor_set(v___x_2516_, 1, v_a_2492_);
return v___x_2516_;
}
else
{
lean_object* v___x_2517_; lean_object* v___x_2518_; uint8_t v___x_2519_; 
v___x_2517_ = l_Lean_Syntax_getArg(v___x_2513_, v___x_2502_);
lean_dec(v___x_2513_);
v___x_2518_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__60));
lean_inc(v___x_2517_);
v___x_2519_ = l_Lean_Syntax_isOfKind(v___x_2517_, v___x_2518_);
if (v___x_2519_ == 0)
{
lean_object* v___x_2520_; lean_object* v___x_2521_; 
lean_dec(v___x_2517_);
lean_dec(v___x_2508_);
v___x_2520_ = lean_box(0);
v___x_2521_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2521_, 0, v___x_2520_);
lean_ctor_set(v___x_2521_, 1, v_a_2492_);
return v___x_2521_;
}
else
{
lean_object* v___x_2522_; uint8_t v___x_2523_; 
v___x_2522_ = l_Lean_Syntax_getArg(v___x_2508_, v___x_2497_);
v___x_2523_ = l_Lean_Syntax_matchesNull(v___x_2522_, v___x_2502_);
if (v___x_2523_ == 0)
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
lean_dec(v___x_2517_);
lean_dec(v___x_2508_);
v___x_2524_ = lean_box(0);
v___x_2525_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2524_);
lean_ctor_set(v___x_2525_, 1, v_a_2492_);
return v___x_2525_;
}
else
{
lean_object* v___x_2526_; lean_object* v_00_u03a8_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; 
v___x_2526_ = lean_unsigned_to_nat(3u);
v_00_u03a8_2527_ = l_Lean_Syntax_getArg(v___x_2508_, v___x_2526_);
lean_dec(v___x_2508_);
v___x_2528_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__11));
lean_inc(v_00_u03a8_2527_);
v___x_2529_ = l_Lean_Syntax_isOfKind(v_00_u03a8_2527_, v___x_2528_);
if (v___x_2529_ == 0)
{
lean_object* v___x_2530_; 
v___x_2530_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2527_, v_a_2491_, v_a_2492_);
if (lean_obj_tag(v___x_2530_) == 0)
{
lean_object* v_a_2531_; lean_object* v_a_2532_; lean_object* v___x_2534_; uint8_t v_isShared_2535_; uint8_t v_isSharedCheck_2561_; 
v_a_2531_ = lean_ctor_get(v___x_2530_, 0);
v_a_2532_ = lean_ctor_get(v___x_2530_, 1);
v_isSharedCheck_2561_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2561_ == 0)
{
v___x_2534_ = v___x_2530_;
v_isShared_2535_ = v_isSharedCheck_2561_;
goto v_resetjp_2533_;
}
else
{
lean_inc(v_a_2532_);
lean_inc(v_a_2531_);
lean_dec(v___x_2530_);
v___x_2534_ = lean_box(0);
v_isShared_2535_ = v_isSharedCheck_2561_;
goto v_resetjp_2533_;
}
v_resetjp_2533_:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2559_; 
v___x_2536_ = l_Lean_SourceInfo_fromRef(v_a_2491_, v___x_2529_);
v___x_2537_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2538_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2536_, 10);
v___x_2539_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2536_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
v___x_2540_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_2541_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2541_, 0, v___x_2536_);
lean_ctor_set(v___x_2541_, 1, v___x_2540_);
v___x_2542_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65));
v___x_2543_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__2));
v___x_2544_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2545_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
v___x_2546_ = l_Lean_Syntax_node1(v___x_2536_, v___x_2545_, v___x_2517_);
v___x_2547_ = l_Lean_Syntax_node1(v___x_2536_, v___x_2544_, v___x_2546_);
v___x_2548_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2549_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2549_, 0, v___x_2536_);
lean_ctor_set(v___x_2549_, 1, v___x_2544_);
lean_ctor_set(v___x_2549_, 2, v___x_2548_);
v___x_2550_ = l_Lean_Syntax_node2(v___x_2536_, v___x_2543_, v___x_2547_, v___x_2549_);
v___x_2551_ = l_Lean_Syntax_node1(v___x_2536_, v___x_2542_, v___x_2550_);
v___x_2552_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_2553_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2536_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = l_Lean_Syntax_node4(v___x_2536_, v___x_2528_, v___x_2541_, v___x_2551_, v___x_2553_, v_a_2531_);
v___x_2555_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2556_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2556_, 0, v___x_2536_);
lean_ctor_set(v___x_2556_, 1, v___x_2555_);
v___x_2557_ = l_Lean_Syntax_node3(v___x_2536_, v___x_2537_, v___x_2539_, v___x_2554_, v___x_2556_);
if (v_isShared_2535_ == 0)
{
lean_ctor_set(v___x_2534_, 0, v___x_2557_);
v___x_2559_ = v___x_2534_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v___x_2557_);
lean_ctor_set(v_reuseFailAlloc_2560_, 1, v_a_2532_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
}
else
{
lean_object* v_a_2562_; lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec(v___x_2517_);
v_a_2562_ = lean_ctor_get(v___x_2530_, 0);
v_a_2563_ = lean_ctor_get(v___x_2530_, 1);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2530_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2530_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_inc(v_a_2562_);
lean_dec(v___x_2530_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2562_);
lean_ctor_set(v_reuseFailAlloc_2569_, 1, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
}
else
{
lean_object* v___x_2571_; lean_object* v___x_2572_; uint8_t v___x_2573_; 
v___x_2571_ = l_Lean_Syntax_getArg(v_00_u03a8_2527_, v___x_2497_);
v___x_2572_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__65));
lean_inc(v___x_2571_);
v___x_2573_ = l_Lean_Syntax_isOfKind(v___x_2571_, v___x_2572_);
if (v___x_2573_ == 0)
{
lean_object* v___x_2574_; 
lean_dec(v___x_2571_);
v___x_2574_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2527_, v_a_2491_, v_a_2492_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v_a_2576_; lean_object* v___x_2578_; uint8_t v_isShared_2579_; uint8_t v_isSharedCheck_2604_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
v_a_2576_ = lean_ctor_get(v___x_2574_, 1);
v_isSharedCheck_2604_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2604_ == 0)
{
v___x_2578_ = v___x_2574_;
v_isShared_2579_ = v_isSharedCheck_2604_;
goto v_resetjp_2577_;
}
else
{
lean_inc(v_a_2576_);
lean_inc(v_a_2575_);
lean_dec(v___x_2574_);
v___x_2578_ = lean_box(0);
v_isShared_2579_ = v_isSharedCheck_2604_;
goto v_resetjp_2577_;
}
v_resetjp_2577_:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2602_; 
v___x_2580_ = l_Lean_SourceInfo_fromRef(v_a_2491_, v___x_2573_);
v___x_2581_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2582_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2580_, 10);
v___x_2583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2580_);
lean_ctor_set(v___x_2583_, 1, v___x_2582_);
v___x_2584_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_2585_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2585_, 0, v___x_2580_);
lean_ctor_set(v___x_2585_, 1, v___x_2584_);
v___x_2586_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__2));
v___x_2587_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2588_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
v___x_2589_ = l_Lean_Syntax_node1(v___x_2580_, v___x_2588_, v___x_2517_);
v___x_2590_ = l_Lean_Syntax_node1(v___x_2580_, v___x_2587_, v___x_2589_);
v___x_2591_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2592_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2580_);
lean_ctor_set(v___x_2592_, 1, v___x_2587_);
lean_ctor_set(v___x_2592_, 2, v___x_2591_);
v___x_2593_ = l_Lean_Syntax_node2(v___x_2580_, v___x_2586_, v___x_2590_, v___x_2592_);
v___x_2594_ = l_Lean_Syntax_node1(v___x_2580_, v___x_2572_, v___x_2593_);
v___x_2595_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_2596_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2596_, 0, v___x_2580_);
lean_ctor_set(v___x_2596_, 1, v___x_2595_);
v___x_2597_ = l_Lean_Syntax_node4(v___x_2580_, v___x_2528_, v___x_2585_, v___x_2594_, v___x_2596_, v_a_2575_);
v___x_2598_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2599_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2599_, 0, v___x_2580_);
lean_ctor_set(v___x_2599_, 1, v___x_2598_);
v___x_2600_ = l_Lean_Syntax_node3(v___x_2580_, v___x_2581_, v___x_2583_, v___x_2597_, v___x_2599_);
if (v_isShared_2579_ == 0)
{
lean_ctor_set(v___x_2578_, 0, v___x_2600_);
v___x_2602_ = v___x_2578_;
goto v_reusejp_2601_;
}
else
{
lean_object* v_reuseFailAlloc_2603_; 
v_reuseFailAlloc_2603_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2603_, 0, v___x_2600_);
lean_ctor_set(v_reuseFailAlloc_2603_, 1, v_a_2576_);
v___x_2602_ = v_reuseFailAlloc_2603_;
goto v_reusejp_2601_;
}
v_reusejp_2601_:
{
return v___x_2602_;
}
}
}
else
{
lean_object* v_a_2605_; lean_object* v_a_2606_; lean_object* v___x_2608_; uint8_t v_isShared_2609_; uint8_t v_isSharedCheck_2613_; 
lean_dec(v___x_2517_);
v_a_2605_ = lean_ctor_get(v___x_2574_, 0);
v_a_2606_ = lean_ctor_get(v___x_2574_, 1);
v_isSharedCheck_2613_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2613_ == 0)
{
v___x_2608_ = v___x_2574_;
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
else
{
lean_inc(v_a_2606_);
lean_inc(v_a_2605_);
lean_dec(v___x_2574_);
v___x_2608_ = lean_box(0);
v_isShared_2609_ = v_isSharedCheck_2613_;
goto v_resetjp_2607_;
}
v_resetjp_2607_:
{
lean_object* v___x_2611_; 
if (v_isShared_2609_ == 0)
{
v___x_2611_ = v___x_2608_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_a_2605_);
lean_ctor_set(v_reuseFailAlloc_2612_, 1, v_a_2606_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
else
{
lean_object* v___x_2614_; lean_object* v___x_2615_; uint8_t v___x_2616_; 
v___x_2614_ = l_Lean_Syntax_getArg(v___x_2571_, v___x_2502_);
lean_dec(v___x_2571_);
v___x_2615_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__2));
lean_inc(v___x_2614_);
v___x_2616_ = l_Lean_Syntax_isOfKind(v___x_2614_, v___x_2615_);
if (v___x_2616_ == 0)
{
lean_object* v___x_2617_; 
lean_dec(v___x_2614_);
v___x_2617_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2527_, v_a_2491_, v_a_2492_);
if (lean_obj_tag(v___x_2617_) == 0)
{
lean_object* v_a_2618_; lean_object* v_a_2619_; lean_object* v___x_2621_; uint8_t v_isShared_2622_; uint8_t v_isSharedCheck_2646_; 
v_a_2618_ = lean_ctor_get(v___x_2617_, 0);
v_a_2619_ = lean_ctor_get(v___x_2617_, 1);
v_isSharedCheck_2646_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2621_ = v___x_2617_;
v_isShared_2622_ = v_isSharedCheck_2646_;
goto v_resetjp_2620_;
}
else
{
lean_inc(v_a_2619_);
lean_inc(v_a_2618_);
lean_dec(v___x_2617_);
v___x_2621_ = lean_box(0);
v_isShared_2622_ = v_isSharedCheck_2646_;
goto v_resetjp_2620_;
}
v_resetjp_2620_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2644_; 
v___x_2623_ = l_Lean_SourceInfo_fromRef(v_a_2491_, v___x_2616_);
v___x_2624_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2625_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2623_, 10);
v___x_2626_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2626_, 0, v___x_2623_);
lean_ctor_set(v___x_2626_, 1, v___x_2625_);
v___x_2627_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_2628_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2623_);
lean_ctor_set(v___x_2628_, 1, v___x_2627_);
v___x_2629_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2630_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
v___x_2631_ = l_Lean_Syntax_node1(v___x_2623_, v___x_2630_, v___x_2517_);
v___x_2632_ = l_Lean_Syntax_node1(v___x_2623_, v___x_2629_, v___x_2631_);
v___x_2633_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2634_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2623_);
lean_ctor_set(v___x_2634_, 1, v___x_2629_);
lean_ctor_set(v___x_2634_, 2, v___x_2633_);
v___x_2635_ = l_Lean_Syntax_node2(v___x_2623_, v___x_2615_, v___x_2632_, v___x_2634_);
v___x_2636_ = l_Lean_Syntax_node1(v___x_2623_, v___x_2572_, v___x_2635_);
v___x_2637_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_2638_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2638_, 0, v___x_2623_);
lean_ctor_set(v___x_2638_, 1, v___x_2637_);
v___x_2639_ = l_Lean_Syntax_node4(v___x_2623_, v___x_2528_, v___x_2628_, v___x_2636_, v___x_2638_, v_a_2618_);
v___x_2640_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2641_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2641_, 0, v___x_2623_);
lean_ctor_set(v___x_2641_, 1, v___x_2640_);
v___x_2642_ = l_Lean_Syntax_node3(v___x_2623_, v___x_2624_, v___x_2626_, v___x_2639_, v___x_2641_);
if (v_isShared_2622_ == 0)
{
lean_ctor_set(v___x_2621_, 0, v___x_2642_);
v___x_2644_ = v___x_2621_;
goto v_reusejp_2643_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v___x_2642_);
lean_ctor_set(v_reuseFailAlloc_2645_, 1, v_a_2619_);
v___x_2644_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2643_;
}
v_reusejp_2643_:
{
return v___x_2644_;
}
}
}
else
{
lean_object* v_a_2647_; lean_object* v_a_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2655_; 
lean_dec(v___x_2517_);
v_a_2647_ = lean_ctor_get(v___x_2617_, 0);
v_a_2648_ = lean_ctor_get(v___x_2617_, 1);
v_isSharedCheck_2655_ = !lean_is_exclusive(v___x_2617_);
if (v_isSharedCheck_2655_ == 0)
{
v___x_2650_ = v___x_2617_;
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
else
{
lean_inc(v_a_2648_);
lean_inc(v_a_2647_);
lean_dec(v___x_2617_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2655_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2653_; 
if (v_isShared_2651_ == 0)
{
v___x_2653_ = v___x_2650_;
goto v_reusejp_2652_;
}
else
{
lean_object* v_reuseFailAlloc_2654_; 
v_reuseFailAlloc_2654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2654_, 0, v_a_2647_);
lean_ctor_set(v_reuseFailAlloc_2654_, 1, v_a_2648_);
v___x_2653_ = v_reuseFailAlloc_2654_;
goto v_reusejp_2652_;
}
v_reusejp_2652_:
{
return v___x_2653_;
}
}
}
}
else
{
lean_object* v___x_2656_; lean_object* v___x_2657_; uint8_t v___x_2658_; 
v___x_2656_ = l_Lean_Syntax_getArg(v___x_2614_, v___x_2502_);
v___x_2657_ = l_Lean_Syntax_getNumArgs(v___x_2656_);
v___x_2658_ = lean_nat_dec_le(v___x_2497_, v___x_2657_);
if (v___x_2658_ == 0)
{
lean_object* v___x_2659_; 
lean_dec(v___x_2657_);
lean_dec(v___x_2656_);
lean_dec(v___x_2614_);
v___x_2659_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2527_, v_a_2491_, v_a_2492_);
if (lean_obj_tag(v___x_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2688_; 
v_a_2660_ = lean_ctor_get(v___x_2659_, 0);
v_a_2661_ = lean_ctor_get(v___x_2659_, 1);
v_isSharedCheck_2688_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2688_ == 0)
{
v___x_2663_ = v___x_2659_;
v_isShared_2664_ = v_isSharedCheck_2688_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_inc(v_a_2660_);
lean_dec(v___x_2659_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2688_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2686_; 
v___x_2665_ = l_Lean_SourceInfo_fromRef(v_a_2491_, v___x_2658_);
v___x_2666_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2667_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2665_, 10);
v___x_2668_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2668_, 0, v___x_2665_);
lean_ctor_set(v___x_2668_, 1, v___x_2667_);
v___x_2669_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_2670_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2670_, 0, v___x_2665_);
lean_ctor_set(v___x_2670_, 1, v___x_2669_);
v___x_2671_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2672_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
v___x_2673_ = l_Lean_Syntax_node1(v___x_2665_, v___x_2672_, v___x_2517_);
v___x_2674_ = l_Lean_Syntax_node1(v___x_2665_, v___x_2671_, v___x_2673_);
v___x_2675_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2676_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2676_, 0, v___x_2665_);
lean_ctor_set(v___x_2676_, 1, v___x_2671_);
lean_ctor_set(v___x_2676_, 2, v___x_2675_);
v___x_2677_ = l_Lean_Syntax_node2(v___x_2665_, v___x_2615_, v___x_2674_, v___x_2676_);
v___x_2678_ = l_Lean_Syntax_node1(v___x_2665_, v___x_2572_, v___x_2677_);
v___x_2679_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_2680_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2680_, 0, v___x_2665_);
lean_ctor_set(v___x_2680_, 1, v___x_2679_);
v___x_2681_ = l_Lean_Syntax_node4(v___x_2665_, v___x_2528_, v___x_2670_, v___x_2678_, v___x_2680_, v_a_2660_);
v___x_2682_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2683_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2683_, 0, v___x_2665_);
lean_ctor_set(v___x_2683_, 1, v___x_2682_);
v___x_2684_ = l_Lean_Syntax_node3(v___x_2665_, v___x_2666_, v___x_2668_, v___x_2681_, v___x_2683_);
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 0, v___x_2684_);
v___x_2686_ = v___x_2663_;
goto v_reusejp_2685_;
}
else
{
lean_object* v_reuseFailAlloc_2687_; 
v_reuseFailAlloc_2687_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2687_, 0, v___x_2684_);
lean_ctor_set(v_reuseFailAlloc_2687_, 1, v_a_2661_);
v___x_2686_ = v_reuseFailAlloc_2687_;
goto v_reusejp_2685_;
}
v_reusejp_2685_:
{
return v___x_2686_;
}
}
}
else
{
lean_object* v_a_2689_; lean_object* v_a_2690_; lean_object* v___x_2692_; uint8_t v_isShared_2693_; uint8_t v_isSharedCheck_2697_; 
lean_dec(v___x_2517_);
v_a_2689_ = lean_ctor_get(v___x_2659_, 0);
v_a_2690_ = lean_ctor_get(v___x_2659_, 1);
v_isSharedCheck_2697_ = !lean_is_exclusive(v___x_2659_);
if (v_isSharedCheck_2697_ == 0)
{
v___x_2692_ = v___x_2659_;
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
else
{
lean_inc(v_a_2690_);
lean_inc(v_a_2689_);
lean_dec(v___x_2659_);
v___x_2692_ = lean_box(0);
v_isShared_2693_ = v_isSharedCheck_2697_;
goto v_resetjp_2691_;
}
v_resetjp_2691_:
{
lean_object* v___x_2695_; 
if (v_isShared_2693_ == 0)
{
v___x_2695_ = v___x_2692_;
goto v_reusejp_2694_;
}
else
{
lean_object* v_reuseFailAlloc_2696_; 
v_reuseFailAlloc_2696_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2696_, 0, v_a_2689_);
lean_ctor_set(v_reuseFailAlloc_2696_, 1, v_a_2690_);
v___x_2695_ = v_reuseFailAlloc_2696_;
goto v_reusejp_2694_;
}
v_reusejp_2694_:
{
return v___x_2695_;
}
}
}
}
else
{
lean_object* v___x_2698_; lean_object* v___x_2699_; uint8_t v___x_2700_; 
v___x_2698_ = l_Lean_Syntax_getArg(v___x_2656_, v___x_2502_);
v___x_2699_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1___closed__1));
lean_inc(v___x_2698_);
v___x_2700_ = l_Lean_Syntax_isOfKind(v___x_2698_, v___x_2699_);
if (v___x_2700_ == 0)
{
lean_object* v___x_2701_; 
lean_dec(v___x_2698_);
lean_dec(v___x_2657_);
lean_dec(v___x_2656_);
lean_dec(v___x_2614_);
v___x_2701_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2527_, v_a_2491_, v_a_2492_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v_a_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2729_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
v_a_2703_ = lean_ctor_get(v___x_2701_, 1);
v_isSharedCheck_2729_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2729_ == 0)
{
v___x_2705_ = v___x_2701_;
v_isShared_2706_ = v_isSharedCheck_2729_;
goto v_resetjp_2704_;
}
else
{
lean_inc(v_a_2703_);
lean_inc(v_a_2702_);
lean_dec(v___x_2701_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2729_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2727_; 
v___x_2707_ = l_Lean_SourceInfo_fromRef(v_a_2491_, v___x_2700_);
v___x_2708_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2709_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2707_, 10);
v___x_2710_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2707_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_2712_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2707_);
lean_ctor_set(v___x_2712_, 1, v___x_2711_);
v___x_2713_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2714_ = l_Lean_Syntax_node1(v___x_2707_, v___x_2699_, v___x_2517_);
v___x_2715_ = l_Lean_Syntax_node1(v___x_2707_, v___x_2713_, v___x_2714_);
v___x_2716_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2717_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2717_, 0, v___x_2707_);
lean_ctor_set(v___x_2717_, 1, v___x_2713_);
lean_ctor_set(v___x_2717_, 2, v___x_2716_);
v___x_2718_ = l_Lean_Syntax_node2(v___x_2707_, v___x_2615_, v___x_2715_, v___x_2717_);
v___x_2719_ = l_Lean_Syntax_node1(v___x_2707_, v___x_2572_, v___x_2718_);
v___x_2720_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_2721_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2721_, 0, v___x_2707_);
lean_ctor_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = l_Lean_Syntax_node4(v___x_2707_, v___x_2528_, v___x_2712_, v___x_2719_, v___x_2721_, v_a_2702_);
v___x_2723_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2724_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2724_, 0, v___x_2707_);
lean_ctor_set(v___x_2724_, 1, v___x_2723_);
v___x_2725_ = l_Lean_Syntax_node3(v___x_2707_, v___x_2708_, v___x_2710_, v___x_2722_, v___x_2724_);
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 0, v___x_2725_);
v___x_2727_ = v___x_2705_;
goto v_reusejp_2726_;
}
else
{
lean_object* v_reuseFailAlloc_2728_; 
v_reuseFailAlloc_2728_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2728_, 0, v___x_2725_);
lean_ctor_set(v_reuseFailAlloc_2728_, 1, v_a_2703_);
v___x_2727_ = v_reuseFailAlloc_2728_;
goto v_reusejp_2726_;
}
v_reusejp_2726_:
{
return v___x_2727_;
}
}
}
else
{
lean_object* v_a_2730_; lean_object* v_a_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2738_; 
lean_dec(v___x_2517_);
v_a_2730_ = lean_ctor_get(v___x_2701_, 0);
v_a_2731_ = lean_ctor_get(v___x_2701_, 1);
v_isSharedCheck_2738_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2738_ == 0)
{
v___x_2733_ = v___x_2701_;
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_a_2731_);
lean_inc(v_a_2730_);
lean_dec(v___x_2701_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2738_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2736_; 
if (v_isShared_2734_ == 0)
{
v___x_2736_ = v___x_2733_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2737_; 
v_reuseFailAlloc_2737_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2737_, 0, v_a_2730_);
lean_ctor_set(v_reuseFailAlloc_2737_, 1, v_a_2731_);
v___x_2736_ = v_reuseFailAlloc_2737_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
return v___x_2736_;
}
}
}
}
else
{
lean_object* v___x_2739_; uint8_t v___x_2740_; 
v___x_2739_ = l_Lean_Syntax_getArg(v___x_2698_, v___x_2502_);
lean_dec(v___x_2698_);
lean_inc(v___x_2739_);
v___x_2740_ = l_Lean_Syntax_isOfKind(v___x_2739_, v___x_2518_);
if (v___x_2740_ == 0)
{
lean_object* v___x_2741_; 
lean_dec(v___x_2739_);
lean_dec(v___x_2657_);
lean_dec(v___x_2656_);
lean_dec(v___x_2614_);
v___x_2741_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2527_, v_a_2491_, v_a_2492_);
if (lean_obj_tag(v___x_2741_) == 0)
{
lean_object* v_a_2742_; lean_object* v_a_2743_; lean_object* v___x_2745_; uint8_t v_isShared_2746_; uint8_t v_isSharedCheck_2769_; 
v_a_2742_ = lean_ctor_get(v___x_2741_, 0);
v_a_2743_ = lean_ctor_get(v___x_2741_, 1);
v_isSharedCheck_2769_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2769_ == 0)
{
v___x_2745_ = v___x_2741_;
v_isShared_2746_ = v_isSharedCheck_2769_;
goto v_resetjp_2744_;
}
else
{
lean_inc(v_a_2743_);
lean_inc(v_a_2742_);
lean_dec(v___x_2741_);
v___x_2745_ = lean_box(0);
v_isShared_2746_ = v_isSharedCheck_2769_;
goto v_resetjp_2744_;
}
v_resetjp_2744_:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; lean_object* v___x_2758_; lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2767_; 
v___x_2747_ = l_Lean_SourceInfo_fromRef(v_a_2491_, v___x_2740_);
v___x_2748_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2749_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2747_, 10);
v___x_2750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2747_);
lean_ctor_set(v___x_2750_, 1, v___x_2749_);
v___x_2751_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_2752_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2752_, 0, v___x_2747_);
lean_ctor_set(v___x_2752_, 1, v___x_2751_);
v___x_2753_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2754_ = l_Lean_Syntax_node1(v___x_2747_, v___x_2699_, v___x_2517_);
v___x_2755_ = l_Lean_Syntax_node1(v___x_2747_, v___x_2753_, v___x_2754_);
v___x_2756_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2757_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2757_, 0, v___x_2747_);
lean_ctor_set(v___x_2757_, 1, v___x_2753_);
lean_ctor_set(v___x_2757_, 2, v___x_2756_);
v___x_2758_ = l_Lean_Syntax_node2(v___x_2747_, v___x_2615_, v___x_2755_, v___x_2757_);
v___x_2759_ = l_Lean_Syntax_node1(v___x_2747_, v___x_2572_, v___x_2758_);
v___x_2760_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_2761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2761_, 0, v___x_2747_);
lean_ctor_set(v___x_2761_, 1, v___x_2760_);
v___x_2762_ = l_Lean_Syntax_node4(v___x_2747_, v___x_2528_, v___x_2752_, v___x_2759_, v___x_2761_, v_a_2742_);
v___x_2763_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2747_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
v___x_2765_ = l_Lean_Syntax_node3(v___x_2747_, v___x_2748_, v___x_2750_, v___x_2762_, v___x_2764_);
if (v_isShared_2746_ == 0)
{
lean_ctor_set(v___x_2745_, 0, v___x_2765_);
v___x_2767_ = v___x_2745_;
goto v_reusejp_2766_;
}
else
{
lean_object* v_reuseFailAlloc_2768_; 
v_reuseFailAlloc_2768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2768_, 0, v___x_2765_);
lean_ctor_set(v_reuseFailAlloc_2768_, 1, v_a_2743_);
v___x_2767_ = v_reuseFailAlloc_2768_;
goto v_reusejp_2766_;
}
v_reusejp_2766_:
{
return v___x_2767_;
}
}
}
else
{
lean_object* v_a_2770_; lean_object* v_a_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2778_; 
lean_dec(v___x_2517_);
v_a_2770_ = lean_ctor_get(v___x_2741_, 0);
v_a_2771_ = lean_ctor_get(v___x_2741_, 1);
v_isSharedCheck_2778_ = !lean_is_exclusive(v___x_2741_);
if (v_isSharedCheck_2778_ == 0)
{
v___x_2773_ = v___x_2741_;
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_a_2771_);
lean_inc(v_a_2770_);
lean_dec(v___x_2741_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2778_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
lean_object* v___x_2776_; 
if (v_isShared_2774_ == 0)
{
v___x_2776_ = v___x_2773_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_a_2770_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v_a_2771_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
else
{
lean_object* v___x_2779_; lean_object* v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; size_t v_sz_2785_; size_t v___x_2786_; lean_object* v___x_2787_; 
v___x_2779_ = l_Lean_Syntax_getArgs(v___x_2656_);
lean_dec(v___x_2656_);
v___x_2780_ = l_Array_extract___redArg(v___x_2779_, v___x_2497_, v___x_2657_);
lean_dec_ref(v___x_2779_);
v___x_2781_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__16));
v___x_2782_ = lean_box(2);
v___x_2783_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2783_, 0, v___x_2782_);
lean_ctor_set(v___x_2783_, 1, v___x_2781_);
lean_ctor_set(v___x_2783_, 2, v___x_2780_);
v___x_2784_ = l_Lean_Syntax_getArgs(v___x_2783_);
lean_dec_ref_known(v___x_2783_, 3);
v_sz_2785_ = lean_array_size(v___x_2784_);
v___x_2786_ = ((size_t)0ULL);
v___x_2787_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__0(v_sz_2785_, v___x_2786_, v___x_2784_);
if (lean_obj_tag(v___x_2787_) == 0)
{
lean_object* v___x_2788_; 
lean_dec(v___x_2739_);
lean_dec(v___x_2614_);
v___x_2788_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2527_, v_a_2491_, v_a_2492_);
if (lean_obj_tag(v___x_2788_) == 0)
{
lean_object* v_a_2789_; lean_object* v_a_2790_; lean_object* v___x_2792_; uint8_t v_isShared_2793_; uint8_t v_isSharedCheck_2816_; 
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
v_a_2790_ = lean_ctor_get(v___x_2788_, 1);
v_isSharedCheck_2816_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2816_ == 0)
{
v___x_2792_ = v___x_2788_;
v_isShared_2793_ = v_isSharedCheck_2816_;
goto v_resetjp_2791_;
}
else
{
lean_inc(v_a_2790_);
lean_inc(v_a_2789_);
lean_dec(v___x_2788_);
v___x_2792_ = lean_box(0);
v_isShared_2793_ = v_isSharedCheck_2816_;
goto v_resetjp_2791_;
}
v_resetjp_2791_:
{
uint8_t v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2814_; 
v___x_2794_ = 0;
v___x_2795_ = l_Lean_SourceInfo_fromRef(v_a_2491_, v___x_2794_);
v___x_2796_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2797_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2795_, 10);
v___x_2798_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2795_);
lean_ctor_set(v___x_2798_, 1, v___x_2797_);
v___x_2799_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_2800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2800_, 0, v___x_2795_);
lean_ctor_set(v___x_2800_, 1, v___x_2799_);
v___x_2801_ = l_Lean_Syntax_node1(v___x_2795_, v___x_2699_, v___x_2517_);
v___x_2802_ = l_Lean_Syntax_node1(v___x_2795_, v___x_2781_, v___x_2801_);
v___x_2803_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2804_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2804_, 0, v___x_2795_);
lean_ctor_set(v___x_2804_, 1, v___x_2781_);
lean_ctor_set(v___x_2804_, 2, v___x_2803_);
v___x_2805_ = l_Lean_Syntax_node2(v___x_2795_, v___x_2615_, v___x_2802_, v___x_2804_);
v___x_2806_ = l_Lean_Syntax_node1(v___x_2795_, v___x_2572_, v___x_2805_);
v___x_2807_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_2808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2808_, 0, v___x_2795_);
lean_ctor_set(v___x_2808_, 1, v___x_2807_);
v___x_2809_ = l_Lean_Syntax_node4(v___x_2795_, v___x_2528_, v___x_2800_, v___x_2806_, v___x_2808_, v_a_2789_);
v___x_2810_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2811_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2811_, 0, v___x_2795_);
lean_ctor_set(v___x_2811_, 1, v___x_2810_);
v___x_2812_ = l_Lean_Syntax_node3(v___x_2795_, v___x_2796_, v___x_2798_, v___x_2809_, v___x_2811_);
if (v_isShared_2793_ == 0)
{
lean_ctor_set(v___x_2792_, 0, v___x_2812_);
v___x_2814_ = v___x_2792_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v___x_2812_);
lean_ctor_set(v_reuseFailAlloc_2815_, 1, v_a_2790_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
else
{
lean_object* v_a_2817_; lean_object* v_a_2818_; lean_object* v___x_2820_; uint8_t v_isShared_2821_; uint8_t v_isSharedCheck_2825_; 
lean_dec(v___x_2517_);
v_a_2817_ = lean_ctor_get(v___x_2788_, 0);
v_a_2818_ = lean_ctor_get(v___x_2788_, 1);
v_isSharedCheck_2825_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2825_ == 0)
{
v___x_2820_ = v___x_2788_;
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
else
{
lean_inc(v_a_2818_);
lean_inc(v_a_2817_);
lean_dec(v___x_2788_);
v___x_2820_ = lean_box(0);
v_isShared_2821_ = v_isSharedCheck_2825_;
goto v_resetjp_2819_;
}
v_resetjp_2819_:
{
lean_object* v___x_2823_; 
if (v_isShared_2821_ == 0)
{
v___x_2823_ = v___x_2820_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2824_; 
v_reuseFailAlloc_2824_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2824_, 0, v_a_2817_);
lean_ctor_set(v_reuseFailAlloc_2824_, 1, v_a_2818_);
v___x_2823_ = v_reuseFailAlloc_2824_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
return v___x_2823_;
}
}
}
}
else
{
lean_object* v_val_2826_; lean_object* v___x_2827_; uint8_t v___x_2828_; 
v_val_2826_ = lean_ctor_get(v___x_2787_, 0);
lean_inc(v_val_2826_);
lean_dec_ref_known(v___x_2787_, 1);
v___x_2827_ = l_Lean_Syntax_getArg(v___x_2614_, v___x_2497_);
lean_dec(v___x_2614_);
v___x_2828_ = l_Lean_Syntax_matchesNull(v___x_2827_, v___x_2502_);
if (v___x_2828_ == 0)
{
lean_object* v___x_2829_; 
lean_dec(v_val_2826_);
lean_dec(v___x_2739_);
v___x_2829_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2527_, v_a_2491_, v_a_2492_);
if (lean_obj_tag(v___x_2829_) == 0)
{
lean_object* v_a_2830_; lean_object* v_a_2831_; lean_object* v___x_2833_; uint8_t v_isShared_2834_; uint8_t v_isSharedCheck_2856_; 
v_a_2830_ = lean_ctor_get(v___x_2829_, 0);
v_a_2831_ = lean_ctor_get(v___x_2829_, 1);
v_isSharedCheck_2856_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2856_ == 0)
{
v___x_2833_ = v___x_2829_;
v_isShared_2834_ = v_isSharedCheck_2856_;
goto v_resetjp_2832_;
}
else
{
lean_inc(v_a_2831_);
lean_inc(v_a_2830_);
lean_dec(v___x_2829_);
v___x_2833_ = lean_box(0);
v_isShared_2834_ = v_isSharedCheck_2856_;
goto v_resetjp_2832_;
}
v_resetjp_2832_:
{
lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; lean_object* v___x_2839_; lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2854_; 
v___x_2835_ = l_Lean_SourceInfo_fromRef(v_a_2491_, v___x_2828_);
v___x_2836_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2837_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2835_, 10);
v___x_2838_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2838_, 0, v___x_2835_);
lean_ctor_set(v___x_2838_, 1, v___x_2837_);
v___x_2839_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_2840_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2840_, 0, v___x_2835_);
lean_ctor_set(v___x_2840_, 1, v___x_2839_);
v___x_2841_ = l_Lean_Syntax_node1(v___x_2835_, v___x_2699_, v___x_2517_);
v___x_2842_ = l_Lean_Syntax_node1(v___x_2835_, v___x_2781_, v___x_2841_);
v___x_2843_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2844_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2844_, 0, v___x_2835_);
lean_ctor_set(v___x_2844_, 1, v___x_2781_);
lean_ctor_set(v___x_2844_, 2, v___x_2843_);
v___x_2845_ = l_Lean_Syntax_node2(v___x_2835_, v___x_2615_, v___x_2842_, v___x_2844_);
v___x_2846_ = l_Lean_Syntax_node1(v___x_2835_, v___x_2572_, v___x_2845_);
v___x_2847_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_2848_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2848_, 0, v___x_2835_);
lean_ctor_set(v___x_2848_, 1, v___x_2847_);
v___x_2849_ = l_Lean_Syntax_node4(v___x_2835_, v___x_2528_, v___x_2840_, v___x_2846_, v___x_2848_, v_a_2830_);
v___x_2850_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2851_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2851_, 0, v___x_2835_);
lean_ctor_set(v___x_2851_, 1, v___x_2850_);
v___x_2852_ = l_Lean_Syntax_node3(v___x_2835_, v___x_2836_, v___x_2838_, v___x_2849_, v___x_2851_);
if (v_isShared_2834_ == 0)
{
lean_ctor_set(v___x_2833_, 0, v___x_2852_);
v___x_2854_ = v___x_2833_;
goto v_reusejp_2853_;
}
else
{
lean_object* v_reuseFailAlloc_2855_; 
v_reuseFailAlloc_2855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2855_, 0, v___x_2852_);
lean_ctor_set(v_reuseFailAlloc_2855_, 1, v_a_2831_);
v___x_2854_ = v_reuseFailAlloc_2855_;
goto v_reusejp_2853_;
}
v_reusejp_2853_:
{
return v___x_2854_;
}
}
}
else
{
lean_object* v_a_2857_; lean_object* v_a_2858_; lean_object* v___x_2860_; uint8_t v_isShared_2861_; uint8_t v_isSharedCheck_2865_; 
lean_dec(v___x_2517_);
v_a_2857_ = lean_ctor_get(v___x_2829_, 0);
v_a_2858_ = lean_ctor_get(v___x_2829_, 1);
v_isSharedCheck_2865_ = !lean_is_exclusive(v___x_2829_);
if (v_isSharedCheck_2865_ == 0)
{
v___x_2860_ = v___x_2829_;
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
else
{
lean_inc(v_a_2858_);
lean_inc(v_a_2857_);
lean_dec(v___x_2829_);
v___x_2860_ = lean_box(0);
v_isShared_2861_ = v_isSharedCheck_2865_;
goto v_resetjp_2859_;
}
v_resetjp_2859_:
{
lean_object* v___x_2863_; 
if (v_isShared_2861_ == 0)
{
v___x_2863_ = v___x_2860_;
goto v_reusejp_2862_;
}
else
{
lean_object* v_reuseFailAlloc_2864_; 
v_reuseFailAlloc_2864_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2864_, 0, v_a_2857_);
lean_ctor_set(v_reuseFailAlloc_2864_, 1, v_a_2858_);
v___x_2863_ = v_reuseFailAlloc_2864_;
goto v_reusejp_2862_;
}
v_reusejp_2862_:
{
return v___x_2863_;
}
}
}
}
else
{
lean_object* v_00_u03a8_2866_; lean_object* v___x_2867_; 
v_00_u03a8_2866_ = l_Lean_Syntax_getArg(v_00_u03a8_2527_, v___x_2526_);
lean_dec(v_00_u03a8_2527_);
v___x_2867_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_00_u03a8_2866_, v_a_2491_, v_a_2492_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2900_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
v_a_2869_ = lean_ctor_get(v___x_2867_, 1);
v_isSharedCheck_2900_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2900_ == 0)
{
v___x_2871_ = v___x_2867_;
v_isShared_2872_ = v_isSharedCheck_2900_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_inc(v_a_2868_);
lean_dec(v___x_2867_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2900_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
uint8_t v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; size_t v_sz_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2898_; 
v___x_2873_ = 0;
v___x_2874_ = l_Lean_SourceInfo_fromRef(v_a_2491_, v___x_2873_);
v___x_2875_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2876_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2874_, 12);
v___x_2877_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2874_);
lean_ctor_set(v___x_2877_, 1, v___x_2876_);
v___x_2878_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandExists___closed__0));
v___x_2879_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2874_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
v___x_2880_ = l_Lean_Syntax_node1(v___x_2874_, v___x_2699_, v___x_2517_);
v___x_2881_ = l_Lean_Syntax_node1(v___x_2874_, v___x_2699_, v___x_2739_);
v___x_2882_ = l_Array_mkArray2___redArg(v___x_2880_, v___x_2881_);
v_sz_2883_ = lean_array_size(v_val_2826_);
v___x_2884_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do_SPred_Notation_unexpandExists_spec__1(v___x_2874_, v_sz_2883_, v___x_2786_, v_val_2826_);
v___x_2885_ = l_Array_append___redArg(v___x_2882_, v___x_2884_);
lean_dec_ref(v___x_2884_);
v___x_2886_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2886_, 0, v___x_2874_);
lean_ctor_set(v___x_2886_, 1, v___x_2781_);
lean_ctor_set(v___x_2886_, 2, v___x_2885_);
v___x_2887_ = lean_obj_once(&l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50, &l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50_once, _init_l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__50);
v___x_2888_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_2888_, 0, v___x_2874_);
lean_ctor_set(v___x_2888_, 1, v___x_2781_);
lean_ctor_set(v___x_2888_, 2, v___x_2887_);
v___x_2889_ = l_Lean_Syntax_node2(v___x_2874_, v___x_2615_, v___x_2886_, v___x_2888_);
v___x_2890_ = l_Lean_Syntax_node1(v___x_2874_, v___x_2572_, v___x_2889_);
v___x_2891_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__53));
v___x_2892_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2874_);
lean_ctor_set(v___x_2892_, 1, v___x_2891_);
v___x_2893_ = l_Lean_Syntax_node4(v___x_2874_, v___x_2528_, v___x_2879_, v___x_2890_, v___x_2892_, v_a_2868_);
v___x_2894_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2895_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2895_, 0, v___x_2874_);
lean_ctor_set(v___x_2895_, 1, v___x_2894_);
v___x_2896_ = l_Lean_Syntax_node3(v___x_2874_, v___x_2875_, v___x_2877_, v___x_2893_, v___x_2895_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v___x_2896_);
v___x_2898_ = v___x_2871_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2899_; 
v_reuseFailAlloc_2899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2899_, 0, v___x_2896_);
lean_ctor_set(v_reuseFailAlloc_2899_, 1, v_a_2869_);
v___x_2898_ = v_reuseFailAlloc_2899_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
return v___x_2898_;
}
}
}
else
{
lean_object* v_a_2901_; lean_object* v_a_2902_; lean_object* v___x_2904_; uint8_t v_isShared_2905_; uint8_t v_isSharedCheck_2909_; 
lean_dec(v_val_2826_);
lean_dec(v___x_2739_);
lean_dec(v___x_2517_);
v_a_2901_ = lean_ctor_get(v___x_2867_, 0);
v_a_2902_ = lean_ctor_get(v___x_2867_, 1);
v_isSharedCheck_2909_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2909_ == 0)
{
v___x_2904_ = v___x_2867_;
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
else
{
lean_inc(v_a_2902_);
lean_inc(v_a_2901_);
lean_dec(v___x_2867_);
v___x_2904_ = lean_box(0);
v_isShared_2905_ = v_isSharedCheck_2909_;
goto v_resetjp_2903_;
}
v_resetjp_2903_:
{
lean_object* v___x_2907_; 
if (v_isShared_2905_ == 0)
{
v___x_2907_ = v___x_2904_;
goto v_reusejp_2906_;
}
else
{
lean_object* v_reuseFailAlloc_2908_; 
v_reuseFailAlloc_2908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2908_, 0, v_a_2901_);
lean_ctor_set(v_reuseFailAlloc_2908_, 1, v_a_2902_);
v___x_2907_ = v_reuseFailAlloc_2908_;
goto v_reusejp_2906_;
}
v_reusejp_2906_:
{
return v___x_2907_;
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
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandExists___boxed(lean_object* v_x_2910_, lean_object* v_a_2911_, lean_object* v_a_2912_){
_start:
{
lean_object* v_res_2913_; 
v_res_2913_ = l_Std_Do_SPred_Notation_unexpandExists(v_x_2910_, v_a_2911_, v_a_2912_);
lean_dec(v_a_2911_);
return v_res_2913_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandIff(lean_object* v_x_2915_, lean_object* v_a_2916_, lean_object* v_a_2917_){
_start:
{
lean_object* v___x_2918_; uint8_t v___x_2919_; 
v___x_2918_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term_u231c___u231d__1___closed__4));
lean_inc(v_x_2915_);
v___x_2919_ = l_Lean_Syntax_isOfKind(v_x_2915_, v___x_2918_);
if (v___x_2919_ == 0)
{
lean_object* v___x_2920_; lean_object* v___x_2921_; 
lean_dec(v_x_2915_);
v___x_2920_ = lean_box(0);
v___x_2921_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2921_, 0, v___x_2920_);
lean_ctor_set(v___x_2921_, 1, v_a_2917_);
return v___x_2921_;
}
else
{
lean_object* v___x_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; uint8_t v___x_2925_; 
v___x_2922_ = lean_unsigned_to_nat(1u);
v___x_2923_ = l_Lean_Syntax_getArg(v_x_2915_, v___x_2922_);
lean_dec(v_x_2915_);
v___x_2924_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_2923_);
v___x_2925_ = l_Lean_Syntax_matchesNull(v___x_2923_, v___x_2924_);
if (v___x_2925_ == 0)
{
lean_object* v___x_2926_; lean_object* v___x_2927_; 
lean_dec(v___x_2923_);
v___x_2926_ = lean_box(0);
v___x_2927_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2927_, 0, v___x_2926_);
lean_ctor_set(v___x_2927_, 1, v_a_2917_);
return v___x_2927_;
}
else
{
lean_object* v___x_2928_; lean_object* v_P_2929_; lean_object* v___x_2930_; 
v___x_2928_ = lean_unsigned_to_nat(0u);
v_P_2929_ = l_Lean_Syntax_getArg(v___x_2923_, v___x_2928_);
v___x_2930_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_P_2929_, v_a_2916_, v_a_2917_);
if (lean_obj_tag(v___x_2930_) == 0)
{
lean_object* v_a_2931_; lean_object* v_a_2932_; lean_object* v_Q_2933_; lean_object* v___x_2934_; 
v_a_2931_ = lean_ctor_get(v___x_2930_, 0);
lean_inc(v_a_2931_);
v_a_2932_ = lean_ctor_get(v___x_2930_, 1);
lean_inc(v_a_2932_);
lean_dec_ref_known(v___x_2930_, 2);
v_Q_2933_ = l_Lean_Syntax_getArg(v___x_2923_, v___x_2922_);
lean_dec(v___x_2923_);
v___x_2934_ = l_Std_Do_SPred_Notation_unpack___at___00Std_Do_SPred_Notation_unexpandEntails_spec__0(v_Q_2933_, v_a_2916_, v_a_2932_);
if (lean_obj_tag(v___x_2934_) == 0)
{
lean_object* v_a_2935_; lean_object* v_a_2936_; lean_object* v___x_2938_; uint8_t v_isShared_2939_; uint8_t v_isSharedCheck_2955_; 
v_a_2935_ = lean_ctor_get(v___x_2934_, 0);
v_a_2936_ = lean_ctor_get(v___x_2934_, 1);
v_isSharedCheck_2955_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2955_ == 0)
{
v___x_2938_ = v___x_2934_;
v_isShared_2939_ = v_isSharedCheck_2955_;
goto v_resetjp_2937_;
}
else
{
lean_inc(v_a_2936_);
lean_inc(v_a_2935_);
lean_dec(v___x_2934_);
v___x_2938_ = lean_box(0);
v_isShared_2939_ = v_isSharedCheck_2955_;
goto v_resetjp_2937_;
}
v_resetjp_2937_:
{
uint8_t v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v___x_2953_; 
v___x_2940_ = 0;
v___x_2941_ = l_Lean_SourceInfo_fromRef(v_a_2916_, v___x_2940_);
v___x_2942_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__10));
v___x_2943_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__11));
lean_inc_n(v___x_2941_, 4);
v___x_2944_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2944_, 0, v___x_2941_);
lean_ctor_set(v___x_2944_, 1, v___x_2943_);
v___x_2945_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__termSpred_x28___x29__1___closed__9));
v___x_2946_ = ((lean_object*)(l_Std_Do_SPred_Notation_unexpandIff___closed__0));
v___x_2947_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2941_);
lean_ctor_set(v___x_2947_, 1, v___x_2946_);
v___x_2948_ = l_Lean_Syntax_node3(v___x_2941_, v___x_2945_, v_a_2931_, v___x_2947_, v_a_2935_);
v___x_2949_ = ((lean_object*)(l_Std_Do___aux__Std__Do__SPred__Notation______macroRules__Std__Do__term___u22a2_u209b____1___closed__12));
v___x_2950_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2941_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
v___x_2951_ = l_Lean_Syntax_node3(v___x_2941_, v___x_2942_, v___x_2944_, v___x_2948_, v___x_2950_);
if (v_isShared_2939_ == 0)
{
lean_ctor_set(v___x_2938_, 0, v___x_2951_);
v___x_2953_ = v___x_2938_;
goto v_reusejp_2952_;
}
else
{
lean_object* v_reuseFailAlloc_2954_; 
v_reuseFailAlloc_2954_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2954_, 0, v___x_2951_);
lean_ctor_set(v_reuseFailAlloc_2954_, 1, v_a_2936_);
v___x_2953_ = v_reuseFailAlloc_2954_;
goto v_reusejp_2952_;
}
v_reusejp_2952_:
{
return v___x_2953_;
}
}
}
else
{
lean_object* v_a_2956_; lean_object* v_a_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2964_; 
lean_dec(v_a_2931_);
v_a_2956_ = lean_ctor_get(v___x_2934_, 0);
v_a_2957_ = lean_ctor_get(v___x_2934_, 1);
v_isSharedCheck_2964_ = !lean_is_exclusive(v___x_2934_);
if (v_isSharedCheck_2964_ == 0)
{
v___x_2959_ = v___x_2934_;
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
else
{
lean_inc(v_a_2957_);
lean_inc(v_a_2956_);
lean_dec(v___x_2934_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2964_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2962_; 
if (v_isShared_2960_ == 0)
{
v___x_2962_ = v___x_2959_;
goto v_reusejp_2961_;
}
else
{
lean_object* v_reuseFailAlloc_2963_; 
v_reuseFailAlloc_2963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2963_, 0, v_a_2956_);
lean_ctor_set(v_reuseFailAlloc_2963_, 1, v_a_2957_);
v___x_2962_ = v_reuseFailAlloc_2963_;
goto v_reusejp_2961_;
}
v_reusejp_2961_:
{
return v___x_2962_;
}
}
}
}
else
{
lean_object* v_a_2965_; lean_object* v_a_2966_; lean_object* v___x_2968_; uint8_t v_isShared_2969_; uint8_t v_isSharedCheck_2973_; 
lean_dec(v___x_2923_);
v_a_2965_ = lean_ctor_get(v___x_2930_, 0);
v_a_2966_ = lean_ctor_get(v___x_2930_, 1);
v_isSharedCheck_2973_ = !lean_is_exclusive(v___x_2930_);
if (v_isSharedCheck_2973_ == 0)
{
v___x_2968_ = v___x_2930_;
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
else
{
lean_inc(v_a_2966_);
lean_inc(v_a_2965_);
lean_dec(v___x_2930_);
v___x_2968_ = lean_box(0);
v_isShared_2969_ = v_isSharedCheck_2973_;
goto v_resetjp_2967_;
}
v_resetjp_2967_:
{
lean_object* v___x_2971_; 
if (v_isShared_2969_ == 0)
{
v___x_2971_ = v___x_2968_;
goto v_reusejp_2970_;
}
else
{
lean_object* v_reuseFailAlloc_2972_; 
v_reuseFailAlloc_2972_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2972_, 0, v_a_2965_);
lean_ctor_set(v_reuseFailAlloc_2972_, 1, v_a_2966_);
v___x_2971_ = v_reuseFailAlloc_2972_;
goto v_reusejp_2970_;
}
v_reusejp_2970_:
{
return v___x_2971_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_SPred_Notation_unexpandIff___boxed(lean_object* v_x_2974_, lean_object* v_a_2975_, lean_object* v_a_2976_){
_start:
{
lean_object* v_res_2977_; 
v_res_2977_ = l_Std_Do_SPred_Notation_unexpandIff(v_x_2974_, v_a_2975_, v_a_2976_);
lean_dec(v_a_2975_);
return v_res_2977_;
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
