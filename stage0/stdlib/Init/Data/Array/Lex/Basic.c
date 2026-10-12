// Lean compiler output
// Module: Init.Data.Array.Lex.Basic
// Imports: public import Init.Data.Range.Polymorphic.RangeIterator import Init.Data.Range.Polymorphic.Iterators import Init.Data.Range.Polymorphic.Nat import Init.Omega
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
lean_object* l_Lean_mkAtom(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
static const lean_string_object l_Array_lex___auto__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Array_lex___auto__1___closed__0 = (const lean_object*)&l_Array_lex___auto__1___closed__0_value;
static const lean_string_object l_Array_lex___auto__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Array_lex___auto__1___closed__1 = (const lean_object*)&l_Array_lex___auto__1___closed__1_value;
static const lean_string_object l_Array_lex___auto__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Array_lex___auto__1___closed__2 = (const lean_object*)&l_Array_lex___auto__1___closed__2_value;
static const lean_string_object l_Array_lex___auto__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Array_lex___auto__1___closed__3 = (const lean_object*)&l_Array_lex___auto__1___closed__3_value;
static const lean_ctor_object l_Array_lex___auto__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_lex___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_lex___auto__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_lex___auto__1___closed__4_value_aux_0),((lean_object*)&l_Array_lex___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_lex___auto__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_lex___auto__1___closed__4_value_aux_1),((lean_object*)&l_Array_lex___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array_lex___auto__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_lex___auto__1___closed__4_value_aux_2),((lean_object*)&l_Array_lex___auto__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Array_lex___auto__1___closed__4 = (const lean_object*)&l_Array_lex___auto__1___closed__4_value;
static const lean_array_object l_Array_lex___auto__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_lex___auto__1___closed__5 = (const lean_object*)&l_Array_lex___auto__1___closed__5_value;
static const lean_string_object l_Array_lex___auto__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Array_lex___auto__1___closed__6 = (const lean_object*)&l_Array_lex___auto__1___closed__6_value;
static const lean_ctor_object l_Array_lex___auto__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_lex___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_lex___auto__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_lex___auto__1___closed__7_value_aux_0),((lean_object*)&l_Array_lex___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_lex___auto__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_lex___auto__1___closed__7_value_aux_1),((lean_object*)&l_Array_lex___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array_lex___auto__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_lex___auto__1___closed__7_value_aux_2),((lean_object*)&l_Array_lex___auto__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Array_lex___auto__1___closed__7 = (const lean_object*)&l_Array_lex___auto__1___closed__7_value;
static const lean_string_object l_Array_lex___auto__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Array_lex___auto__1___closed__8 = (const lean_object*)&l_Array_lex___auto__1___closed__8_value;
static const lean_ctor_object l_Array_lex___auto__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_lex___auto__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Array_lex___auto__1___closed__9 = (const lean_object*)&l_Array_lex___auto__1___closed__9_value;
static const lean_string_object l_Array_lex___auto__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Array_lex___auto__1___closed__10 = (const lean_object*)&l_Array_lex___auto__1___closed__10_value;
static const lean_ctor_object l_Array_lex___auto__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_lex___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_lex___auto__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_lex___auto__1___closed__11_value_aux_0),((lean_object*)&l_Array_lex___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_lex___auto__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_lex___auto__1___closed__11_value_aux_1),((lean_object*)&l_Array_lex___auto__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Array_lex___auto__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_lex___auto__1___closed__11_value_aux_2),((lean_object*)&l_Array_lex___auto__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Array_lex___auto__1___closed__11 = (const lean_object*)&l_Array_lex___auto__1___closed__11_value;
static lean_once_cell_t l_Array_lex___auto__1___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__12;
static lean_once_cell_t l_Array_lex___auto__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__13;
static const lean_string_object l_Array_lex___auto__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Array_lex___auto__1___closed__14 = (const lean_object*)&l_Array_lex___auto__1___closed__14_value;
static const lean_string_object l_Array_lex___auto__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Array_lex___auto__1___closed__15 = (const lean_object*)&l_Array_lex___auto__1___closed__15_value;
static const lean_ctor_object l_Array_lex___auto__1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_lex___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_lex___auto__1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_lex___auto__1___closed__16_value_aux_0),((lean_object*)&l_Array_lex___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_lex___auto__1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_lex___auto__1___closed__16_value_aux_1),((lean_object*)&l_Array_lex___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Array_lex___auto__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_lex___auto__1___closed__16_value_aux_2),((lean_object*)&l_Array_lex___auto__1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Array_lex___auto__1___closed__16 = (const lean_object*)&l_Array_lex___auto__1___closed__16_value;
static const lean_string_object l_Array_lex___auto__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Array_lex___auto__1___closed__17 = (const lean_object*)&l_Array_lex___auto__1___closed__17_value;
static const lean_ctor_object l_Array_lex___auto__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_lex___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_lex___auto__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_lex___auto__1___closed__18_value_aux_0),((lean_object*)&l_Array_lex___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_lex___auto__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_lex___auto__1___closed__18_value_aux_1),((lean_object*)&l_Array_lex___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Array_lex___auto__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_lex___auto__1___closed__18_value_aux_2),((lean_object*)&l_Array_lex___auto__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Array_lex___auto__1___closed__18 = (const lean_object*)&l_Array_lex___auto__1___closed__18_value;
static const lean_string_object l_Array_lex___auto__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Array_lex___auto__1___closed__19 = (const lean_object*)&l_Array_lex___auto__1___closed__19_value;
static lean_once_cell_t l_Array_lex___auto__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__20;
static lean_once_cell_t l_Array_lex___auto__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__21;
static const lean_string_object l_Array_lex___auto__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Array_lex___auto__1___closed__22 = (const lean_object*)&l_Array_lex___auto__1___closed__22_value;
static const lean_ctor_object l_Array_lex___auto__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_lex___auto__1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Array_lex___auto__1___closed__23 = (const lean_object*)&l_Array_lex___auto__1___closed__23_value;
static const lean_string_object l_Array_lex___auto__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "[anonymous]"};
static const lean_object* l_Array_lex___auto__1___closed__24 = (const lean_object*)&l_Array_lex___auto__1___closed__24_value;
static const lean_ctor_object l_Array_lex___auto__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Array_lex___auto__1___closed__24_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(11) << 1) | 1))}};
static const lean_object* l_Array_lex___auto__1___closed__25 = (const lean_object*)&l_Array_lex___auto__1___closed__25_value;
static const lean_ctor_object l_Array_lex___auto__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)&l_Array_lex___auto__1___closed__25_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array_lex___auto__1___closed__26 = (const lean_object*)&l_Array_lex___auto__1___closed__26_value;
static lean_once_cell_t l_Array_lex___auto__1___closed__27_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__27;
static lean_once_cell_t l_Array_lex___auto__1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__28;
static lean_once_cell_t l_Array_lex___auto__1___closed__29_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__29;
static lean_once_cell_t l_Array_lex___auto__1___closed__30_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__30;
static lean_once_cell_t l_Array_lex___auto__1___closed__31_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__31;
static const lean_string_object l_Array_lex___auto__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_<_"};
static const lean_object* l_Array_lex___auto__1___closed__32 = (const lean_object*)&l_Array_lex___auto__1___closed__32_value;
static const lean_ctor_object l_Array_lex___auto__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_lex___auto__1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(192, 242, 106, 74, 199, 131, 133, 95)}};
static const lean_object* l_Array_lex___auto__1___closed__33 = (const lean_object*)&l_Array_lex___auto__1___closed__33_value;
static const lean_string_object l_Array_lex___auto__1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cdot"};
static const lean_object* l_Array_lex___auto__1___closed__34 = (const lean_object*)&l_Array_lex___auto__1___closed__34_value;
static const lean_ctor_object l_Array_lex___auto__1___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_lex___auto__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Array_lex___auto__1___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_lex___auto__1___closed__35_value_aux_0),((lean_object*)&l_Array_lex___auto__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Array_lex___auto__1___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_lex___auto__1___closed__35_value_aux_1),((lean_object*)&l_Array_lex___auto__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Array_lex___auto__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Array_lex___auto__1___closed__35_value_aux_2),((lean_object*)&l_Array_lex___auto__1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(215, 94, 65, 66, 49, 100, 151, 85)}};
static const lean_object* l_Array_lex___auto__1___closed__35 = (const lean_object*)&l_Array_lex___auto__1___closed__35_value;
static const lean_string_object l_Array_lex___auto__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "·"};
static const lean_object* l_Array_lex___auto__1___closed__36 = (const lean_object*)&l_Array_lex___auto__1___closed__36_value;
static lean_once_cell_t l_Array_lex___auto__1___closed__37_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__37;
static lean_once_cell_t l_Array_lex___auto__1___closed__38_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__38;
static lean_once_cell_t l_Array_lex___auto__1___closed__39_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__39;
static lean_once_cell_t l_Array_lex___auto__1___closed__40_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__40;
static lean_once_cell_t l_Array_lex___auto__1___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__41;
static const lean_string_object l_Array_lex___auto__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "<"};
static const lean_object* l_Array_lex___auto__1___closed__42 = (const lean_object*)&l_Array_lex___auto__1___closed__42_value;
static lean_once_cell_t l_Array_lex___auto__1___closed__43_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__43;
static lean_once_cell_t l_Array_lex___auto__1___closed__44_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__44;
static lean_once_cell_t l_Array_lex___auto__1___closed__45_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__45;
static lean_once_cell_t l_Array_lex___auto__1___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__46;
static lean_once_cell_t l_Array_lex___auto__1___closed__47_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__47;
static const lean_string_object l_Array_lex___auto__1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Array_lex___auto__1___closed__48 = (const lean_object*)&l_Array_lex___auto__1___closed__48_value;
static lean_once_cell_t l_Array_lex___auto__1___closed__49_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__49;
static lean_once_cell_t l_Array_lex___auto__1___closed__50_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__50;
static lean_once_cell_t l_Array_lex___auto__1___closed__51_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__51;
static lean_once_cell_t l_Array_lex___auto__1___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__52;
static lean_once_cell_t l_Array_lex___auto__1___closed__53_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__53;
static lean_once_cell_t l_Array_lex___auto__1___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__54;
static lean_once_cell_t l_Array_lex___auto__1___closed__55_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__55;
static lean_once_cell_t l_Array_lex___auto__1___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__56;
static lean_once_cell_t l_Array_lex___auto__1___closed__57_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__57;
static lean_once_cell_t l_Array_lex___auto__1___closed__58_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__58;
static lean_once_cell_t l_Array_lex___auto__1___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Array_lex___auto__1___closed__59;
LEAN_EXPORT lean_object* l_Array_lex___auto__1;
LEAN_EXPORT lean_object* l_Array_lex___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_lex___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Array_lex___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Array_lex___redArg___closed__0 = (const lean_object*)&l_Array_lex___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_Array_lex___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_lex___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_lex(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_lex___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Array_lex___auto__1___closed__12(void){
_start:
{
lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_27_ = ((lean_object*)(l_Array_lex___auto__1___closed__10));
v___x_28_ = l_Lean_mkAtom(v___x_27_);
return v___x_28_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__13(void){
_start:
{
lean_object* v___x_29_; lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_29_ = lean_obj_once(&l_Array_lex___auto__1___closed__12, &l_Array_lex___auto__1___closed__12_once, _init_l_Array_lex___auto__1___closed__12);
v___x_30_ = ((lean_object*)(l_Array_lex___auto__1___closed__5));
v___x_31_ = lean_array_push(v___x_30_, v___x_29_);
return v___x_31_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__20(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = ((lean_object*)(l_Array_lex___auto__1___closed__19));
v___x_47_ = l_Lean_mkAtom(v___x_46_);
return v___x_47_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__21(void){
_start:
{
lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; 
v___x_48_ = lean_obj_once(&l_Array_lex___auto__1___closed__20, &l_Array_lex___auto__1___closed__20_once, _init_l_Array_lex___auto__1___closed__20);
v___x_49_ = ((lean_object*)(l_Array_lex___auto__1___closed__5));
v___x_50_ = lean_array_push(v___x_49_, v___x_48_);
return v___x_50_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__27(void){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = ((lean_object*)(l_Array_lex___auto__1___closed__26));
v___x_65_ = ((lean_object*)(l_Array_lex___auto__1___closed__5));
v___x_66_ = lean_array_push(v___x_65_, v___x_64_);
return v___x_66_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__28(void){
_start:
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_67_ = lean_obj_once(&l_Array_lex___auto__1___closed__27, &l_Array_lex___auto__1___closed__27_once, _init_l_Array_lex___auto__1___closed__27);
v___x_68_ = ((lean_object*)(l_Array_lex___auto__1___closed__23));
v___x_69_ = lean_box(2);
v___x_70_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_70_, 0, v___x_69_);
lean_ctor_set(v___x_70_, 1, v___x_68_);
lean_ctor_set(v___x_70_, 2, v___x_67_);
return v___x_70_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__29(void){
_start:
{
lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_71_ = lean_obj_once(&l_Array_lex___auto__1___closed__28, &l_Array_lex___auto__1___closed__28_once, _init_l_Array_lex___auto__1___closed__28);
v___x_72_ = lean_obj_once(&l_Array_lex___auto__1___closed__21, &l_Array_lex___auto__1___closed__21_once, _init_l_Array_lex___auto__1___closed__21);
v___x_73_ = lean_array_push(v___x_72_, v___x_71_);
return v___x_73_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__30(void){
_start:
{
lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; 
v___x_74_ = lean_obj_once(&l_Array_lex___auto__1___closed__29, &l_Array_lex___auto__1___closed__29_once, _init_l_Array_lex___auto__1___closed__29);
v___x_75_ = ((lean_object*)(l_Array_lex___auto__1___closed__18));
v___x_76_ = lean_box(2);
v___x_77_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v___x_75_);
lean_ctor_set(v___x_77_, 2, v___x_74_);
return v___x_77_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__31(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_78_ = lean_obj_once(&l_Array_lex___auto__1___closed__30, &l_Array_lex___auto__1___closed__30_once, _init_l_Array_lex___auto__1___closed__30);
v___x_79_ = ((lean_object*)(l_Array_lex___auto__1___closed__5));
v___x_80_ = lean_array_push(v___x_79_, v___x_78_);
return v___x_80_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__37(void){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; 
v___x_91_ = ((lean_object*)(l_Array_lex___auto__1___closed__36));
v___x_92_ = l_Lean_mkAtom(v___x_91_);
return v___x_92_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__38(void){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; 
v___x_93_ = lean_obj_once(&l_Array_lex___auto__1___closed__37, &l_Array_lex___auto__1___closed__37_once, _init_l_Array_lex___auto__1___closed__37);
v___x_94_ = ((lean_object*)(l_Array_lex___auto__1___closed__5));
v___x_95_ = lean_array_push(v___x_94_, v___x_93_);
return v___x_95_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__39(void){
_start:
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; 
v___x_96_ = lean_obj_once(&l_Array_lex___auto__1___closed__28, &l_Array_lex___auto__1___closed__28_once, _init_l_Array_lex___auto__1___closed__28);
v___x_97_ = lean_obj_once(&l_Array_lex___auto__1___closed__38, &l_Array_lex___auto__1___closed__38_once, _init_l_Array_lex___auto__1___closed__38);
v___x_98_ = lean_array_push(v___x_97_, v___x_96_);
return v___x_98_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__40(void){
_start:
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v___x_99_ = lean_obj_once(&l_Array_lex___auto__1___closed__39, &l_Array_lex___auto__1___closed__39_once, _init_l_Array_lex___auto__1___closed__39);
v___x_100_ = ((lean_object*)(l_Array_lex___auto__1___closed__35));
v___x_101_ = lean_box(2);
v___x_102_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set(v___x_102_, 1, v___x_100_);
lean_ctor_set(v___x_102_, 2, v___x_99_);
return v___x_102_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__41(void){
_start:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_105_; 
v___x_103_ = lean_obj_once(&l_Array_lex___auto__1___closed__40, &l_Array_lex___auto__1___closed__40_once, _init_l_Array_lex___auto__1___closed__40);
v___x_104_ = ((lean_object*)(l_Array_lex___auto__1___closed__5));
v___x_105_ = lean_array_push(v___x_104_, v___x_103_);
return v___x_105_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__43(void){
_start:
{
lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_107_ = ((lean_object*)(l_Array_lex___auto__1___closed__42));
v___x_108_ = l_Lean_mkAtom(v___x_107_);
return v___x_108_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__44(void){
_start:
{
lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; 
v___x_109_ = lean_obj_once(&l_Array_lex___auto__1___closed__43, &l_Array_lex___auto__1___closed__43_once, _init_l_Array_lex___auto__1___closed__43);
v___x_110_ = lean_obj_once(&l_Array_lex___auto__1___closed__41, &l_Array_lex___auto__1___closed__41_once, _init_l_Array_lex___auto__1___closed__41);
v___x_111_ = lean_array_push(v___x_110_, v___x_109_);
return v___x_111_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__45(void){
_start:
{
lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; 
v___x_112_ = lean_obj_once(&l_Array_lex___auto__1___closed__40, &l_Array_lex___auto__1___closed__40_once, _init_l_Array_lex___auto__1___closed__40);
v___x_113_ = lean_obj_once(&l_Array_lex___auto__1___closed__44, &l_Array_lex___auto__1___closed__44_once, _init_l_Array_lex___auto__1___closed__44);
v___x_114_ = lean_array_push(v___x_113_, v___x_112_);
return v___x_114_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__46(void){
_start:
{
lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_115_ = lean_obj_once(&l_Array_lex___auto__1___closed__45, &l_Array_lex___auto__1___closed__45_once, _init_l_Array_lex___auto__1___closed__45);
v___x_116_ = ((lean_object*)(l_Array_lex___auto__1___closed__33));
v___x_117_ = lean_box(2);
v___x_118_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_118_, 0, v___x_117_);
lean_ctor_set(v___x_118_, 1, v___x_116_);
lean_ctor_set(v___x_118_, 2, v___x_115_);
return v___x_118_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__47(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; 
v___x_119_ = lean_obj_once(&l_Array_lex___auto__1___closed__46, &l_Array_lex___auto__1___closed__46_once, _init_l_Array_lex___auto__1___closed__46);
v___x_120_ = lean_obj_once(&l_Array_lex___auto__1___closed__31, &l_Array_lex___auto__1___closed__31_once, _init_l_Array_lex___auto__1___closed__31);
v___x_121_ = lean_array_push(v___x_120_, v___x_119_);
return v___x_121_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__49(void){
_start:
{
lean_object* v___x_123_; lean_object* v___x_124_; 
v___x_123_ = ((lean_object*)(l_Array_lex___auto__1___closed__48));
v___x_124_ = l_Lean_mkAtom(v___x_123_);
return v___x_124_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__50(void){
_start:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_127_; 
v___x_125_ = lean_obj_once(&l_Array_lex___auto__1___closed__49, &l_Array_lex___auto__1___closed__49_once, _init_l_Array_lex___auto__1___closed__49);
v___x_126_ = lean_obj_once(&l_Array_lex___auto__1___closed__47, &l_Array_lex___auto__1___closed__47_once, _init_l_Array_lex___auto__1___closed__47);
v___x_127_ = lean_array_push(v___x_126_, v___x_125_);
return v___x_127_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__51(void){
_start:
{
lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; 
v___x_128_ = lean_obj_once(&l_Array_lex___auto__1___closed__50, &l_Array_lex___auto__1___closed__50_once, _init_l_Array_lex___auto__1___closed__50);
v___x_129_ = ((lean_object*)(l_Array_lex___auto__1___closed__16));
v___x_130_ = lean_box(2);
v___x_131_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_131_, 0, v___x_130_);
lean_ctor_set(v___x_131_, 1, v___x_129_);
lean_ctor_set(v___x_131_, 2, v___x_128_);
return v___x_131_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__52(void){
_start:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_132_ = lean_obj_once(&l_Array_lex___auto__1___closed__51, &l_Array_lex___auto__1___closed__51_once, _init_l_Array_lex___auto__1___closed__51);
v___x_133_ = lean_obj_once(&l_Array_lex___auto__1___closed__13, &l_Array_lex___auto__1___closed__13_once, _init_l_Array_lex___auto__1___closed__13);
v___x_134_ = lean_array_push(v___x_133_, v___x_132_);
return v___x_134_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__53(void){
_start:
{
lean_object* v___x_135_; lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_135_ = lean_obj_once(&l_Array_lex___auto__1___closed__52, &l_Array_lex___auto__1___closed__52_once, _init_l_Array_lex___auto__1___closed__52);
v___x_136_ = ((lean_object*)(l_Array_lex___auto__1___closed__11));
v___x_137_ = lean_box(2);
v___x_138_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_138_, 0, v___x_137_);
lean_ctor_set(v___x_138_, 1, v___x_136_);
lean_ctor_set(v___x_138_, 2, v___x_135_);
return v___x_138_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__54(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = lean_obj_once(&l_Array_lex___auto__1___closed__53, &l_Array_lex___auto__1___closed__53_once, _init_l_Array_lex___auto__1___closed__53);
v___x_140_ = ((lean_object*)(l_Array_lex___auto__1___closed__5));
v___x_141_ = lean_array_push(v___x_140_, v___x_139_);
return v___x_141_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__55(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_142_ = lean_obj_once(&l_Array_lex___auto__1___closed__54, &l_Array_lex___auto__1___closed__54_once, _init_l_Array_lex___auto__1___closed__54);
v___x_143_ = ((lean_object*)(l_Array_lex___auto__1___closed__9));
v___x_144_ = lean_box(2);
v___x_145_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v___x_143_);
lean_ctor_set(v___x_145_, 2, v___x_142_);
return v___x_145_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__56(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_146_ = lean_obj_once(&l_Array_lex___auto__1___closed__55, &l_Array_lex___auto__1___closed__55_once, _init_l_Array_lex___auto__1___closed__55);
v___x_147_ = ((lean_object*)(l_Array_lex___auto__1___closed__5));
v___x_148_ = lean_array_push(v___x_147_, v___x_146_);
return v___x_148_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__57(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_149_ = lean_obj_once(&l_Array_lex___auto__1___closed__56, &l_Array_lex___auto__1___closed__56_once, _init_l_Array_lex___auto__1___closed__56);
v___x_150_ = ((lean_object*)(l_Array_lex___auto__1___closed__7));
v___x_151_ = lean_box(2);
v___x_152_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_152_, 0, v___x_151_);
lean_ctor_set(v___x_152_, 1, v___x_150_);
lean_ctor_set(v___x_152_, 2, v___x_149_);
return v___x_152_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__58(void){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_153_ = lean_obj_once(&l_Array_lex___auto__1___closed__57, &l_Array_lex___auto__1___closed__57_once, _init_l_Array_lex___auto__1___closed__57);
v___x_154_ = ((lean_object*)(l_Array_lex___auto__1___closed__5));
v___x_155_ = lean_array_push(v___x_154_, v___x_153_);
return v___x_155_;
}
}
static lean_object* _init_l_Array_lex___auto__1___closed__59(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_156_ = lean_obj_once(&l_Array_lex___auto__1___closed__58, &l_Array_lex___auto__1___closed__58_once, _init_l_Array_lex___auto__1___closed__58);
v___x_157_ = ((lean_object*)(l_Array_lex___auto__1___closed__4));
v___x_158_ = lean_box(2);
v___x_159_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
lean_ctor_set(v___x_159_, 1, v___x_157_);
lean_ctor_set(v___x_159_, 2, v___x_156_);
return v___x_159_;
}
}
static lean_object* _init_l_Array_lex___auto__1(void){
_start:
{
lean_object* v___x_160_; 
v___x_160_ = lean_obj_once(&l_Array_lex___auto__1___closed__59, &l_Array_lex___auto__1___closed__59_once, _init_l_Array_lex___auto__1___closed__59);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Array_lex___redArg___lam__0(lean_object* v___y_161_, lean_object* v_as_162_, lean_object* v_bs_163_, lean_object* v_lt_164_, lean_object* v_inst_165_, lean_object* v___x_166_, lean_object* v___x_167_, lean_object* v_next_168_, lean_object* v_acc_169_, lean_object* v_h_170_, lean_object* v_G_171_){
_start:
{
uint8_t v___x_172_; 
v___x_172_ = lean_nat_dec_lt(v_next_168_, v___y_161_);
if (v___x_172_ == 0)
{
lean_dec_ref(v_G_171_);
lean_dec_ref(v___x_167_);
lean_dec_ref(v_inst_165_);
lean_dec_ref(v_lt_164_);
lean_inc_ref(v_acc_169_);
return v_acc_169_;
}
else
{
lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; uint8_t v___x_176_; 
v___x_173_ = lean_array_fget_borrowed(v_as_162_, v_next_168_);
v___x_174_ = lean_array_fget_borrowed(v_bs_163_, v_next_168_);
lean_inc(v___x_174_);
lean_inc(v___x_173_);
v___x_175_ = lean_apply_2(v_lt_164_, v___x_173_, v___x_174_);
v___x_176_ = lean_unbox(v___x_175_);
if (v___x_176_ == 0)
{
lean_object* v___x_177_; uint8_t v___x_178_; 
lean_inc(v___x_174_);
lean_inc(v___x_173_);
v___x_177_ = lean_apply_2(v_inst_165_, v___x_173_, v___x_174_);
v___x_178_ = lean_unbox(v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec_ref(v_G_171_);
lean_dec_ref(v___x_167_);
v___x_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_179_, 0, v___x_175_);
v___x_180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v___x_166_);
return v___x_180_;
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_181_ = lean_unsigned_to_nat(1u);
v___x_182_ = lean_nat_add(v_next_168_, v___x_181_);
v___x_183_ = lean_apply_4(v_G_171_, v___x_182_, v___x_167_, lean_box(0), lean_box(0));
return v___x_183_;
}
}
else
{
lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec_ref(v_G_171_);
lean_dec_ref(v___x_167_);
lean_dec_ref(v_inst_165_);
v___x_184_ = lean_box(v___x_172_);
v___x_185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_185_, 0, v___x_184_);
v___x_186_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v___x_166_);
return v___x_186_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_lex___redArg___lam__0___boxed(lean_object* v___y_187_, lean_object* v_as_188_, lean_object* v_bs_189_, lean_object* v_lt_190_, lean_object* v_inst_191_, lean_object* v___x_192_, lean_object* v___x_193_, lean_object* v_next_194_, lean_object* v_acc_195_, lean_object* v_h_196_, lean_object* v_G_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l_Array_lex___redArg___lam__0(v___y_187_, v_as_188_, v_bs_189_, v_lt_190_, v_inst_191_, v___x_192_, v___x_193_, v_next_194_, v_acc_195_, v_h_196_, v_G_197_);
lean_dec_ref(v_acc_195_);
lean_dec(v_next_194_);
lean_dec_ref(v_bs_189_);
lean_dec_ref(v_as_188_);
lean_dec(v___y_187_);
return v_res_198_;
}
}
uint8_t l_Array_lex___redArg(lean_object* v_inst_202_, lean_object* v_as_203_, lean_object* v_bs_204_, lean_object* v_lt_205_){
_start:
{
lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___y_210_; uint8_t v___x_219_; 
v___x_206_ = lean_unsigned_to_nat(0u);
v___x_207_ = lean_array_get_size(v_as_203_);
v___x_208_ = lean_array_get_size(v_bs_204_);
v___x_219_ = lean_nat_dec_le(v___x_207_, v___x_208_);
if (v___x_219_ == 0)
{
v___y_210_ = v___x_208_;
goto v___jp_209_;
}
else
{
v___y_210_ = v___x_207_;
goto v___jp_209_;
}
v___jp_209_:
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___f_213_; lean_object* v___x_214_; lean_object* v_fst_215_; 
v___x_211_ = lean_box(0);
v___x_212_ = ((lean_object*)(l_Array_lex___redArg___closed__0));
v___f_213_ = lean_alloc_closure((void*)(l_Array_lex___redArg___lam__0___boxed), 11, 7);
lean_closure_set(v___f_213_, 0, v___y_210_);
lean_closure_set(v___f_213_, 1, v_as_203_);
lean_closure_set(v___f_213_, 2, v_bs_204_);
lean_closure_set(v___f_213_, 3, v_lt_205_);
lean_closure_set(v___f_213_, 4, v_inst_202_);
lean_closure_set(v___f_213_, 5, v___x_211_);
lean_closure_set(v___f_213_, 6, v___x_212_);
v___x_214_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_213_, v___x_206_, v___x_212_, lean_box(0));
v_fst_215_ = lean_ctor_get(v___x_214_, 0);
lean_inc(v_fst_215_);
lean_dec(v___x_214_);
if (lean_obj_tag(v_fst_215_) == 0)
{
uint8_t v___x_216_; 
v___x_216_ = lean_nat_dec_lt(v___x_207_, v___x_208_);
return v___x_216_;
}
else
{
lean_object* v_val_217_; uint8_t v___x_218_; 
v_val_217_ = lean_ctor_get(v_fst_215_, 0);
lean_inc(v_val_217_);
lean_dec_ref_known(v_fst_215_, 1);
v___x_218_ = lean_unbox(v_val_217_);
lean_dec(v_val_217_);
return v___x_218_;
}
}
}
}
LEAN_EXPORT void l_Array_lex___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_202_ = stack[0].m_obj;
lean_object* v_as_203_ = stack[1].m_obj;
lean_object* v_bs_204_ = stack[2].m_obj;
lean_object* v_lt_205_ = stack[3].m_obj;
uint8_t v_res_220_;
v_res_220_ = l_Array_lex___redArg(v_inst_202_, v_as_203_, v_bs_204_, v_lt_205_);
stack->m_num = v_res_220_;
}
LEAN_EXPORT lean_object* l_Array_lex___redArg___boxed(lean_object* v_inst_221_, lean_object* v_as_222_, lean_object* v_bs_223_, lean_object* v_lt_224_){
_start:
{
uint8_t v_res_225_; lean_object* v_r_226_; 
v_res_225_ = l_Array_lex___redArg(v_inst_221_, v_as_222_, v_bs_223_, v_lt_224_);
v_r_226_ = lean_box(v_res_225_);
return v_r_226_;
}
}
uint8_t l_Array_lex(lean_object* v_00_u03b1_227_, lean_object* v_inst_228_, lean_object* v_as_229_, lean_object* v_bs_230_, lean_object* v_lt_231_){
_start:
{
uint8_t v___x_232_; 
v___x_232_ = l_Array_lex___redArg(v_inst_228_, v_as_229_, v_bs_230_, v_lt_231_);
return v___x_232_;
}
}
LEAN_EXPORT void l_Array_lex_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_228_ = stack[1].m_obj;
lean_object* v_as_229_ = stack[2].m_obj;
lean_object* v_bs_230_ = stack[3].m_obj;
lean_object* v_lt_231_ = stack[4].m_obj;
uint8_t v_res_233_;
v_res_233_ = l_Array_lex(lean_box(0), v_inst_228_, v_as_229_, v_bs_230_, v_lt_231_);
stack->m_num = v_res_233_;
}
LEAN_EXPORT lean_object* l_Array_lex___boxed(lean_object* v_00_u03b1_234_, lean_object* v_inst_235_, lean_object* v_as_236_, lean_object* v_bs_237_, lean_object* v_lt_238_){
_start:
{
uint8_t v_res_239_; lean_object* v_r_240_; 
v_res_239_ = l_Array_lex(v_00_u03b1_234_, v_inst_235_, v_as_236_, v_bs_237_, v_lt_238_);
v_r_240_ = lean_box(v_res_239_);
return v_r_240_;
}
}
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Array_Lex_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Array_Lex_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
l_Array_lex___auto__1 = _init_l_Array_lex___auto__1();
lean_mark_persistent(l_Array_lex___auto__1);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Array_Lex_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Lex_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Array_Lex_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Array_Lex_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
