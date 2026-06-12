// Lean compiler output
// Module: Lean.DocString.Syntax
// Imports: public import Lean.Parser.Term.Basic public meta import Lean.Parser.Term.Basic
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_pushNone;
lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColEq(lean_object*);
lean_object* l_Lean_Parser_symbol(lean_object*);
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_Term_structInstField;
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColGe(lean_object*);
lean_object* l_Lean_Parser_sepBy(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_withPosition(lean_object*);
lean_object* l_Lean_Parser_Term_structInstFields(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByIndent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_structInstFields_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_structInstField_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByIndent_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_structInstFields_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_arg__val_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__val_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__val_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__2_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__val_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "quot"};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__4_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__4_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__4_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(145, 163, 173, 41, 168, 168, 65, 81)}};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__4_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__val_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "arg_val"};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__5_value),LEAN_SCALAR_PTR_LITERAL(199, 154, 240, 169, 25, 100, 158, 173)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__6_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(21, 43, 204, 27, 49, 138, 49, 195)}};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__6_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__val_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__7_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__val_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "`(arg_val| "};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__9_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__9_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__10 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__10_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__5_value),LEAN_SCALAR_PTR_LITERAL(199, 154, 240, 169, 25, 100, 158, 173)}};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__11 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__11_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__12 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__12_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__val_quot___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__13 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__13_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__13_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__14 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__12_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__15 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__15_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__10_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__15_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__16 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__16_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__6_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__16_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__17 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__17_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__val_quot___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__17_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__val_quot___closed__18 = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__18_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_arg__val_quot = (const lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__18_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_arg__val;
static const lean_string_object l_Lean_Doc_Syntax_arg__str___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l_Lean_Doc_Syntax_arg__str___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__str___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Syntax"};
static const lean_object* l_Lean_Doc_Syntax_arg__str___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__str___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "arg_str"};
static const lean_object* l_Lean_Doc_Syntax_arg__str___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__str___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__str___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__str___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__str___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__2_value),LEAN_SCALAR_PTR_LITERAL(28, 110, 66, 227, 168, 59, 232, 226)}};
static const lean_object* l_Lean_Doc_Syntax_arg__str___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__3_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__str___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Doc_Syntax_arg__str___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__str___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__4_value),LEAN_SCALAR_PTR_LITERAL(255, 188, 142, 1, 190, 33, 34, 128)}};
static const lean_object* l_Lean_Doc_Syntax_arg__str___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__str___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__str___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__str___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__3_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__str___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_arg__str = (const lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__7_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__ident___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "arg_ident"};
static const lean_object* l_Lean_Doc_Syntax_arg__ident___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__ident___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__ident___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__ident___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__ident___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__0_value),LEAN_SCALAR_PTR_LITERAL(73, 49, 249, 222, 84, 35, 6, 34)}};
static const lean_object* l_Lean_Doc_Syntax_arg__ident___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__ident___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Doc_Syntax_arg__ident___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__ident___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__2_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Doc_Syntax_arg__ident___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__ident___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__3_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__ident___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__ident___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__ident___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_arg__ident = (const lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__5_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__num___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "arg_num"};
static const lean_object* l_Lean_Doc_Syntax_arg__num___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__num___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__num___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__num___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_arg__num___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__0_value),LEAN_SCALAR_PTR_LITERAL(14, 247, 226, 130, 46, 200, 13, 201)}};
static const lean_object* l_Lean_Doc_Syntax_arg__num___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_arg__num___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Doc_Syntax_arg__num___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__num___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__2_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l_Lean_Doc_Syntax_arg__num___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__num___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__3_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__num___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_arg__num___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_arg__num___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_arg__num = (const lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__5_value;
static const lean_string_object l_Lean_Doc_Syntax_doc__arg_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doc_arg"};
static const lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_doc__arg_quot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 168, 26, 226, 195, 1, 139, 142)}};
static const lean_ctor_object l_Lean_Doc_Syntax_doc__arg_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(221, 5, 8, 15, 213, 144, 60, 97)}};
static const lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_doc__arg_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "`(doc_arg| "};
static const lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_doc__arg_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_doc__arg_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 168, 26, 226, 195, 1, 139, 142)}};
static const lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_doc__arg_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_doc__arg_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_doc__arg_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_doc__arg_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_doc__arg_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_doc__arg_quot___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_doc__arg_quot = (const lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_doc__arg;
static const lean_string_object l_Lean_Doc_Syntax_anon___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "anon"};
static const lean_object* l_Lean_Doc_Syntax_anon___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_anon___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_anon___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_anon___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_anon___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_anon___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_anon___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_anon___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_anon___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_anon___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 30, 185, 65, 40, 8, 94, 56)}};
static const lean_object* l_Lean_Doc_Syntax_anon___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_anon___closed__1_value;
static const lean_ctor_object l_Lean_Doc_Syntax_anon___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_anon___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__12_value)}};
static const lean_object* l_Lean_Doc_Syntax_anon___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_anon___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_anon = (const lean_object*)&l_Lean_Doc_Syntax_anon___closed__2_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "Anonymous positional argument "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_named___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "named"};
static const lean_object* l_Lean_Doc_Syntax_named___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_named___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_named___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_named___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_named___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_named___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_named___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_named___closed__0_value),LEAN_SCALAR_PTR_LITERAL(240, 209, 4, 173, 176, 102, 100, 110)}};
static const lean_object* l_Lean_Doc_Syntax_named___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_named___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Doc_Syntax_named___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_named___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_named___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_named___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_named___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__4_value;
static const lean_string_object l_Lean_Doc_Syntax_named___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Doc_Syntax_named___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_named___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_named___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_named___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_named___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_named___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_named___closed__7_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__12_value)}};
static const lean_object* l_Lean_Doc_Syntax_named___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_named___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_named___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__9_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_named___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_named___closed__9_value)}};
static const lean_object* l_Lean_Doc_Syntax_named___closed__10 = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__10_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_named = (const lean_object*)&l_Lean_Doc_Syntax_named___closed__10_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Named argument "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_named__no__paren___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "named_no_paren"};
static const lean_object* l_Lean_Doc_Syntax_named__no__paren___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named__no__paren___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_named__no__paren___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_named__no__paren___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_named__no__paren___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 78, 240, 214, 103, 62, 217, 25)}};
static const lean_object* l_Lean_Doc_Syntax_named__no__paren___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__1_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named__no__paren___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_named___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_named__no__paren___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named__no__paren___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__2_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__12_value)}};
static const lean_object* l_Lean_Doc_Syntax_named__no__paren___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_named__no__paren___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__3_value)}};
static const lean_object* l_Lean_Doc_Syntax_named__no__paren___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_named__no__paren = (const lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named__no__paren___regBuiltin_Lean_Doc_Syntax_named__no__paren_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named__no__paren___regBuiltin_Lean_Doc_Syntax_named__no__paren_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_flag__on___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "flag_on"};
static const lean_object* l_Lean_Doc_Syntax_flag__on___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_flag__on___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_flag__on___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_flag__on___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_flag__on___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 222, 140, 123, 199, 224, 2, 54)}};
static const lean_object* l_Lean_Doc_Syntax_flag__on___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_flag__on___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l_Lean_Doc_Syntax_flag__on___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_flag__on___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_flag__on___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_flag__on___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_flag__on___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_flag__on___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_flag__on___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_flag__on = (const lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__5_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Boolean flag, turned on "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_flag__off___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "flag_off"};
static const lean_object* l_Lean_Doc_Syntax_flag__off___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_flag__off___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_flag__off___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_flag__off___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_flag__off___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 0, 37, 229, 12, 38, 20, 228)}};
static const lean_object* l_Lean_Doc_Syntax_flag__off___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_flag__off___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_Doc_Syntax_flag__off___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_flag__off___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_flag__off___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_flag__off___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_flag__off___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_flag__off___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_flag__off___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_flag__off = (const lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__5_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Boolean flag, turned off "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_link__target_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "link_target"};
static const lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__target_quot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(73, 92, 160, 204, 226, 167, 176, 87)}};
static const lean_ctor_object l_Lean_Doc_Syntax_link__target_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(187, 144, 133, 12, 143, 217, 129, 236)}};
static const lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_link__target_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "`(link_target| "};
static const lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__target_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__target_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(73, 92, 160, 204, 226, 167, 176, 87)}};
static const lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__target_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__target_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__target_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__target_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__target_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_link__target_quot___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_link__target_quot = (const lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_link__target;
static const lean_string_object l_Lean_Doc_Syntax_url___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "url"};
static const lean_object* l_Lean_Doc_Syntax_url___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_url___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_url___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_url___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_url___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_url___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_url___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_url___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_url___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_url___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 109, 202, 165, 136, 148, 125, 206)}};
static const lean_object* l_Lean_Doc_Syntax_url___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_url___closed__1_value;
static const lean_ctor_object l_Lean_Doc_Syntax_url___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_named___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_url___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_url___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_url___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_url___closed__2_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_url___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_url___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_url___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_url___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_url___closed__3_value)}};
static const lean_object* l_Lean_Doc_Syntax_url___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_url___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_url = (const lean_object*)&l_Lean_Doc_Syntax_url___closed__4_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 75, .m_capacity = 75, .m_length = 74, .m_data = "A URL target, written explicitly. Use square brackets for a named target. "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_ref___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ref"};
static const lean_object* l_Lean_Doc_Syntax_ref___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_ref___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ref___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_ref___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ref___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_ref___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ref___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_ref___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ref___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__0_value),LEAN_SCALAR_PTR_LITERAL(157, 197, 143, 220, 44, 158, 31, 133)}};
static const lean_object* l_Lean_Doc_Syntax_ref___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_ref___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_ref___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Doc_Syntax_ref___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_ref___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ref___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ref___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_ref___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_ref___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ref___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_ref___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_ref___closed__4_value;
static const lean_string_object l_Lean_Doc_Syntax_ref___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Doc_Syntax_ref___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_ref___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ref___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ref___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_ref___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_ref___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ref___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_ref___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_ref___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ref___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ref___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_ref___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_ref___closed__8_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_ref = (const lean_object*)&l_Lean_Doc_Syntax_ref___closed__8_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "A named reference to a URL defined elsewhere. Use parentheses to write the URL here. "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_inline_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "inline"};
static const lean_object* l_Lean_Doc_Syntax_inline_quot___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline_quot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 198, 166, 26, 13, 231, 61, 113)}};
static const lean_ctor_object l_Lean_Doc_Syntax_inline_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(34, 76, 196, 93, 152, 249, 46, 126)}};
static const lean_object* l_Lean_Doc_Syntax_inline_quot___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_inline_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "`(inline| "};
static const lean_object* l_Lean_Doc_Syntax_inline_quot___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_inline_quot___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(92, 198, 166, 26, 13, 231, 61, 113)}};
static const lean_object* l_Lean_Doc_Syntax_inline_quot___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Doc_Syntax_inline_quot___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_inline_quot___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_inline_quot___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_inline_quot___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_inline_quot___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_inline_quot = (const lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_inline;
static const lean_string_object l_Lean_Doc_Syntax_text___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l_Lean_Doc_Syntax_text___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_text___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_text___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_text___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_text___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_text___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_text___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_text___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_text___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_text___closed__0_value),LEAN_SCALAR_PTR_LITERAL(252, 149, 124, 218, 116, 154, 240, 105)}};
static const lean_object* l_Lean_Doc_Syntax_text___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_text___closed__1_value;
static const lean_ctor_object l_Lean_Doc_Syntax_text___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_text___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_text___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_text___closed__2_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_text = (const lean_object*)&l_Lean_Doc_Syntax_text___closed__2_value;
static const lean_string_object l_Lean_Doc_Syntax_emph___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "emph"};
static const lean_object* l_Lean_Doc_Syntax_emph___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_emph___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_emph___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_emph___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_emph___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_emph___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_emph___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_emph___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_emph___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 183, 215, 94, 0, 242, 191, 239)}};
static const lean_object* l_Lean_Doc_Syntax_emph___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_emph___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_emph___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "_["};
static const lean_object* l_Lean_Doc_Syntax_emph___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_emph___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_emph___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_emph___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_emph___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_emph___closed__3_value;
static const lean_string_object l_Lean_Doc_Syntax_emph___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "many"};
static const lean_object* l_Lean_Doc_Syntax_emph___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_emph___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_emph___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__4_value),LEAN_SCALAR_PTR_LITERAL(41, 35, 40, 86, 189, 97, 244, 31)}};
static const lean_object* l_Lean_Doc_Syntax_emph___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_emph___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_emph___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_emph___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_emph___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_emph___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_emph___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_emph___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_emph___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_emph___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__7_value),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_emph___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_emph___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_emph___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_emph___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_emph___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_emph___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_emph = (const lean_object*)&l_Lean_Doc_Syntax_emph___closed__9_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 330, .m_capacity = 330, .m_length = 328, .m_data = "Emphasis, often rendered as italics.\n\nEmphasis may be nested by using longer sequences of `_` for the outer delimiters. For example:\n```\nRemember: __always butter the _rugbrød_ before adding toppings!__\n```\nHere, the outer `__` is used to emphasize the instructions, while the inner `_` indicates the use of\na non-English word.\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_bold___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bold"};
static const lean_object* l_Lean_Doc_Syntax_bold___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_bold___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_bold___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_bold___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_bold___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_bold___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_bold___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_bold___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_bold___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_bold___closed__0_value),LEAN_SCALAR_PTR_LITERAL(217, 240, 207, 144, 35, 3, 119, 11)}};
static const lean_object* l_Lean_Doc_Syntax_bold___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_bold___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_bold___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "*["};
static const lean_object* l_Lean_Doc_Syntax_bold___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_bold___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_bold___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_bold___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_bold___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_bold___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_bold___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_bold___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_bold___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_bold___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_bold___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_bold___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_bold___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_bold___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_bold___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_bold___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_bold___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_bold___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_bold___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_bold = (const lean_object*)&l_Lean_Doc_Syntax_bold___closed__6_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 166, .m_capacity = 166, .m_length = 165, .m_data = "Bold emphasis.\n\nA single `*` suffices to make text bold. Using `_` for emphasis.\n\nBold text may be nested by using longer sequences of `*` for the outer delimiters.\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_link___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "link"};
static const lean_object* l_Lean_Doc_Syntax_link___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_link___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_link___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_link___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_link___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_link___closed__0_value),LEAN_SCALAR_PTR_LITERAL(129, 184, 35, 28, 112, 167, 76, 80)}};
static const lean_object* l_Lean_Doc_Syntax_link___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_link___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_link___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "link["};
static const lean_object* l_Lean_Doc_Syntax_link___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_link___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_link___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_link___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_link___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_link___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_link___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_link___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_link___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_link___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_link___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_link___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_link___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_link___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_link___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_link___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_link = (const lean_object*)&l_Lean_Doc_Syntax_link___closed__7_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 126, .m_capacity = 126, .m_length = 125, .m_data = "A link. The link's target may either be a concrete URL (written in parentheses) or a named URL\n(written in square brackets).\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_image___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "image"};
static const lean_object* l_Lean_Doc_Syntax_image___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_image___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_image___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_image___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_image___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_image___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_image___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_image___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_image___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_image___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 113, 65, 80, 13, 110, 129, 61)}};
static const lean_object* l_Lean_Doc_Syntax_image___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_image___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_image___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "image("};
static const lean_object* l_Lean_Doc_Syntax_image___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_image___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_image___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_image___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_image___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_image___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_image___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_image___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_image___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_image___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_image___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_image___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_image___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_image___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_image___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_image___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_link__target_quot___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_image___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_image___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_image___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_image___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_image___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_image___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_image___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_image = (const lean_object*)&l_Lean_Doc_Syntax_image___closed__7_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 221, .m_capacity = 221, .m_length = 220, .m_data = "An image, with alternate text and a URL.\n\nThe alternate text is a plain string, rather than Verso markup.\n\nThe image URL may either be a concrete URL (written in parentheses) or a named URL (written in\nsquare brackets).\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_footnote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "footnote"};
static const lean_object* l_Lean_Doc_Syntax_footnote___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_footnote___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_footnote___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_footnote___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_footnote___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_footnote___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_footnote___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_footnote___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_footnote___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_footnote___closed__0_value),LEAN_SCALAR_PTR_LITERAL(207, 87, 199, 0, 139, 133, 244, 123)}};
static const lean_object* l_Lean_Doc_Syntax_footnote___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_footnote___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_footnote___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "footnote("};
static const lean_object* l_Lean_Doc_Syntax_footnote___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_footnote___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_footnote___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_footnote___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_footnote___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_footnote___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_footnote___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_footnote___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_footnote___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_footnote___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_footnote___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_footnote___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_footnote___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_footnote___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_footnote___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_footnote___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_footnote___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_footnote___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_footnote___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_footnote = (const lean_object*)&l_Lean_Doc_Syntax_footnote___closed__6_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 93, .m_capacity = 93, .m_length = 92, .m_data = "A footnote use site.\n\nFootnotes must be defined elsewhere using the `[^NAME]: TEXT` syntax.\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_linebreak___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "linebreak"};
static const lean_object* l_Lean_Doc_Syntax_linebreak___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_linebreak___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_linebreak___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_linebreak___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_linebreak___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__0_value),LEAN_SCALAR_PTR_LITERAL(204, 183, 85, 224, 226, 177, 67, 207)}};
static const lean_object* l_Lean_Doc_Syntax_linebreak___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_linebreak___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "line!"};
static const lean_object* l_Lean_Doc_Syntax_linebreak___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_linebreak___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_linebreak___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_linebreak___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_linebreak___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_linebreak___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_linebreak___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_linebreak = (const lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__5_value;
static const lean_string_object l_Lean_Doc_Syntax_code___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "code"};
static const lean_object* l_Lean_Doc_Syntax_code___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_code___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_code___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_code___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_code___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_code___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_code___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_code___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_code___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_code___closed__0_value),LEAN_SCALAR_PTR_LITERAL(115, 95, 172, 118, 77, 213, 142, 126)}};
static const lean_object* l_Lean_Doc_Syntax_code___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_code___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_code___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "code("};
static const lean_object* l_Lean_Doc_Syntax_code___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_code___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_code___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_code___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_code___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_code___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_code___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_code___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_code___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_code___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_code___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_code___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_code___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_code___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_code___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_code___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_code___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_code___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_code___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_code = (const lean_object*)&l_Lean_Doc_Syntax_code___closed__6_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 448, .m_capacity = 448, .m_length = 447, .m_data = "Literal code.\n\nCode may begin with any non-zero number of backticks. It must be terminated with the same number,\nand it may not contain a sequence of backticks that is at least as long as its starting or ending\ndelimiters.\n\nIf the first and last characters are space, and it contains at least one non-space character, then\nthe resulting string has a single space stripped from each end. Thus, ``` `` `x `` ``` represents\n``\"`x\"``, not ``\" `x \"``.\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_role___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "role"};
static const lean_object* l_Lean_Doc_Syntax_role___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_role___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_role___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_role___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_role___closed__0_value),LEAN_SCALAR_PTR_LITERAL(88, 39, 13, 65, 153, 69, 141, 111)}};
static const lean_object* l_Lean_Doc_Syntax_role___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_role___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "role{"};
static const lean_object* l_Lean_Doc_Syntax_role___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_role___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_role___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_role___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_emph___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_doc__arg_quot___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_role___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_role___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__6_value;
static const lean_string_object l_Lean_Doc_Syntax_role___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l_Lean_Doc_Syntax_role___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_role___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_role___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__6_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_role___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__9_value;
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__9_value),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__3_value)}};
static const lean_object* l_Lean_Doc_Syntax_role___closed__10 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__10_value;
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__10_value),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_role___closed__11 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__11_value;
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__11_value),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_role___closed__12 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__12_value;
static const lean_ctor_object l_Lean_Doc_Syntax_role___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_role___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_role___closed__12_value)}};
static const lean_object* l_Lean_Doc_Syntax_role___closed__13 = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__13_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_role = (const lean_object*)&l_Lean_Doc_Syntax_role___closed__13_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 762, .m_capacity = 762, .m_length = 761, .m_data = "A _role_: an extension to the Verso document language in an inline position.\n\nText is given a role using the following syntax: `{NAME ARGS*}[CONTENT]`. The `NAME` is an\nidentifier that determines which role is being used, akin to a function name. Each of the `ARGS` may\nhave the following forms:\n* A value, which is a string literal, natural number, or identifier\n* A named argument, of the form `(NAME := VALUE)`\n* A flag, of the form `+NAME` or `-NAME`\n\nThe `CONTENT` is a sequence of inline content. If there is only one piece of content and it has\nbeginning and ending delimiters (e.g. code literals, links, or images, but not ordinary text), then\nthe `[` and `]` may be omitted. In particular, `` {NAME ARGS*}`x` `` is equivalent to\n``{NAME ARGS*}[`x`]``.\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_inline__math___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "inline_math"};
static const lean_object* l_Lean_Doc_Syntax_inline__math___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline__math___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_inline__math___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_inline__math___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_inline__math___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__0_value),LEAN_SCALAR_PTR_LITERAL(39, 58, 152, 4, 55, 96, 114, 182)}};
static const lean_object* l_Lean_Doc_Syntax_inline__math___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_inline__math___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "\\math"};
static const lean_object* l_Lean_Doc_Syntax_inline__math___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline__math___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_inline__math___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline__math___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_code___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_inline__math___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_inline__math___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_inline__math___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_inline__math = (const lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__5_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "Inline mathematical notation (equivalent to LaTeX's `$` notation) "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_display__math___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "display_math"};
static const lean_object* l_Lean_Doc_Syntax_display__math___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_display__math___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_display__math___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_display__math___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_display__math___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_display__math___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_display__math___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_display__math___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_display__math___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_display__math___closed__0_value),LEAN_SCALAR_PTR_LITERAL(185, 134, 189, 58, 202, 192, 153, 244)}};
static const lean_object* l_Lean_Doc_Syntax_display__math___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_display__math___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_display__math___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "\\displaymath"};
static const lean_object* l_Lean_Doc_Syntax_display__math___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_display__math___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_display__math___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_display__math___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_display__math___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_display__math___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_display__math___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_display__math___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_code___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_display__math___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_display__math___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_display__math___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_display__math___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_display__math___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_display__math___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_display__math___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_display__math = (const lean_object*)&l_Lean_Doc_Syntax_display__math___closed__5_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Display-mode mathematical notation "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_block_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "block"};
static const lean_object* l_Lean_Doc_Syntax_block_quot___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_block_quot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 251, 195, 145, 15, 78, 208, 56)}};
static const lean_ctor_object l_Lean_Doc_Syntax_block_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(209, 131, 253, 7, 152, 186, 37, 254)}};
static const lean_object* l_Lean_Doc_Syntax_block_quot___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_block_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "`(block| "};
static const lean_object* l_Lean_Doc_Syntax_block_quot___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_block_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_block_quot___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_block_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 251, 195, 145, 15, 78, 208, 56)}};
static const lean_object* l_Lean_Doc_Syntax_block_quot___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_block_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Doc_Syntax_block_quot___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_block_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_block_quot___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_block_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_block_quot___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_block_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_block_quot___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_block_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_block_quot___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_block_quot = (const lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_block;
static const lean_string_object l_Lean_Doc_Syntax_list__item_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "list_item"};
static const lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_list__item_quot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 212, 251, 56, 191, 246, 167, 212)}};
static const lean_ctor_object l_Lean_Doc_Syntax_list__item_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(21, 109, 214, 10, 148, 231, 82, 169)}};
static const lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_list__item_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "`(list_item| "};
static const lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_list__item_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_list__item_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 212, 251, 56, 191, 246, 167, 212)}};
static const lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_list__item_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_list__item_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_list__item_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_list__item_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_list__item_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_list__item_quot___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_list__item_quot = (const lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_list__item;
static const lean_string_object l_Lean_Doc_Syntax_li___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "li"};
static const lean_object* l_Lean_Doc_Syntax_li___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_li___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_li___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_li___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_li___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_li___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_li___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_li___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_li___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_li___closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 229, 0, 156, 136, 247, 163, 99)}};
static const lean_object* l_Lean_Doc_Syntax_li___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_li___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_li___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l_Lean_Doc_Syntax_li___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_li___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_li___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_li___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_li___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_li___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_li___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_emph___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_li___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_li___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_li___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_li___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_li___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_li___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_li___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_li___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_li___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_li___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_li___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_li___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_li = (const lean_object*)&l_Lean_Doc_Syntax_li___closed__6_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "A list item "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_desc__item_quot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "desc_item"};
static const lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc__item_quot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 29, 44, 183, 55, 191, 144, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_desc__item_quot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__3_value),LEAN_SCALAR_PTR_LITERAL(55, 249, 160, 84, 217, 200, 245, 59)}};
static const lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_desc__item_quot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "`(desc_item| "};
static const lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc__item_quot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc__item_quot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(221, 29, 44, 183, 55, 191, 144, 255)}};
static const lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc__item_quot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc__item_quot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc__item_quot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc__item_quot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc__item_quot___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_desc__item_quot___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_desc__item_quot = (const lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__9_value;
LEAN_EXPORT lean_object* l_Lean_Parser_Category_desc__item;
static const lean_string_object l_Lean_Doc_Syntax_desc___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "desc"};
static const lean_object* l_Lean_Doc_Syntax_desc___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_desc___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_desc___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_desc___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_desc___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_desc___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_desc___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_desc___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_desc___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 44, 92, 80, 93, 40, 168, 47)}};
static const lean_object* l_Lean_Doc_Syntax_desc___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_desc___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_desc___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l_Lean_Doc_Syntax_desc___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_desc___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_desc___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_desc___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_desc___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_desc___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_desc___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_desc___closed__4_value;
static const lean_string_object l_Lean_Doc_Syntax_desc___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Lean_Doc_Syntax_desc___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_desc___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_desc___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_desc___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_desc___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_desc___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_desc___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_desc___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_desc___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_desc___closed__7_value),((lean_object*)&l_Lean_Doc_Syntax_li___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_desc___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_desc___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_desc___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_desc___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_desc___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_desc___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_desc___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_desc = (const lean_object*)&l_Lean_Doc_Syntax_desc___closed__9_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "A description of an item "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_para___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "para"};
static const lean_object* l_Lean_Doc_Syntax_para___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_para___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_para___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_para___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_para___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_para___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_para___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_para___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_para___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_para___closed__0_value),LEAN_SCALAR_PTR_LITERAL(114, 72, 198, 245, 142, 145, 171, 144)}};
static const lean_object* l_Lean_Doc_Syntax_para___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_para___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_para___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "para["};
static const lean_object* l_Lean_Doc_Syntax_para___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_para___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_para___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_para___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_para___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_para___closed__3_value;
static const lean_string_object l_Lean_Doc_Syntax_para___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "many1"};
static const lean_object* l_Lean_Doc_Syntax_para___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_para___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_para___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_para___closed__4_value),LEAN_SCALAR_PTR_LITERAL(55, 136, 52, 6, 12, 19, 78, 239)}};
static const lean_object* l_Lean_Doc_Syntax_para___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_para___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_para___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_para___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_para___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_para___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_para___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_para___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_para___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_para___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_para___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_para___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_para___closed__7_value),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_para___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_para___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_para___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_para___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_para___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_para___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_para___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_para = (const lean_object*)&l_Lean_Doc_Syntax_para___closed__9_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "Paragraph "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_ul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ul"};
static const lean_object* l_Lean_Doc_Syntax_ul___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_ul___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ul___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_ul___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ul___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_ul___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ul___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_ul___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ul___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_ul___closed__0_value),LEAN_SCALAR_PTR_LITERAL(248, 90, 162, 51, 92, 30, 144, 89)}};
static const lean_object* l_Lean_Doc_Syntax_ul___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_ul___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_ul___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ul{"};
static const lean_object* l_Lean_Doc_Syntax_ul___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_ul___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ul___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ul___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_ul___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_ul___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ul___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_emph___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_list__item_quot___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_ul___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_ul___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ul___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ul___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_ul___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_ul___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_ul___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ul___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ul___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_ul___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_ul___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ul___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ul___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_ul___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_ul___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_ul___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_ul = (const lean_object*)&l_Lean_Doc_Syntax_ul___closed__7_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "Unordered List "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_dl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "dl"};
static const lean_object* l_Lean_Doc_Syntax_dl___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_dl___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_dl___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_dl___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_dl___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_dl___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_dl___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_dl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_dl___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_dl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 49, 30, 64, 139, 101, 177, 168)}};
static const lean_object* l_Lean_Doc_Syntax_dl___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_dl___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_dl___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "dl{"};
static const lean_object* l_Lean_Doc_Syntax_dl___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_dl___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_dl___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_dl___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_dl___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_dl___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_dl___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_emph___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_desc__item_quot___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_dl___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_dl___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_dl___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_dl___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_dl___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_dl___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_dl___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_dl___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_dl___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_dl___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_dl___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_dl___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_dl___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_dl___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_dl___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_dl___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_dl = (const lean_object*)&l_Lean_Doc_Syntax_dl___closed__7_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Description list "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_ol___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ol"};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ol___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ol___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ol___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_ol___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 73, 192, 118, 161, 88, 51, 173)}};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_ol___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ol("};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ol___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ol___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ol___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__5_value;
static const lean_string_object l_Lean_Doc_Syntax_ol___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ol___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ol___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_ol___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ol___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ul___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__9_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ol___closed__9_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__10 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__10_value;
static const lean_ctor_object l_Lean_Doc_Syntax_ol___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_ol___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_ol___closed__10_value)}};
static const lean_object* l_Lean_Doc_Syntax_ol___closed__11 = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__11_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_ol = (const lean_object*)&l_Lean_Doc_Syntax_ol___closed__11_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Ordered list "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_codeblock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "codeblock"};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__0_value),LEAN_SCALAR_PTR_LITERAL(228, 242, 241, 127, 13, 6, 27, 177)}};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_codeblock___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "```"};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__3_value;
static const lean_string_object l_Lean_Doc_Syntax_codeblock___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "optional"};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__4_value),LEAN_SCALAR_PTR_LITERAL(233, 141, 154, 50, 143, 135, 42, 252)}};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__8_value;
static const lean_string_object l_Lean_Doc_Syntax_codeblock___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__9_value;
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__9_value)}};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__10 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__10_value;
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__10_value)}};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__11 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__11_value;
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__11_value),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__12 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__12_value;
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__12_value),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__3_value)}};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__13 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__13_value;
static const lean_ctor_object l_Lean_Doc_Syntax_codeblock___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__13_value)}};
static const lean_object* l_Lean_Doc_Syntax_codeblock___closed__14 = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__14_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_codeblock = (const lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__14_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1211, .m_capacity = 1211, .m_length = 1210, .m_data = "A code block that contains literal code.\n\nCode blocks have the following syntax:\n````\n```(NAME ARGS*)\?\nCONTENT\n```\n````\n\n`CONTENT` is a literal string. If the `CONTENT` contains a sequence of three or more backticks, then\nthe opening and closing ` ``` ` (called _fences_) should have more backticks than the longest\nsequence in `CONTENT`. Additionally, the opening and closing fences should have the same number of\nbackticks.\n\nIf `NAME` and `ARGS` are not provided, then the code block represents literal text. If provided, the\n`NAME` is an identifier that selects an interpretation of the block. Unlike Markdown, this name is\nnot necessarily the language in which the code is written, though many custom code blocks are, in\npractice, named after the language that they contain. `NAME` is more akin to a function name. Each\nof the `ARGS` may have the following forms:\n* A value, which is a string literal, natural number, or identifier\n* A named argument, of the form `(NAME := VALUE)`\n* A flag, of the form `+NAME` or `-NAME`\n\nThe `CONTENT` is interpreted according to the indentation of the fences. If the fences are indented\n`n` spaces, then `n` spaces are removed from the start of each line of `CONTENT`.\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_blockquote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "blockquote"};
static const lean_object* l_Lean_Doc_Syntax_blockquote___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_blockquote___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_blockquote___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_blockquote___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_blockquote___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__0_value),LEAN_SCALAR_PTR_LITERAL(154, 37, 74, 205, 107, 38, 107, 223)}};
static const lean_object* l_Lean_Doc_Syntax_blockquote___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_blockquote___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ">"};
static const lean_object* l_Lean_Doc_Syntax_blockquote___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_blockquote___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_blockquote___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_blockquote___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_li___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_blockquote___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_blockquote___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_blockquote___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__5_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_blockquote = (const lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__5_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 92, .m_capacity = 92, .m_length = 91, .m_data = "A quotation, which contains a sequence of blocks that are at least as indented as the `>`.\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_link__ref___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "link_ref"};
static const lean_object* l_Lean_Doc_Syntax_link__ref___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__ref___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_link__ref___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_link__ref___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_link__ref___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__0_value),LEAN_SCALAR_PTR_LITERAL(37, 122, 52, 169, 192, 153, 29, 165)}};
static const lean_object* l_Lean_Doc_Syntax_link__ref___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_link__ref___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]:"};
static const lean_object* l_Lean_Doc_Syntax_link__ref___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__ref___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_link__ref___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__ref___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__3_value)}};
static const lean_object* l_Lean_Doc_Syntax_link__ref___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__ref___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_link__ref___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_link__ref___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_link__ref___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__6_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_link__ref = (const lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__6_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 51, .m_capacity = 51, .m_length = 50, .m_data = "A named URL that can be used in links and images.\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_footnote__ref___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "footnote_ref"};
static const lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_footnote__ref___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_footnote__ref___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_footnote__ref___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_footnote__ref___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 7, 163, 121, 208, 236, 208, 13)}};
static const lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_footnote__ref___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[^"};
static const lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_footnote__ref___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_footnote__ref___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_footnote__ref___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__3_value)}};
static const lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_footnote__ref___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_footnote__ref___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_footnote__ref___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_footnote__ref = (const lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__7_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A footnote definition.\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_directive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "directive"};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_directive___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_directive___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_directive___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__0_value),LEAN_SCALAR_PTR_LITERAL(59, 236, 126, 236, 245, 181, 4, 182)}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_directive___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ":::"};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_directive___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__3_value;
static const lean_string_object l_Lean_Doc_Syntax_directive___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "rawIdent"};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__4_value),LEAN_SCALAR_PTR_LITERAL(112, 100, 176, 236, 81, 164, 232, 12)}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_directive___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__7_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_ol___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__9_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__4_value),((lean_object*)(((size_t)(1024) << 1) | 1))}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__10 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__10_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_emph___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__10_value)}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__11 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__11_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__9_value),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__11_value)}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__12 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__12_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__12_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__13 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__13_value;
static const lean_ctor_object l_Lean_Doc_Syntax_directive___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_directive___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__13_value)}};
static const lean_object* l_Lean_Doc_Syntax_directive___closed__14 = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__14_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_directive = (const lean_object*)&l_Lean_Doc_Syntax_directive___closed__14_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 675, .m_capacity = 675, .m_length = 674, .m_data = "A _directive_, which is an extension to the Verso language in block position.\n\nDirectives have the following syntax:\n```\n:::NAME ARGS*\nCONTENT*\n:::\n```\n\nThe `NAME` is an identifier that determines which directive is being used, akin to a function name.\nEach of the `ARGS` may have the following forms:\n* A value, which is a string literal, natural number, or identifier\n* A named argument, of the form `(NAME := VALUE)`\n* A flag, of the form `+NAME` or `-NAME`\n\nThe `CONTENT` is a sequence of block content. Directives may be nested by using more colons in\nthe outer directive. For example:\n```\n::::outer +flag (arg := 5)\nA paragraph.\n:::inner \"label\"\n* 1\n* 2\n:::\n::::\n```\n\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_header___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l_Lean_Doc_Syntax_header___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_header___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_header___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_header___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_header___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_header___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_header___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_header___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_header___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_header___closed__0_value),LEAN_SCALAR_PTR_LITERAL(138, 131, 27, 234, 140, 72, 2, 168)}};
static const lean_object* l_Lean_Doc_Syntax_header___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_header___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_header___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "header("};
static const lean_object* l_Lean_Doc_Syntax_header___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_header___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_header___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_header___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_header___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_header___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_header___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_header___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__4_value)}};
static const lean_object* l_Lean_Doc_Syntax_header___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_header___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_header___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_header___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__14_value)}};
static const lean_object* l_Lean_Doc_Syntax_header___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_header___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_header___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_header___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_ol___closed__7_value)}};
static const lean_object* l_Lean_Doc_Syntax_header___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_header___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_header___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_header___closed__6_value),((lean_object*)&l_Lean_Doc_Syntax_para___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_header___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_header___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_header___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_header___closed__7_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_header___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_header___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_header___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_header___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_header___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_header___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_header___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_header = (const lean_object*)&l_Lean_Doc_Syntax_header___closed__9_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 203, .m_capacity = 203, .m_length = 202, .m_data = "A header\n\nHeaders must be correctly nested to form a tree structure. The first header in a document must\nstart with `#`, and subsequent headers must have at most one more `#` than the preceding header.\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_metadataContents___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Doc_Syntax_metadataContents___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_metadataContents___closed__0_value;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__1;
static const lean_string_object l_Lean_Doc_Syntax_metadataContents___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sepBy"};
static const lean_object* l_Lean_Doc_Syntax_metadataContents___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_metadataContents___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_metadataContents___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_metadataContents___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 56, 254, 223, 11, 70, 55, 147)}};
static const lean_object* l_Lean_Doc_Syntax_metadataContents___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_metadataContents___closed__3_value;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__4;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__5;
static const lean_string_object l_Lean_Doc_Syntax_metadataContents___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "irrelevant"};
static const lean_object* l_Lean_Doc_Syntax_metadataContents___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_metadataContents___closed__6_value;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__7;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__8;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__9;
static const lean_string_object l_Lean_Doc_Syntax_metadataContents___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "line break"};
static const lean_object* l_Lean_Doc_Syntax_metadataContents___closed__10 = (const lean_object*)&l_Lean_Doc_Syntax_metadataContents___closed__10_value;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__11;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__12;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__13;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__14;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__15;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__16;
static lean_once_cell_t l_Lean_Doc_Syntax_metadataContents___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Syntax_metadataContents___closed__17;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents;
static const lean_string_object l_Lean_Doc_Syntax_metadata__block___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "metadata_block"};
static const lean_object* l_Lean_Doc_Syntax_metadata__block___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__0_value),LEAN_SCALAR_PTR_LITERAL(75, 201, 5, 85, 129, 97, 253, 216)}};
static const lean_object* l_Lean_Doc_Syntax_metadata__block___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_metadata__block___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "%%%"};
static const lean_object* l_Lean_Doc_Syntax_metadata__block___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_metadata__block___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__3_value;
static const lean_string_object l_Lean_Doc_Syntax_metadata__block___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "metadataContents"};
static const lean_object* l_Lean_Doc_Syntax_metadata__block___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__5_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__5_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__5_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__4_value),LEAN_SCALAR_PTR_LITERAL(235, 164, 223, 160, 173, 108, 137, 29)}};
static const lean_object* l_Lean_Doc_Syntax_metadata__block___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 8}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_metadata__block___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_metadata__block___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__7_value;
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__7_value),((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__3_value)}};
static const lean_object* l_Lean_Doc_Syntax_metadata__block___closed__8 = (const lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__8_value;
static const lean_ctor_object l_Lean_Doc_Syntax_metadata__block___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_metadata__block___closed__9 = (const lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__9_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_metadata__block = (const lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__9_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 36, .m_capacity = 36, .m_length = 35, .m_data = "Metadata for the preceding header.\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Syntax_metadataContents_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_structInstField_formatter___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Syntax_metadataContents_formatter___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_metadataContents_formatter___closed__0_value;
static const lean_closure_object l_Lean_Doc_Syntax_metadataContents_formatter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_formatter___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadataContents___closed__0_value)} };
static const lean_object* l_Lean_Doc_Syntax_metadataContents_formatter___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_metadataContents_formatter___closed__1_value;
static const lean_closure_object l_Lean_Doc_Syntax_metadataContents_formatter___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_sepByIndent_formatter___boxed, .m_arity = 8, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadataContents_formatter___closed__0_value),((lean_object*)&l_Lean_Doc_Syntax_metadataContents___closed__0_value),((lean_object*)&l_Lean_Doc_Syntax_metadataContents_formatter___closed__1_value)} };
static const lean_object* l_Lean_Doc_Syntax_metadataContents_formatter___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_metadataContents_formatter___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_Term_structInstField_parenthesizer___boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__0_value;
static const lean_closure_object l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_symbol_parenthesizer___boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadataContents___closed__0_value)} };
static const lean_object* l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__1_value;
static const lean_closure_object l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_sepByIndent_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__0_value),((lean_object*)&l_Lean_Doc_Syntax_metadataContents___closed__0_value),((lean_object*)&l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_Syntax_command___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l_Lean_Doc_Syntax_command___closed__0 = (const lean_object*)&l_Lean_Doc_Syntax_command___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Syntax_command___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Syntax_command___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_command___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Syntax_command___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_command___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__1_value),LEAN_SCALAR_PTR_LITERAL(133, 108, 207, 58, 1, 109, 247, 255)}};
static const lean_ctor_object l_Lean_Doc_Syntax_command___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_command___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_command___closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 102, 246, 27, 44, 229, 232, 70)}};
static const lean_object* l_Lean_Doc_Syntax_command___closed__1 = (const lean_object*)&l_Lean_Doc_Syntax_command___closed__1_value;
static const lean_string_object l_Lean_Doc_Syntax_command___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "command{"};
static const lean_object* l_Lean_Doc_Syntax_command___closed__2 = (const lean_object*)&l_Lean_Doc_Syntax_command___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Syntax_command___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_command___closed__2_value)}};
static const lean_object* l_Lean_Doc_Syntax_command___closed__3 = (const lean_object*)&l_Lean_Doc_Syntax_command___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Syntax_command___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_command___closed__3_value),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_command___closed__4 = (const lean_object*)&l_Lean_Doc_Syntax_command___closed__4_value;
static const lean_ctor_object l_Lean_Doc_Syntax_command___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_command___closed__4_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__5_value)}};
static const lean_object* l_Lean_Doc_Syntax_command___closed__5 = (const lean_object*)&l_Lean_Doc_Syntax_command___closed__5_value;
static const lean_ctor_object l_Lean_Doc_Syntax_command___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__8_value),((lean_object*)&l_Lean_Doc_Syntax_command___closed__5_value),((lean_object*)&l_Lean_Doc_Syntax_role___closed__8_value)}};
static const lean_object* l_Lean_Doc_Syntax_command___closed__6 = (const lean_object*)&l_Lean_Doc_Syntax_command___closed__6_value;
static const lean_ctor_object l_Lean_Doc_Syntax_command___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Doc_Syntax_command___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_command___closed__6_value)}};
static const lean_object* l_Lean_Doc_Syntax_command___closed__7 = (const lean_object*)&l_Lean_Doc_Syntax_command___closed__7_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Syntax_command = (const lean_object*)&l_Lean_Doc_Syntax_command___closed__7_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 391, .m_capacity = 391, .m_length = 390, .m_data = "A block-level command, which invokes an extension during documentation processing.\n\nThe `NAME` is an identifier that determines which command is being used, akin to a function name.\nEach of the `ARGS` may have the following forms:\n* A value, which is a string literal, natural number, or identifier\n* A named argument, of the form `(NAME := VALUE)`\n* A flag, of the form `+NAME` or `-NAME`\n"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1___boxed(lean_object*);
static lean_object* _init_l_Lean_Parser_Category_arg__val(void){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = lean_box(0);
return v___x_45_;
}
}
static lean_object* _init_l_Lean_Parser_Category_doc__arg(void){
_start:
{
lean_object* v___x_125_; 
v___x_125_ = lean_box(0);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1(){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_139_ = ((lean_object*)(l_Lean_Doc_Syntax_anon___closed__1));
v___x_140_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1___closed__0));
v___x_141_ = l_Lean_addBuiltinDocString(v___x_139_, v___x_140_);
return v___x_141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1___boxed(lean_object* v_a_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1();
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1(){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_179_ = ((lean_object*)(l_Lean_Doc_Syntax_named___closed__1));
v___x_180_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___closed__0));
v___x_181_ = l_Lean_addBuiltinDocString(v___x_179_, v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___boxed(lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1();
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named__no__paren___regBuiltin_Lean_Doc_Syntax_named__no__paren_docString__1(){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_204_ = ((lean_object*)(l_Lean_Doc_Syntax_named__no__paren___closed__1));
v___x_205_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___closed__0));
v___x_206_ = l_Lean_addBuiltinDocString(v___x_204_, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named__no__paren___regBuiltin_Lean_Doc_Syntax_named__no__paren_docString__1___boxed(lean_object* v_a_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named__no__paren___regBuiltin_Lean_Doc_Syntax_named__no__paren_docString__1();
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1(){
_start:
{
lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_229_ = ((lean_object*)(l_Lean_Doc_Syntax_flag__on___closed__1));
v___x_230_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1___closed__0));
v___x_231_ = l_Lean_addBuiltinDocString(v___x_229_, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1___boxed(lean_object* v_a_232_){
_start:
{
lean_object* v_res_233_; 
v_res_233_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1();
return v_res_233_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1(){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = ((lean_object*)(l_Lean_Doc_Syntax_flag__off___closed__1));
v___x_255_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1___closed__0));
v___x_256_ = l_Lean_addBuiltinDocString(v___x_254_, v___x_255_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1___boxed(lean_object* v_a_257_){
_start:
{
lean_object* v_res_258_; 
v_res_258_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1();
return v_res_258_;
}
}
static lean_object* _init_l_Lean_Parser_Category_link__target(void){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = lean_box(0);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1(){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_310_ = ((lean_object*)(l_Lean_Doc_Syntax_url___closed__1));
v___x_311_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1___closed__0));
v___x_312_ = l_Lean_addBuiltinDocString(v___x_310_, v___x_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1___boxed(lean_object* v_a_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1();
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1(){
_start:
{
lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; 
v___x_342_ = ((lean_object*)(l_Lean_Doc_Syntax_ref___closed__1));
v___x_343_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1___closed__0));
v___x_344_ = l_Lean_addBuiltinDocString(v___x_342_, v___x_343_);
return v___x_344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1___boxed(lean_object* v_a_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1();
return v_res_346_;
}
}
static lean_object* _init_l_Lean_Parser_Category_inline(void){
_start:
{
lean_object* v___x_376_; 
v___x_376_ = lean_box(0);
return v___x_376_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1(){
_start:
{
lean_object* v___x_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
v___x_418_ = ((lean_object*)(l_Lean_Doc_Syntax_emph___closed__1));
v___x_419_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1___closed__0));
v___x_420_ = l_Lean_addBuiltinDocString(v___x_418_, v___x_419_);
return v___x_420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1___boxed(lean_object* v_a_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1();
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1(){
_start:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_447_ = ((lean_object*)(l_Lean_Doc_Syntax_bold___closed__1));
v___x_448_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1___closed__0));
v___x_449_ = l_Lean_addBuiltinDocString(v___x_447_, v___x_448_);
return v___x_449_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1___boxed(lean_object* v_a_450_){
_start:
{
lean_object* v_res_451_; 
v_res_451_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1();
return v_res_451_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1(){
_start:
{
lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v___x_480_ = ((lean_object*)(l_Lean_Doc_Syntax_link___closed__1));
v___x_481_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1___closed__0));
v___x_482_ = l_Lean_addBuiltinDocString(v___x_480_, v___x_481_);
return v___x_482_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1___boxed(lean_object* v_a_483_){
_start:
{
lean_object* v_res_484_; 
v_res_484_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1();
return v_res_484_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1(){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_513_ = ((lean_object*)(l_Lean_Doc_Syntax_image___closed__1));
v___x_514_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1___closed__0));
v___x_515_ = l_Lean_addBuiltinDocString(v___x_513_, v___x_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1___boxed(lean_object* v_a_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1();
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1(){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_542_ = ((lean_object*)(l_Lean_Doc_Syntax_footnote___closed__1));
v___x_543_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1___closed__0));
v___x_544_ = l_Lean_addBuiltinDocString(v___x_542_, v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1___boxed(lean_object* v_a_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1();
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1(){
_start:
{
lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; 
v___x_589_ = ((lean_object*)(l_Lean_Doc_Syntax_code___closed__1));
v___x_590_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1___closed__0));
v___x_591_ = l_Lean_addBuiltinDocString(v___x_589_, v___x_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1___boxed(lean_object* v_a_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1();
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1(){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; 
v___x_640_ = ((lean_object*)(l_Lean_Doc_Syntax_role___closed__1));
v___x_641_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1___closed__0));
v___x_642_ = l_Lean_addBuiltinDocString(v___x_640_, v___x_641_);
return v___x_642_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1___boxed(lean_object* v_a_643_){
_start:
{
lean_object* v_res_644_; 
v_res_644_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1();
return v_res_644_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1(){
_start:
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = ((lean_object*)(l_Lean_Doc_Syntax_inline__math___closed__1));
v___x_666_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1___closed__0));
v___x_667_ = l_Lean_addBuiltinDocString(v___x_665_, v___x_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1___boxed(lean_object* v_a_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1();
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1(){
_start:
{
lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; 
v___x_690_ = ((lean_object*)(l_Lean_Doc_Syntax_display__math___closed__1));
v___x_691_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1___closed__0));
v___x_692_ = l_Lean_addBuiltinDocString(v___x_690_, v___x_691_);
return v___x_692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1___boxed(lean_object* v_a_693_){
_start:
{
lean_object* v_res_694_; 
v_res_694_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1();
return v_res_694_;
}
}
static lean_object* _init_l_Lean_Parser_Category_block(void){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = lean_box(0);
return v___x_724_;
}
}
static lean_object* _init_l_Lean_Parser_Category_list__item(void){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = lean_box(0);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1(){
_start:
{
lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_778_ = ((lean_object*)(l_Lean_Doc_Syntax_li___closed__1));
v___x_779_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1___closed__0));
v___x_780_ = l_Lean_addBuiltinDocString(v___x_778_, v___x_779_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1___boxed(lean_object* v_a_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1();
return v_res_782_;
}
}
static lean_object* _init_l_Lean_Parser_Category_desc__item(void){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = lean_box(0);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1(){
_start:
{
lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; 
v___x_844_ = ((lean_object*)(l_Lean_Doc_Syntax_desc___closed__1));
v___x_845_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1___closed__0));
v___x_846_ = l_Lean_addBuiltinDocString(v___x_844_, v___x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1___boxed(lean_object* v_a_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1();
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1(){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; 
v___x_879_ = ((lean_object*)(l_Lean_Doc_Syntax_para___closed__1));
v___x_880_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1___closed__0));
v___x_881_ = l_Lean_addBuiltinDocString(v___x_879_, v___x_880_);
return v___x_881_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1___boxed(lean_object* v_a_882_){
_start:
{
lean_object* v_res_883_; 
v_res_883_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1();
return v_res_883_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1(){
_start:
{
lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_911_ = ((lean_object*)(l_Lean_Doc_Syntax_ul___closed__1));
v___x_912_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1___closed__0));
v___x_913_ = l_Lean_addBuiltinDocString(v___x_911_, v___x_912_);
return v___x_913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1___boxed(lean_object* v_a_914_){
_start:
{
lean_object* v_res_915_; 
v_res_915_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1();
return v_res_915_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1(){
_start:
{
lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; 
v___x_943_ = ((lean_object*)(l_Lean_Doc_Syntax_dl___closed__1));
v___x_944_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1___closed__0));
v___x_945_ = l_Lean_addBuiltinDocString(v___x_943_, v___x_944_);
return v___x_945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1___boxed(lean_object* v_a_946_){
_start:
{
lean_object* v_res_947_; 
v_res_947_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1();
return v_res_947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1(){
_start:
{
lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; 
v___x_987_ = ((lean_object*)(l_Lean_Doc_Syntax_ol___closed__1));
v___x_988_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1___closed__0));
v___x_989_ = l_Lean_addBuiltinDocString(v___x_987_, v___x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1___boxed(lean_object* v_a_990_){
_start:
{
lean_object* v_res_991_; 
v_res_991_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1();
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1(){
_start:
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1037_ = ((lean_object*)(l_Lean_Doc_Syntax_codeblock___closed__1));
v___x_1038_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1___closed__0));
v___x_1039_ = l_Lean_addBuiltinDocString(v___x_1037_, v___x_1038_);
return v___x_1039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1___boxed(lean_object* v_a_1040_){
_start:
{
lean_object* v_res_1041_; 
v_res_1041_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1();
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1(){
_start:
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = ((lean_object*)(l_Lean_Doc_Syntax_blockquote___closed__1));
v___x_1063_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1___closed__0));
v___x_1064_ = l_Lean_addBuiltinDocString(v___x_1062_, v___x_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1___boxed(lean_object* v_a_1065_){
_start:
{
lean_object* v_res_1066_; 
v_res_1066_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1();
return v_res_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1(){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = ((lean_object*)(l_Lean_Doc_Syntax_link__ref___closed__1));
v___x_1092_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1___closed__0));
v___x_1093_ = l_Lean_addBuiltinDocString(v___x_1091_, v___x_1092_);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1___boxed(lean_object* v_a_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1();
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1(){
_start:
{
lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; 
v___x_1124_ = ((lean_object*)(l_Lean_Doc_Syntax_footnote__ref___closed__1));
v___x_1125_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1___closed__0));
v___x_1126_ = l_Lean_addBuiltinDocString(v___x_1124_, v___x_1125_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1___boxed(lean_object* v_a_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1();
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1(){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___x_1176_ = ((lean_object*)(l_Lean_Doc_Syntax_directive___closed__1));
v___x_1177_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1___closed__0));
v___x_1178_ = l_Lean_addBuiltinDocString(v___x_1176_, v___x_1177_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1___boxed(lean_object* v_a_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1();
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1(){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1217_ = ((lean_object*)(l_Lean_Doc_Syntax_header___closed__1));
v___x_1218_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1___closed__0));
v___x_1219_ = l_Lean_addBuiltinDocString(v___x_1217_, v___x_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1___boxed(lean_object* v_a_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1();
return v_res_1221_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__1(void){
_start:
{
lean_object* v___x_1223_; lean_object* v___x_1224_; 
v___x_1223_ = ((lean_object*)(l_Lean_Doc_Syntax_metadataContents___closed__0));
v___x_1224_ = l_Lean_Parser_symbol(v___x_1223_);
return v___x_1224_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__4(void){
_start:
{
lean_object* v___x_1228_; lean_object* v___x_1229_; 
v___x_1228_ = ((lean_object*)(l_Lean_Doc_Syntax_li___closed__2));
v___x_1229_ = l_Lean_Parser_symbol(v___x_1228_);
return v___x_1229_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__5(void){
_start:
{
lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v_p_1233_; 
v___x_1230_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__4, &l_Lean_Doc_Syntax_metadataContents___closed__4_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__4);
v___x_1231_ = l_Lean_Parser_Term_structInstField;
v___x_1232_ = ((lean_object*)(l_Lean_Doc_Syntax_metadataContents___closed__3));
v_p_1233_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1232_, v___x_1231_, v___x_1230_);
return v_p_1233_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__7(void){
_start:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; 
v___x_1235_ = ((lean_object*)(l_Lean_Doc_Syntax_metadataContents___closed__6));
v___x_1236_ = l_Lean_Parser_checkColGe(v___x_1235_);
return v___x_1236_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__8(void){
_start:
{
lean_object* v_p_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; 
v_p_1237_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__5, &l_Lean_Doc_Syntax_metadataContents___closed__5_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__5);
v___x_1238_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__7, &l_Lean_Doc_Syntax_metadataContents___closed__7_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__7);
v___x_1239_ = l_Lean_Parser_andthen(v___x_1238_, v_p_1237_);
return v___x_1239_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__9(void){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; 
v___x_1240_ = ((lean_object*)(l_Lean_Doc_Syntax_metadataContents___closed__6));
v___x_1241_ = l_Lean_Parser_checkColEq(v___x_1240_);
return v___x_1241_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__11(void){
_start:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = ((lean_object*)(l_Lean_Doc_Syntax_metadataContents___closed__10));
v___x_1244_ = l_Lean_Parser_checkLinebreakBefore(v___x_1243_);
return v___x_1244_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__12(void){
_start:
{
lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1245_ = l_Lean_Parser_pushNone;
v___x_1246_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__11, &l_Lean_Doc_Syntax_metadataContents___closed__11_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__11);
v___x_1247_ = l_Lean_Parser_andthen(v___x_1246_, v___x_1245_);
return v___x_1247_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__13(void){
_start:
{
lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; 
v___x_1248_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__12, &l_Lean_Doc_Syntax_metadataContents___closed__12_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__12);
v___x_1249_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__9, &l_Lean_Doc_Syntax_metadataContents___closed__9_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__9);
v___x_1250_ = l_Lean_Parser_andthen(v___x_1249_, v___x_1248_);
return v___x_1250_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__14(void){
_start:
{
lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
v___x_1251_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__13, &l_Lean_Doc_Syntax_metadataContents___closed__13_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__13);
v___x_1252_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__1, &l_Lean_Doc_Syntax_metadataContents___closed__1_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__1);
v___x_1253_ = l_Lean_Parser_orelse(v___x_1252_, v___x_1251_);
return v___x_1253_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__15(void){
_start:
{
uint8_t v___x_1254_; lean_object* v___x_1255_; lean_object* v___x_1256_; lean_object* v___x_1257_; lean_object* v___x_1258_; 
v___x_1254_ = 1;
v___x_1255_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__14, &l_Lean_Doc_Syntax_metadataContents___closed__14_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__14);
v___x_1256_ = ((lean_object*)(l_Lean_Doc_Syntax_metadataContents___closed__0));
v___x_1257_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__8, &l_Lean_Doc_Syntax_metadataContents___closed__8_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__8);
v___x_1258_ = l_Lean_Parser_sepBy(v___x_1257_, v___x_1256_, v___x_1255_, v___x_1254_);
return v___x_1258_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__16(void){
_start:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__15, &l_Lean_Doc_Syntax_metadataContents___closed__15_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__15);
v___x_1260_ = l_Lean_Parser_withPosition(v___x_1259_);
return v___x_1260_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents___closed__17(void){
_start:
{
lean_object* v___x_1261_; lean_object* v___x_1262_; 
v___x_1261_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__16, &l_Lean_Doc_Syntax_metadataContents___closed__16_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__16);
v___x_1262_ = l_Lean_Parser_Term_structInstFields(v___x_1261_);
return v___x_1262_;
}
}
static lean_object* _init_l_Lean_Doc_Syntax_metadataContents(void){
_start:
{
lean_object* v___x_1263_; 
v___x_1263_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__17, &l_Lean_Doc_Syntax_metadataContents___closed__17_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__17);
return v___x_1263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1(){
_start:
{
lean_object* v___x_1296_; lean_object* v___x_1297_; lean_object* v___x_1298_; 
v___x_1296_ = ((lean_object*)(l_Lean_Doc_Syntax_metadata__block___closed__1));
v___x_1297_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1___closed__0));
v___x_1298_ = l_Lean_addBuiltinDocString(v___x_1296_, v___x_1297_);
return v___x_1298_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1___boxed(lean_object* v_a_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1();
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents_formatter(lean_object* v_a_1308_, lean_object* v_a_1309_, lean_object* v_a_1310_, lean_object* v_a_1311_){
_start:
{
lean_object* v___x_1313_; lean_object* v___x_1314_; 
v___x_1313_ = ((lean_object*)(l_Lean_Doc_Syntax_metadataContents_formatter___closed__2));
v___x_1314_ = l_Lean_Parser_Term_structInstFields_formatter(v___x_1313_, v_a_1308_, v_a_1309_, v_a_1310_, v_a_1311_);
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents_formatter___boxed(lean_object* v_a_1315_, lean_object* v_a_1316_, lean_object* v_a_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_Doc_Syntax_metadataContents_formatter(v_a_1315_, v_a_1316_, v_a_1317_, v_a_1318_);
lean_dec(v_a_1318_);
lean_dec_ref(v_a_1317_);
lean_dec(v_a_1316_);
lean_dec_ref(v_a_1315_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents_parenthesizer(lean_object* v_a_1330_, lean_object* v_a_1331_, lean_object* v_a_1332_, lean_object* v_a_1333_){
_start:
{
lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1335_ = ((lean_object*)(l_Lean_Doc_Syntax_metadataContents_parenthesizer___closed__2));
v___x_1336_ = l_Lean_Parser_Term_structInstFields_parenthesizer(v___x_1335_, v_a_1330_, v_a_1331_, v_a_1332_, v_a_1333_);
return v___x_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Syntax_metadataContents_parenthesizer___boxed(lean_object* v_a_1337_, lean_object* v_a_1338_, lean_object* v_a_1339_, lean_object* v_a_1340_, lean_object* v_a_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_Lean_Doc_Syntax_metadataContents_parenthesizer(v_a_1337_, v_a_1338_, v_a_1339_, v_a_1340_);
lean_dec(v_a_1340_);
lean_dec_ref(v_a_1339_);
lean_dec(v_a_1338_);
lean_dec_ref(v_a_1337_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1(){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1371_ = ((lean_object*)(l_Lean_Doc_Syntax_command___closed__1));
v___x_1372_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1___closed__0));
v___x_1373_ = l_Lean_addBuiltinDocString(v___x_1371_, v___x_1372_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1___boxed(lean_object* v_a_1374_){
_start:
{
lean_object* v_res_1375_; 
v_res_1375_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1();
return v_res_1375_;
}
}
lean_object* runtime_initialize_Lean_Parser_Term_Basic(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named__no__paren___regBuiltin_Lean_Doc_Syntax_named__no__paren_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* runtime_initialize_Lean_Parser_Term_Basic(uint8_t builtin);
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_DocString_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
res = runtime_initialize_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Parser_Category_arg__val = _init_l_Lean_Parser_Category_arg__val();
lean_mark_persistent(l_Lean_Parser_Category_arg__val);
l_Lean_Parser_Category_doc__arg = _init_l_Lean_Parser_Category_doc__arg();
lean_mark_persistent(l_Lean_Parser_Category_doc__arg);
l_Lean_Parser_Category_link__target = _init_l_Lean_Parser_Category_link__target();
lean_mark_persistent(l_Lean_Parser_Category_link__target);
l_Lean_Parser_Category_inline = _init_l_Lean_Parser_Category_inline();
lean_mark_persistent(l_Lean_Parser_Category_inline);
l_Lean_Parser_Category_block = _init_l_Lean_Parser_Category_block();
lean_mark_persistent(l_Lean_Parser_Category_block);
l_Lean_Parser_Category_list__item = _init_l_Lean_Parser_Category_list__item();
lean_mark_persistent(l_Lean_Parser_Category_list__item);
l_Lean_Parser_Category_desc__item = _init_l_Lean_Parser_Category_desc__item();
lean_mark_persistent(l_Lean_Parser_Category_desc__item);
l_Lean_Doc_Syntax_metadataContents = _init_l_Lean_Doc_Syntax_metadataContents();
lean_mark_persistent(l_Lean_Doc_Syntax_metadataContents);
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Parser_Term_Basic(uint8_t builtin);
lean_object* initialize_Lean_Parser_Term_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_DocString_Syntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_DocString_Syntax(builtin);
}
#ifdef __cplusplus
}
#endif
