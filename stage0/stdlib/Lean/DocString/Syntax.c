// Lean compiler output
// Module: Lean.DocString.Syntax
// Imports: public import Lean.Parser.Term.Basic public import Lean.DocString.Types meta import Lean.Parser.Term.Basic
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
extern lean_object* l_Lean_Parser_skip;
lean_object* l_Lean_Parser_node(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeWhile1Fn(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_instBEqError_beq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkErrorAt(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_rawFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_tokenWithAntiquot(lean_object*);
lean_object* l_Lean_Parser_atomic(lean_object*);
lean_object* l_Lean_Parser_many(lean_object*);
lean_object* l_Lean_Parser_SyntaxStack_back(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_data(lean_object*);
lean_object* l_Lean_Parser_satisfyFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol(lean_object*);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_ident;
extern lean_object* l_Lean_Parser_numLit;
extern lean_object* l_Lean_Parser_strLit;
lean_object* l_Lean_Parser_many1(lean_object*);
lean_object* l_Lean_Parser_withAntiquotFn(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Syntax_isLit_x3f(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_pushNone;
lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
lean_object* l_Lean_Parser_checkColEq(lean_object*);
extern lean_object* l_Lean_Parser_Term_structInstField;
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColGe(lean_object*);
lean_object* l_Lean_Parser_sepBy(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_withPosition(lean_object*);
lean_object* l_Lean_Parser_Term_structInstFields(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_symbol_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_structInstField_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByIndent_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_structInstFields_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_satisfyFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_notFollowedBy(lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional(lean_object*);
lean_object* l_Lean_Data_Trie_insert___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_adaptUncacheableContextFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Parser_symbol_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getAtomVal(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___closed__0_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse(lean_object*);
static const lean_string_object l_Lean_Doc_Parser_versoText___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "versoText"};
static const lean_object* l_Lean_Doc_Parser_versoText___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoText___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoText___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoText___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoText___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 255, 240, 17, 75, 250, 253, 95)}};
static const lean_object* l_Lean_Doc_Parser_versoText___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_versoText___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_versoText___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoText___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoText___lam__1(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoText___lam__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoText___lam__2(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoText___lam__2___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_versoText___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_versoText___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_versoText___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoText___closed__0_value;
static const lean_closure_object l_Lean_Doc_Parser_versoText___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_versoText___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_versoText___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoText___closed__1_value;
static const lean_closure_object l_Lean_Doc_Parser_versoText___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_versoText___lam__2___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_versoText___closed__2 = (const lean_object*)&l_Lean_Doc_Parser_versoText___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoText___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__1_value),((lean_object*)&l_Lean_Doc_Parser_versoText___closed__2_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Doc_Parser_versoText___closed__3 = (const lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoText___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_versoText___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_versoText___closed__4 = (const lean_object*)&l_Lean_Doc_Parser_versoText___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_versoText = (const lean_object*)&l_Lean_Doc_Parser_versoText___closed__4_value;
static const lean_string_object l_Lean_Doc_Parser_versoRef___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "versoRef"};
static const lean_object* l_Lean_Doc_Parser_versoRef___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoRef___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoRef___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoRef___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoRef___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoRef___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoRef___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoRef___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoRef___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_versoRef___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(50, 44, 27, 25, 170, 146, 153, 245)}};
static const lean_object* l_Lean_Doc_Parser_versoRef___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoRef___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_versoRef___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_versoRef___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoRef___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_versoRef___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_versoRef___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_versoRef___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoRef___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoRef___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_versoRef___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_versoRef___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoRef___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_versoRef = (const lean_object*)&l_Lean_Doc_Parser_versoRef___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "versoLinkUrl"};
static const lean_object* l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(142, 188, 54, 130, 131, 60, 251, 148)}};
static const lean_object* l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoLinkUrl___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_versoLinkUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_versoLinkUrl___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_versoLinkUrl___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoLinkUrl___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkUrl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_versoLinkUrl___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_versoLinkUrl___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoLinkUrl___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_versoLinkUrl = (const lean_object*)&l_Lean_Doc_Parser_versoLinkUrl___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "versoLinkRefUrl"};
static const lean_object* l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 57, 106, 22, 121, 78, 15, 41)}};
static const lean_object* l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoLinkRefUrl___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_versoLinkRefUrl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_versoLinkRefUrl___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_versoLinkRefUrl___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoLinkRefUrl___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkRefUrl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_versoLinkRefUrl___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_versoLinkRefUrl___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoLinkRefUrl___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_versoLinkRefUrl = (const lean_object*)&l_Lean_Doc_Parser_versoLinkRefUrl___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "versoImageAlt"};
static const lean_object* l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(83, 180, 119, 241, 128, 95, 219, 17)}};
static const lean_object* l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoImageAlt___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_versoImageAlt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_versoImageAlt___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_versoImageAlt___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoImageAlt___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoImageAlt___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_versoImageAlt___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_versoImageAlt___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoImageAlt___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_versoImageAlt = (const lean_object*)&l_Lean_Doc_Parser_versoImageAlt___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_versoCode___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "versoCode"};
static const lean_object* l_Lean_Doc_Parser_versoCode___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoCode___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoCode___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCode___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCode___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCode___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCode___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCode___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCode___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_versoCode___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(27, 134, 52, 97, 245, 192, 23, 73)}};
static const lean_object* l_Lean_Doc_Parser_versoCode___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoCode___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_versoCode___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_versoCode___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoCode___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_versoCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_versoCode___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_versoCode___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoCode___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoCode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_versoCode___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_versoCode___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoCode___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_versoCode = (const lean_object*)&l_Lean_Doc_Parser_versoCode___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "versoCodeLine"};
static const lean_object* l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(58, 193, 253, 137, 135, 225, 29, 137)}};
static const lean_object* l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoCodeLine___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_versoCodeLine___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_versoCodeLine___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_versoCodeLine___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoCodeLine___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeLine___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_versoCodeLine___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_versoCodeLine___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoCodeLine___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_versoCodeLine = (const lean_object*)&l_Lean_Doc_Parser_versoCodeLine___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "versoCodeBlock"};
static const lean_object* l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(244, 196, 91, 225, 102, 151, 154, 53)}};
static const lean_object* l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoCodeBlock___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_versoCodeBlock___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_versoCodeBlock___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_versoCodeBlock___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoCodeBlock___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeBlock___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_versoCodeBlock___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_versoCodeBlock___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoCodeBlock___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_versoCodeBlock = (const lean_object*)&l_Lean_Doc_Parser_versoCodeBlock___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoTextKind = (const lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoRefKind = (const lean_object*)&l_Lean_Doc_Parser_versoRef___lam__0___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoLinkUrlKind = (const lean_object*)&l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoLinkRefUrlKind = (const lean_object*)&l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoImageAltKind = (const lean_object*)&l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoCodeKind = (const lean_object*)&l_Lean_Doc_Parser_versoCode___lam__0___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoCodeLineKind = (const lean_object*)&l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoCodeBlockKind = (const lean_object*)&l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__1_value;
static const lean_string_object l_Lean_Doc_parseFailureKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "parseFailure"};
static const lean_object* l_Lean_Doc_parseFailureKind___closed__0 = (const lean_object*)&l_Lean_Doc_parseFailureKind___closed__0_value;
static const lean_ctor_object l_Lean_Doc_parseFailureKind___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_parseFailureKind___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_parseFailureKind___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_parseFailureKind___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_parseFailureKind___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_parseFailureKind___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_parseFailureKind___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_parseFailureKind___closed__0_value),LEAN_SCALAR_PTR_LITERAL(7, 2, 249, 136, 81, 124, 239, 75)}};
static const lean_object* l_Lean_Doc_parseFailureKind___closed__1 = (const lean_object*)&l_Lean_Doc_parseFailureKind___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_parseFailureKind = (const lean_object*)&l_Lean_Doc_parseFailureKind___closed__1_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Doc_longestBacktickRun___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Doc_longestBacktickRun___closed__0 = (const lean_object*)&l_Lean_Doc_longestBacktickRun___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_longestBacktickRun(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_longestBacktickRun___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(lean_object*, uint8_t, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Doc_versoCodeBoundarySpaces___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l_Lean_Doc_versoCodeBoundarySpaces___closed__0 = (const lean_object*)&l_Lean_Doc_versoCodeBoundarySpaces___closed__0_value;
static lean_once_cell_t l_Lean_Doc_versoCodeBoundarySpaces___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_versoCodeBoundarySpaces___closed__1;
LEAN_EXPORT uint8_t l_Lean_Doc_versoCodeBoundarySpaces(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeBoundarySpaces___boxed(lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0(uint32_t, lean_object*);
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoLinkUrl___closed__0___boxed__const__1;
static lean_once_cell_t l_Lean_Doc_escapeVersoLinkUrl___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_escapeVersoLinkUrl___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoLinkUrl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoLinkUrl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoImageAlt___closed__0___boxed__const__1;
static lean_once_cell_t l_Lean_Doc_escapeVersoImageAlt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_escapeVersoImageAlt___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoImageAlt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoImageAlt___boxed(lean_object*);
static lean_once_cell_t l_Lean_TSyntax_getVersoText___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_TSyntax_getVersoText___closed__0;
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoText(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoText___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoTextSource(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoTextSource___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoRefName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoRefName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkUrl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkUrl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkRefUrl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkRefUrl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoImageAlt(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoImageAlt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLine(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLine___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLines(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLines___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCode(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCode___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlockLines(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlockLines___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlock(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlock___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_VersoText_view(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_VersoText_view___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_VersoRefName_view(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_VersoRefName_view___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_VersoLinkUrl_view(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_VersoLinkUrl_view___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_VersoLinkRefUrl_view(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_VersoLinkRefUrl_view___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_VersoImageAlt_view(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_VersoImageAlt_view___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCodeLine_view(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCodeLine_view___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCode_view(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCode_view___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCodeBlock_view(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCodeBlock_view___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ArgVal.str"};
static const lean_object* l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__0_value;
static const lean_string_object l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "ArgVal"};
static const lean_object* l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(41, 57, 249, 217, 203, 152, 202, 12)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__2_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__4_value),LEAN_SCALAR_PTR_LITERAL(165, 66, 72, 255, 161, 123, 180, 197)}};
static const lean_object* l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__2 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_ArgVal_str___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_ArgVal_str___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_ArgVal_str___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_ArgVal_str___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_str___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_str___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_ArgVal_str___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_str___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_ArgVal_str = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_str___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ArgVal.ident"};
static const lean_object* l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(41, 57, 249, 217, 203, 152, 202, 12)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_arg__ident___closed__2_value),LEAN_SCALAR_PTR_LITERAL(46, 191, 138, 67, 72, 90, 15, 127)}};
static const lean_object* l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_ArgVal_ident___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_ArgVal_ident___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_ArgVal_ident___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_ArgVal_ident___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_ident___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_ArgVal_ident___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_ArgVal_ident = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ArgVal.num"};
static const lean_object* l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(41, 57, 249, 217, 203, 152, 202, 12)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_arg__num___closed__2_value),LEAN_SCALAR_PTR_LITERAL(233, 188, 228, 197, 246, 25, 189, 153)}};
static const lean_object* l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_ArgVal_num___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_ArgVal_num___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_ArgVal_num___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_ArgVal_num___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_num___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_num___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_ArgVal_num___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_ArgVal_num___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_num___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_ArgVal_num = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_num___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_argVal___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "argVal"};
static const lean_object* l_Lean_Doc_Parser_argVal___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_argVal___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_argVal___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_argVal___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_argVal___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_argVal___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_argVal___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_argVal___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_argVal___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_argVal___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 119, 50, 194, 18, 139, 234, 159)}};
static const lean_object* l_Lean_Doc_Parser_argVal___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_argVal___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_argVal___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_argVal___lam__0___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_argVal___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_argVal___lam__0___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_argVal___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_argVal___lam__0___closed__4;
static lean_once_cell_t l_Lean_Doc_Parser_argVal___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_argVal___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_argVal___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_argVal___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_argVal___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_argVal___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_argVal___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_argVal___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_argVal___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_argVal___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_argVal___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_argVal = (const lean_object*)&l_Lean_Doc_Parser_argVal___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_Arg_anon___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Arg"};
static const lean_object* l_Lean_Doc_Parser_Arg_anon___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Arg_anon___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_anon___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_anon___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_anon___lam__0___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_anon___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_anon___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 126, 223, 228, 215, 141, 22, 177)}};
static const lean_object* l_Lean_Doc_Parser_Arg_anon___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_anon___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_anon___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_anon___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Arg_anon___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_Arg_anon___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Arg_anon___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_anon___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Arg_anon___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Arg_anon___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Arg_anon___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Arg_anon___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Arg_anon = (const lean_object*)&l_Lean_Doc_Parser_Arg_anon___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named___lam__0___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named___lam__0___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named___lam__0___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named___lam__0___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named___lam__0___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named___lam__0___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named___lam__0___closed__0_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named___lam__0___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_named___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 213, 136, 95, 26, 15, 91, 243)}};
static const lean_object* l_Lean_Doc_Parser_Arg_named___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_named___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___lam__0___closed__1;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___lam__0___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___lam__0___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___lam__0___closed__4;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___lam__0___closed__5;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___lam__0___closed__6;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___lam__0___closed__7;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_named___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Arg_named___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_Arg_named___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Arg_named___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_named___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Arg_named___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Arg_named___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Arg_named___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Arg_named = (const lean_object*)&l_Lean_Doc_Parser_Arg_named___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__0_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_named__no__paren___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 130, 4, 13, 153, 240, 131, 1)}};
static const lean_object* l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__1;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_named__no__paren___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Arg_named__no__paren___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_Arg_named__no__paren___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Arg_named__no__paren___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named__no__paren___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Arg_named__no__paren___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Arg_named__no__paren = (const lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__0_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_flag__on___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 11, 92, 179, 92, 210, 69, 32)}};
static const lean_object* l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__1;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_flag__on___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Arg_flag__on___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_Arg_flag__on___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Arg_flag__on___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__on___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Arg_flag__on___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Arg_flag__on = (const lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__0_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_flag__off___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 14, 2, 143, 165, 169, 65, 229)}};
static const lean_object* l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__1;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_flag__off___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Arg_flag__off___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_Arg_flag__off___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Arg_flag__off___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__off___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Arg_flag__off___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Arg_flag__off = (const lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Parser_arg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "arg"};
static const lean_object* l_Lean_Doc_Parser_arg___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_arg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_arg___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_arg___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_arg___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_arg___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_arg___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_arg___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_arg___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_arg___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(190, 92, 75, 80, 50, 63, 75, 21)}};
static const lean_object* l_Lean_Doc_Parser_arg___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_arg___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_arg___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_arg___lam__0___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_arg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_arg___lam__0___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_arg___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_arg___lam__0___closed__4;
static lean_once_cell_t l_Lean_Doc_Parser_arg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_arg___lam__0___closed__5;
static lean_once_cell_t l_Lean_Doc_Parser_arg___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_arg___lam__0___closed__6;
static lean_once_cell_t l_Lean_Doc_Parser_arg___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_arg___lam__0___closed__7;
static lean_once_cell_t l_Lean_Doc_Parser_arg___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_arg___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_arg___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_arg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_arg___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_arg___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_arg___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_arg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_arg___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_arg___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_arg___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_arg = (const lean_object*)&l_Lean_Doc_Parser_arg___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "LinkTarget"};
static const lean_object* l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 244, 114, 61, 113, 148, 117, 178)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_url___closed__0_value),LEAN_SCALAR_PTR_LITERAL(57, 222, 147, 211, 241, 202, 7, 251)}};
static const lean_object* l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_LinkTarget_url___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_LinkTarget_url___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_LinkTarget_url___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_LinkTarget_url___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_url___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_LinkTarget_url___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_LinkTarget_url = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__0_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(13, 244, 114, 61, 113, 148, 117, 178)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_ref___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 54, 241, 38, 78, 206, 156, 5)}};
static const lean_object* l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__1;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__4;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_LinkTarget_ref___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_LinkTarget_ref___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_LinkTarget_ref___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_LinkTarget_ref___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_ref___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_LinkTarget_ref___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_LinkTarget_ref = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Parser_linkTarget___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "linkTarget"};
static const lean_object* l_Lean_Doc_Parser_linkTarget___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_linkTarget___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_linkTarget___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_linkTarget___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_linkTarget___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_linkTarget___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_linkTarget___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_linkTarget___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_linkTarget___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_linkTarget___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(134, 252, 192, 153, 19, 197, 24, 81)}};
static const lean_object* l_Lean_Doc_Parser_linkTarget___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_linkTarget___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_linkTarget___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_linkTarget___lam__0___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_linkTarget___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_linkTarget___lam__0___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_linkTarget___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_linkTarget___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_linkTarget___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_linkTarget___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_linkTarget___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_linkTarget___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_linkTarget___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_linkTarget___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_linkTarget___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_linkTarget___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_linkTarget___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_linkTarget = (const lean_object*)&l_Lean_Doc_Parser_linkTarget___closed__1_value;
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__1(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "one or more '"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___boxed(lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "'*', '-', or '+'"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__0_value;
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__3, .m_arity = 5, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__1_value),((lean_object*)&l_Lean_Doc_Parser_versoText___closed__2_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__0_value)} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__1_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__1_value)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__2_value;
LEAN_EXPORT const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___closed__2_value;
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0___boxed(lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1___boxed(lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "'.' or ')'"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "'0'-'9'"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "a number followed by '.' or ')'"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__0_value;
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__1_value;
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__1_value)} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__2_value;
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__0_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__2_value)} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__3 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__3_value;
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__3, .m_arity = 5, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__1_value),((lean_object*)&l_Lean_Doc_Parser_versoText___closed__2_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__3_value)} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__4 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__4_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__4_value)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__5 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__5_value;
LEAN_EXPORT const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__0(lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__1_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__0_value;
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__0_value)} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__1_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__1_value)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__2_value;
LEAN_EXPORT const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___closed__2_value;
static const lean_string_object l_Lean_Doc_Parser_headerMarker___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "headerMarker"};
static const lean_object* l_Lean_Doc_Parser_headerMarker___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_headerMarker___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_headerMarker___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_headerMarker___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_headerMarker___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_headerMarker___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_headerMarker___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_headerMarker___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_headerMarker___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_headerMarker___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 163, 210, 90, 152, 248, 144, 166)}};
static const lean_object* l_Lean_Doc_Parser_headerMarker___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_headerMarker___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_headerMarker___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_headerMarker___lam__0___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_headerMarker___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_headerMarker___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_headerMarker___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_headerMarker___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_headerMarker___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_headerMarker___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_headerMarker___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_headerMarker___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_headerMarker___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_headerMarker___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_headerMarker___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_headerMarker = (const lean_object*)&l_Lean_Doc_Parser_headerMarker___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_listMarker___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "listMarker"};
static const lean_object* l_Lean_Doc_Parser_listMarker___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_listMarker___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_listMarker___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_listMarker___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_listMarker___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_listMarker___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_listMarker___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_listMarker___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_listMarker___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_listMarker___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(220, 134, 18, 7, 181, 33, 85, 37)}};
static const lean_object* l_Lean_Doc_Parser_listMarker___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_listMarker___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_listMarker___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_listMarker___lam__0___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_listMarker___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_listMarker___lam__0___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_listMarker___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_listMarker___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_listMarker___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_listMarker___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_listMarker___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_listMarker___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_listMarker___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_listMarker___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_listMarker___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_listMarker___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_listMarker___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_listMarker = (const lean_object*)&l_Lean_Doc_Parser_listMarker___closed__1_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___lam__0(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___closed__1_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___lam__0(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___closed__1_value;
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0(uint32_t);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0___boxed(lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__0;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "':'"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__0_value;
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*3, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3, .m_arity = 5, .m_num_fixed = 3, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__1_value),((lean_object*)&l_Lean_Doc_Parser_versoText___closed__2_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__0_value)} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__1_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__1_value)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__2_value;
LEAN_EXPORT const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___closed__2_value;
static const lean_string_object l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "emphDelimiter"};
static const lean_object* l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(14, 57, 61, 189, 31, 180, 10, 101)}};
static const lean_object* l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_emphDelimiter___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_emphDelimiter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_emphDelimiter___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_emphDelimiter___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_emphDelimiter___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_emphDelimiter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_emphDelimiter___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_emphDelimiter___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_emphDelimiter___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_emphDelimiter = (const lean_object*)&l_Lean_Doc_Parser_emphDelimiter___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "boldDelimiter"};
static const lean_object* l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 9, 73, 54, 22, 222, 115, 214)}};
static const lean_object* l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_boldDelimiter___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_boldDelimiter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_boldDelimiter___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_boldDelimiter___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_boldDelimiter___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_boldDelimiter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_boldDelimiter___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_boldDelimiter___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_boldDelimiter___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_boldDelimiter = (const lean_object*)&l_Lean_Doc_Parser_boldDelimiter___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "codeDelimiter"};
static const lean_object* l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 116, 135, 82, 225, 37, 203, 104)}};
static const lean_object* l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_codeDelimiter___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_codeDelimiter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_codeDelimiter___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_codeDelimiter___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_codeDelimiter___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_codeDelimiter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_codeDelimiter___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_codeDelimiter___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_codeDelimiter___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_codeDelimiter = (const lean_object*)&l_Lean_Doc_Parser_codeDelimiter___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "codeBlockFence"};
static const lean_object* l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(197, 154, 39, 84, 226, 168, 56, 199)}};
static const lean_object* l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_codeBlockFence___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_codeBlockFence___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_codeBlockFence___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_codeBlockFence___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_codeBlockFence___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_codeBlockFence___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_codeBlockFence___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_codeBlockFence___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_codeBlockFence___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_codeBlockFence = (const lean_object*)&l_Lean_Doc_Parser_codeBlockFence___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "inlineMathMarker"};
static const lean_object* l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(102, 9, 108, 134, 130, 7, 90, 114)}};
static const lean_object* l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "$"};
static const lean_object* l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__2 = (const lean_object*)&l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_inlineMathMarker___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_inlineMathMarker___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_inlineMathMarker___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_inlineMathMarker___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_inlineMathMarker___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_inlineMathMarker___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_inlineMathMarker___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_inlineMathMarker___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_inlineMathMarker___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_inlineMathMarker = (const lean_object*)&l_Lean_Doc_Parser_inlineMathMarker___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "displayMathMarker"};
static const lean_object* l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(191, 18, 116, 40, 86, 165, 207, 150)}};
static const lean_object* l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "$$"};
static const lean_object* l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__2 = (const lean_object*)&l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_displayMathMarker___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_displayMathMarker___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_displayMathMarker___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_displayMathMarker___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_displayMathMarker___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_displayMathMarker___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_displayMathMarker___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_displayMathMarker___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_displayMathMarker___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_displayMathMarker = (const lean_object*)&l_Lean_Doc_Parser_displayMathMarker___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "directiveDelimiter"};
static const lean_object* l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(190, 28, 38, 38, 72, 11, 173, 25)}};
static const lean_object* l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_directiveDelimiter___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_directiveDelimiter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_directiveDelimiter___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_directiveDelimiter___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_directiveDelimiter___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_directiveDelimiter___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_directiveDelimiter___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_directiveDelimiter___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_directiveDelimiter___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_directiveDelimiter = (const lean_object*)&l_Lean_Doc_Parser_directiveDelimiter___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0(uint32_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "' to close what '"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "' opened"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Inline"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_code___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 30, 73, 79, 76, 254, 8, 196)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2___boxed__const__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__1_value),((lean_object*)&l_Lean_Doc_Parser_versoText___closed__2_value)} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_linebreak___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 150, 35, 119, 78, 160, 253, 84)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_image___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 170, 102, 209, 119, 14, 254, 233)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!["};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_footnote___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 121, 147, 210, 143, 103, 0, 217)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_inline__math___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 236, 9, 179, 133, 206, 252, 7)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_display__math___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 39, 73, 53, 10, 24, 181, 77)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_text___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 133, 107, 199, 31, 216, 160, 200)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1___boxed(lean_object*);
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__0_value;
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__1_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_bold___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 21, 54, 220, 135, 144, 211, 134)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__0_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___boxed__const__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_emph___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 215, 18, 85, 144, 91, 153, 50)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_link___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 237, 8, 103, 58, 149, 183, 251)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_inline_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(8, 108, 76, 164, 130, 208, 234, 146)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_role___closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 233, 178, 241, 96, 238, 218, 92)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__5 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__5_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__7;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Inline_text___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Inline_text___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Inline_text;
static const lean_closure_object l_Lean_Doc_Parser_Inline_emph___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Inline_emph___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Inline_emph___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Inline_emph___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Inline_emph___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Inline_emph___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Inline_emph___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Inline_emph = (const lean_object*)&l_Lean_Doc_Parser_Inline_emph___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Inline_bold___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Inline_bold___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Inline_bold___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Inline_bold___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Inline_bold___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Inline_bold___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Inline_bold___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Inline_bold = (const lean_object*)&l_Lean_Doc_Parser_Inline_bold___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1___boxed(lean_object*);
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Inline_code = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Inline_inline__math;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Inline_display__math;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Inline_link___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Inline_link___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Inline_link___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Inline_link___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Inline_link___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Inline_link___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Inline_link___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Inline_link = (const lean_object*)&l_Lean_Doc_Parser_Inline_link___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Inline_image___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Inline_image___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Inline_image;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Inline_footnote___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Inline_footnote___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Inline_footnote;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Inline_linebreak___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Inline_linebreak___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Inline_linebreak;
static const lean_closure_object l_Lean_Doc_Parser_Inline_role___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Inline_role___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Inline_role___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Inline_role___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Inline_role___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Inline_role___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Inline_role___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Inline_role = (const lean_object*)&l_Lean_Doc_Parser_Inline_role___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_inline___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_inline___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_inline___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_inline___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_inline___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_inline___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_inline___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_inline = (const lean_object*)&l_Lean_Doc_Parser_inline___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Block"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_para___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 167, 213, 66, 92, 160, 222, 146)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_command___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 232, 253, 29, 141, 75, 139, 21)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_metadata__block___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 125, 116, 48, 167, 45, 110, 42)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_link__ref___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 199, 233, 128, 119, 237, 18, 215)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_footnote__ref___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 53, 29, 246, 154, 171, 121, 154)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_header___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 176, 128, 73, 36, 235, 244, 141)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_codeblock___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 32, 43, 99, 217, 167, 97, 87)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_dl___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 15, 76, 66, 114, 120, 124, 74)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "DescItem.item"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "item"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__2_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DescItem"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__1_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(99, 70, 30, 3, 105, 156, 130, 115)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(37, 193, 144, 210, 183, 212, 114, 89)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_inline___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__3 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__3_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_ul___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 45, 1, 212, 241, 159, 201, 84)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ListItem.item"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ListItem"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__1_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(154, 153, 101, 209, 126, 16, 11, 208)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(200, 123, 16, 134, 76, 179, 171, 228)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_ol___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 199, 227, 191, 40, 60, 185, 243)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_blockquote___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 145, 178, 243, 42, 6, 105, 104)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value_aux_3),((lean_object*)&l_Lean_Doc_Syntax_directive___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 234, 1, 42, 159, 198, 19, 176)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot(lean_object*, lean_object*);
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5_value_aux_2),((lean_object*)&l_Lean_Doc_Syntax_block_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(183, 72, 202, 40, 103, 170, 246, 9)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_ListItem_item___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_listMarker___closed__1_value)} };
static const lean_object* l_Lean_Doc_Parser_ListItem_item___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_ListItem_item___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_ListItem_item___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_ListItem_item___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_ListItem_item___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_ListItem_item___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_ListItem_item = (const lean_object*)&l_Lean_Doc_Parser_ListItem_item___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_DescItem_item___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_DescItem_item___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_DescItem_item___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_DescItem_item___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_DescItem_item___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_DescItem_item___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_DescItem_item___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_DescItem_item = (const lean_object*)&l_Lean_Doc_Parser_DescItem_item___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Block_para___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Block_para___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Block_para;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Block_ul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Block_ul___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Block_ul___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Block_ul___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Block_ul___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Block_ul___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Block_ul___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Block_ul = (const lean_object*)&l_Lean_Doc_Parser_Block_ul___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Block_ol___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Block_ol___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Block_ol___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Block_ol___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Block_ol___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Block_ol___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Block_ol___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Block_ol = (const lean_object*)&l_Lean_Doc_Parser_Block_ol___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Block_dl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Block_dl___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Block_dl___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Block_dl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Block_dl___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Block_dl___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Block_dl___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Block_dl = (const lean_object*)&l_Lean_Doc_Parser_Block_dl___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Block_blockquote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Block_blockquote___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Block_blockquote___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Block_blockquote___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Block_blockquote___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Block_blockquote___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Block_blockquote___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Block_blockquote = (const lean_object*)&l_Lean_Doc_Parser_Block_blockquote___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Block_codeblock___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Block_codeblock___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Block_codeblock;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Block_directive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Block_directive___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Block_directive___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Block_directive___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Block_directive___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Block_directive___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Block_directive___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Block_directive = (const lean_object*)&l_Lean_Doc_Parser_Block_directive___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Block_header___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Block_header___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Block_header;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Block_link__ref___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Block_link__ref___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Block_link__ref;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Block_footnote__ref___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Block_footnote__ref___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Block_footnote__ref;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Block_metadata__block___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Block_metadata__block___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Block_metadata__block;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Block_command___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Block_command___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Block_command;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_block___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_block___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_block___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_block___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_block___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_block___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_block___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_block = (const lean_object*)&l_Lean_Doc_Parser_block___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_document___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "document"};
static const lean_object* l_Lean_Doc_Parser_document___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_document___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_document___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_document___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_document___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Syntax_arg__str___closed__0_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_document___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_document___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Syntax_arg__val_quot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_document___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_document___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_document___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(234, 113, 152, 229, 184, 253, 250, 127)}};
static const lean_object* l_Lean_Doc_Parser_document___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_document___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_document___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_document___lam__0___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_document___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_document___lam__0___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_document___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_document___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_document___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_document___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_document___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_document___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_document___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_document___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_document___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_document___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_document = (const lean_object*)&l_Lean_Doc_Parser_document___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoBlocks(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoBlocks___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoDelimiter(lean_object*);
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoDelimiter___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_VersoDocument_view(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_VersoDocument_view___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_VersoDelimiter_view(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_VersoDelimiter_view___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeVersoDocumentTSyntaxArrayConsSyntaxNodeKindMkStr4Nil___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_TSyntax_getVersoBlocks___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeVersoDocumentTSyntaxArrayConsSyntaxNodeKindMkStr4Nil___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeVersoDocumentTSyntaxArrayConsSyntaxNodeKindMkStr4Nil___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeVersoDocumentTSyntaxArrayConsSyntaxNodeKindMkStr4Nil = (const lean_object*)&l_Lean_Doc_instCoeVersoDocumentTSyntaxArrayConsSyntaxNodeKindMkStr4Nil___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__1 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__2 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__3 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__4 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__5 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__6 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__7 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__8 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__9 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__10 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__11 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__12 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__13 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__14 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__15 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__16 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__17 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__18 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__19 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__20 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__21 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean__22 = (const lean_object*)&l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___closed__0_value;
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___lam__0(lean_object* v_p_1376_, lean_object* v_c_1377_, lean_object* v_s_1378_){
_start:
{
lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v_fn_1381_; lean_object* v___x_1382_; 
v___x_1379_ = lean_box(0);
v___x_1380_ = lean_apply_1(v_p_1376_, v___x_1379_);
v_fn_1381_ = lean_ctor_get(v___x_1380_, 1);
lean_inc_ref(v_fn_1381_);
lean_dec_ref(v___x_1380_);
v___x_1382_ = lean_apply_2(v_fn_1381_, v_c_1377_, v_s_1378_);
return v___x_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse(lean_object* v_p_1387_){
_start:
{
lean_object* v___f_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___f_1388_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___lam__0), 3, 1);
lean_closure_set(v___f_1388_, 0, v_p_1387_);
v___x_1389_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___closed__1));
v___x_1390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
lean_ctor_set(v___x_1390_, 1, v___f_1388_);
return v___x_1390_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoText___lam__0___closed__2(void){
_start:
{
uint8_t v___x_1397_; uint8_t v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1397_ = 0;
v___x_1398_ = 1;
v___x_1399_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___lam__0___closed__1));
v___x_1400_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___lam__0___closed__0));
v___x_1401_ = l_Lean_Parser_mkAntiquot(v___x_1400_, v___x_1399_, v___x_1398_, v___x_1397_);
return v___x_1401_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoText___lam__0(lean_object* v_c_1402_, lean_object* v_s_1403_){
_start:
{
lean_object* v___x_1404_; lean_object* v_fn_1405_; lean_object* v___x_1406_; 
v___x_1404_ = lean_obj_once(&l_Lean_Doc_Parser_versoText___lam__0___closed__2, &l_Lean_Doc_Parser_versoText___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_versoText___lam__0___closed__2);
v_fn_1405_ = lean_ctor_get(v___x_1404_, 1);
lean_inc_ref(v_fn_1405_);
v___x_1406_ = lean_apply_2(v_fn_1405_, v_c_1402_, v_s_1403_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoText___lam__1(lean_object* v___y_1407_){
_start:
{
lean_inc(v___y_1407_);
return v___y_1407_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoText___lam__1___boxed(lean_object* v___y_1408_){
_start:
{
lean_object* v_res_1409_; 
v_res_1409_ = l_Lean_Doc_Parser_versoText___lam__1(v___y_1408_);
lean_dec(v___y_1408_);
return v_res_1409_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoText___lam__2(lean_object* v___y_1410_){
_start:
{
lean_inc_ref(v___y_1410_);
return v___y_1410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoText___lam__2___boxed(lean_object* v___y_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lean_Doc_Parser_versoText___lam__2(v___y_1411_);
lean_dec_ref(v___y_1411_);
return v_res_1412_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoRef___lam__0___closed__2(void){
_start:
{
uint8_t v___x_1430_; uint8_t v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1430_ = 0;
v___x_1431_ = 1;
v___x_1432_ = ((lean_object*)(l_Lean_Doc_Parser_versoRef___lam__0___closed__1));
v___x_1433_ = ((lean_object*)(l_Lean_Doc_Parser_versoRef___lam__0___closed__0));
v___x_1434_ = l_Lean_Parser_mkAntiquot(v___x_1433_, v___x_1432_, v___x_1431_, v___x_1430_);
return v___x_1434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoRef___lam__0(lean_object* v_c_1435_, lean_object* v_s_1436_){
_start:
{
lean_object* v___x_1437_; lean_object* v_fn_1438_; lean_object* v___x_1439_; 
v___x_1437_ = lean_obj_once(&l_Lean_Doc_Parser_versoRef___lam__0___closed__2, &l_Lean_Doc_Parser_versoRef___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_versoRef___lam__0___closed__2);
v_fn_1438_ = lean_ctor_get(v___x_1437_, 1);
lean_inc_ref(v_fn_1438_);
v___x_1439_ = lean_apply_2(v_fn_1438_, v_c_1435_, v_s_1436_);
return v___x_1439_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__2(void){
_start:
{
uint8_t v___x_1451_; uint8_t v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1451_ = 0;
v___x_1452_ = 1;
v___x_1453_ = ((lean_object*)(l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__1));
v___x_1454_ = ((lean_object*)(l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__0));
v___x_1455_ = l_Lean_Parser_mkAntiquot(v___x_1454_, v___x_1453_, v___x_1452_, v___x_1451_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoLinkUrl___lam__0(lean_object* v_c_1456_, lean_object* v_s_1457_){
_start:
{
lean_object* v___x_1458_; lean_object* v_fn_1459_; lean_object* v___x_1460_; 
v___x_1458_ = lean_obj_once(&l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__2, &l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__2);
v_fn_1459_ = lean_ctor_get(v___x_1458_, 1);
lean_inc_ref(v_fn_1459_);
v___x_1460_ = lean_apply_2(v_fn_1459_, v_c_1456_, v_s_1457_);
return v___x_1460_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__2(void){
_start:
{
uint8_t v___x_1472_; uint8_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; 
v___x_1472_ = 0;
v___x_1473_ = 1;
v___x_1474_ = ((lean_object*)(l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__1));
v___x_1475_ = ((lean_object*)(l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__0));
v___x_1476_ = l_Lean_Parser_mkAntiquot(v___x_1475_, v___x_1474_, v___x_1473_, v___x_1472_);
return v___x_1476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoLinkRefUrl___lam__0(lean_object* v_c_1477_, lean_object* v_s_1478_){
_start:
{
lean_object* v___x_1479_; lean_object* v_fn_1480_; lean_object* v___x_1481_; 
v___x_1479_ = lean_obj_once(&l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__2, &l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__2);
v_fn_1480_ = lean_ctor_get(v___x_1479_, 1);
lean_inc_ref(v_fn_1480_);
v___x_1481_ = lean_apply_2(v_fn_1480_, v_c_1477_, v_s_1478_);
return v___x_1481_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__2(void){
_start:
{
uint8_t v___x_1493_; uint8_t v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; lean_object* v___x_1497_; 
v___x_1493_ = 0;
v___x_1494_ = 1;
v___x_1495_ = ((lean_object*)(l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__1));
v___x_1496_ = ((lean_object*)(l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__0));
v___x_1497_ = l_Lean_Parser_mkAntiquot(v___x_1496_, v___x_1495_, v___x_1494_, v___x_1493_);
return v___x_1497_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoImageAlt___lam__0(lean_object* v_c_1498_, lean_object* v_s_1499_){
_start:
{
lean_object* v___x_1500_; lean_object* v_fn_1501_; lean_object* v___x_1502_; 
v___x_1500_ = lean_obj_once(&l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__2, &l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__2);
v_fn_1501_ = lean_ctor_get(v___x_1500_, 1);
lean_inc_ref(v_fn_1501_);
v___x_1502_ = lean_apply_2(v_fn_1501_, v_c_1498_, v_s_1499_);
return v___x_1502_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoCode___lam__0___closed__2(void){
_start:
{
uint8_t v___x_1514_; uint8_t v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1514_ = 0;
v___x_1515_ = 1;
v___x_1516_ = ((lean_object*)(l_Lean_Doc_Parser_versoCode___lam__0___closed__1));
v___x_1517_ = ((lean_object*)(l_Lean_Doc_Parser_versoCode___lam__0___closed__0));
v___x_1518_ = l_Lean_Parser_mkAntiquot(v___x_1517_, v___x_1516_, v___x_1515_, v___x_1514_);
return v___x_1518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoCode___lam__0(lean_object* v_c_1519_, lean_object* v_s_1520_){
_start:
{
lean_object* v___x_1521_; lean_object* v_fn_1522_; lean_object* v___x_1523_; 
v___x_1521_ = lean_obj_once(&l_Lean_Doc_Parser_versoCode___lam__0___closed__2, &l_Lean_Doc_Parser_versoCode___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_versoCode___lam__0___closed__2);
v_fn_1522_ = lean_ctor_get(v___x_1521_, 1);
lean_inc_ref(v_fn_1522_);
v___x_1523_ = lean_apply_2(v_fn_1522_, v_c_1519_, v_s_1520_);
return v___x_1523_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__2(void){
_start:
{
uint8_t v___x_1535_; uint8_t v___x_1536_; lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1535_ = 0;
v___x_1536_ = 1;
v___x_1537_ = ((lean_object*)(l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__1));
v___x_1538_ = ((lean_object*)(l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__0));
v___x_1539_ = l_Lean_Parser_mkAntiquot(v___x_1538_, v___x_1537_, v___x_1536_, v___x_1535_);
return v___x_1539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoCodeLine___lam__0(lean_object* v_c_1540_, lean_object* v_s_1541_){
_start:
{
lean_object* v___x_1542_; lean_object* v_fn_1543_; lean_object* v___x_1544_; 
v___x_1542_ = lean_obj_once(&l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__2, &l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__2);
v_fn_1543_ = lean_ctor_get(v___x_1542_, 1);
lean_inc_ref(v_fn_1543_);
v___x_1544_ = lean_apply_2(v_fn_1543_, v_c_1540_, v_s_1541_);
return v___x_1544_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__2(void){
_start:
{
uint8_t v___x_1556_; uint8_t v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1556_ = 0;
v___x_1557_ = 1;
v___x_1558_ = ((lean_object*)(l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__1));
v___x_1559_ = ((lean_object*)(l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__0));
v___x_1560_ = l_Lean_Parser_mkAntiquot(v___x_1559_, v___x_1558_, v___x_1557_, v___x_1556_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoCodeBlock___lam__0(lean_object* v_c_1561_, lean_object* v_s_1562_){
_start:
{
lean_object* v___x_1563_; lean_object* v_fn_1564_; lean_object* v___x_1565_; 
v___x_1563_ = lean_obj_once(&l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__2, &l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__2);
v_fn_1564_ = lean_ctor_get(v___x_1563_, 1);
lean_inc_ref(v_fn_1564_);
v___x_1565_ = lean_apply_2(v_fn_1564_, v_c_1561_, v_s_1562_);
return v___x_1565_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg(lean_object* v___x_1586_, lean_object* v_str_1587_, lean_object* v_a_1588_, lean_object* v_b_1589_){
_start:
{
uint8_t v_decide_1590_; 
v_decide_1590_ = lean_nat_dec_eq(v_a_1588_, v___x_1586_);
if (v_decide_1590_ == 0)
{
lean_object* v_fst_1591_; lean_object* v_snd_1592_; lean_object* v___x_1594_; uint8_t v_isShared_1595_; uint8_t v_isSharedCheck_1616_; 
v_fst_1591_ = lean_ctor_get(v_b_1589_, 0);
v_snd_1592_ = lean_ctor_get(v_b_1589_, 1);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_b_1589_);
if (v_isSharedCheck_1616_ == 0)
{
v___x_1594_ = v_b_1589_;
v_isShared_1595_ = v_isSharedCheck_1616_;
goto v_resetjp_1593_;
}
else
{
lean_inc(v_snd_1592_);
lean_inc(v_fst_1591_);
lean_dec(v_b_1589_);
v___x_1594_ = lean_box(0);
v_isShared_1595_ = v_isSharedCheck_1616_;
goto v_resetjp_1593_;
}
v_resetjp_1593_:
{
uint32_t v___x_1596_; lean_object* v___x_1597_; uint32_t v___x_1598_; uint8_t v___x_1599_; 
v___x_1596_ = lean_string_utf8_get_fast(v_str_1587_, v_a_1588_);
v___x_1597_ = lean_string_utf8_next_fast(v_str_1587_, v_a_1588_);
lean_dec(v_a_1588_);
v___x_1598_ = 96;
v___x_1599_ = lean_uint32_dec_eq(v___x_1596_, v___x_1598_);
if (v___x_1599_ == 0)
{
lean_object* v_best_1600_; lean_object* v___x_1602_; 
lean_dec(v_snd_1592_);
v_best_1600_ = lean_unsigned_to_nat(0u);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 1, v_best_1600_);
v___x_1602_ = v___x_1594_;
goto v_reusejp_1601_;
}
else
{
lean_object* v_reuseFailAlloc_1604_; 
v_reuseFailAlloc_1604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1604_, 0, v_fst_1591_);
lean_ctor_set(v_reuseFailAlloc_1604_, 1, v_best_1600_);
v___x_1602_ = v_reuseFailAlloc_1604_;
goto v_reusejp_1601_;
}
v_reusejp_1601_:
{
v_a_1588_ = v___x_1597_;
v_b_1589_ = v___x_1602_;
goto _start;
}
}
else
{
lean_object* v___x_1605_; lean_object* v___x_1606_; uint8_t v___x_1607_; 
v___x_1605_ = lean_unsigned_to_nat(1u);
v___x_1606_ = lean_nat_add(v_snd_1592_, v___x_1605_);
lean_dec(v_snd_1592_);
v___x_1607_ = lean_nat_dec_lt(v_fst_1591_, v___x_1606_);
if (v___x_1607_ == 0)
{
lean_object* v___x_1609_; 
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 1, v___x_1606_);
v___x_1609_ = v___x_1594_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1611_; 
v_reuseFailAlloc_1611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1611_, 0, v_fst_1591_);
lean_ctor_set(v_reuseFailAlloc_1611_, 1, v___x_1606_);
v___x_1609_ = v_reuseFailAlloc_1611_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
v_a_1588_ = v___x_1597_;
v_b_1589_ = v___x_1609_;
goto _start;
}
}
else
{
lean_object* v___x_1613_; 
lean_dec(v_fst_1591_);
lean_inc(v___x_1606_);
if (v_isShared_1595_ == 0)
{
lean_ctor_set(v___x_1594_, 1, v___x_1606_);
lean_ctor_set(v___x_1594_, 0, v___x_1606_);
v___x_1613_ = v___x_1594_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v___x_1606_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v___x_1606_);
v___x_1613_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
v_a_1588_ = v___x_1597_;
v_b_1589_ = v___x_1613_;
goto _start;
}
}
}
}
}
else
{
lean_dec(v_a_1588_);
return v_b_1589_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg___boxed(lean_object* v___x_1617_, lean_object* v_str_1618_, lean_object* v_a_1619_, lean_object* v_b_1620_){
_start:
{
lean_object* v_res_1621_; 
v_res_1621_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg(v___x_1617_, v_str_1618_, v_a_1619_, v_b_1620_);
lean_dec_ref(v_str_1618_);
lean_dec(v___x_1617_);
return v_res_1621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_longestBacktickRun(lean_object* v_str_1624_){
_start:
{
lean_object* v_best_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v_fst_1629_; 
v_best_1625_ = lean_unsigned_to_nat(0u);
v___x_1626_ = ((lean_object*)(l_Lean_Doc_longestBacktickRun___closed__0));
v___x_1627_ = lean_string_utf8_byte_size(v_str_1624_);
v___x_1628_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg(v___x_1627_, v_str_1624_, v_best_1625_, v___x_1626_);
v_fst_1629_ = lean_ctor_get(v___x_1628_, 0);
lean_inc(v_fst_1629_);
lean_dec_ref(v___x_1628_);
return v_fst_1629_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_longestBacktickRun___boxed(lean_object* v_str_1630_){
_start:
{
lean_object* v_res_1631_; 
v_res_1631_ = l_Lean_Doc_longestBacktickRun(v_str_1630_);
lean_dec_ref(v_str_1630_);
return v_res_1631_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0(lean_object* v___x_1632_, lean_object* v___x_1633_, lean_object* v_str_1634_, lean_object* v_inst_1635_, lean_object* v_R_1636_, lean_object* v_a_1637_, lean_object* v_b_1638_, lean_object* v_c_1639_){
_start:
{
lean_object* v___x_1640_; 
v___x_1640_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg(v___x_1633_, v_str_1634_, v_a_1637_, v_b_1638_);
return v___x_1640_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___boxed(lean_object* v___x_1641_, lean_object* v___x_1642_, lean_object* v_str_1643_, lean_object* v_inst_1644_, lean_object* v_R_1645_, lean_object* v_a_1646_, lean_object* v_b_1647_, lean_object* v_c_1648_){
_start:
{
lean_object* v_res_1649_; 
v_res_1649_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0(v___x_1641_, v___x_1642_, v_str_1643_, v_inst_1644_, v_R_1645_, v_a_1646_, v_b_1647_, v_c_1648_);
lean_dec_ref(v_str_1643_);
lean_dec(v___x_1642_);
lean_dec_ref(v___x_1641_);
return v_res_1649_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(lean_object* v_s_1650_, uint8_t v___x_1651_, lean_object* v_a_1652_, uint8_t v_b_1653_){
_start:
{
lean_object* v_str_1654_; lean_object* v_startInclusive_1655_; lean_object* v_endExclusive_1656_; lean_object* v___x_1657_; uint8_t v_decide_1658_; 
v_str_1654_ = lean_ctor_get(v_s_1650_, 0);
v_startInclusive_1655_ = lean_ctor_get(v_s_1650_, 1);
v_endExclusive_1656_ = lean_ctor_get(v_s_1650_, 2);
v___x_1657_ = lean_nat_sub(v_endExclusive_1656_, v_startInclusive_1655_);
v_decide_1658_ = lean_nat_dec_eq(v_a_1652_, v___x_1657_);
lean_dec(v___x_1657_);
if (v_decide_1658_ == 0)
{
lean_object* v___x_1659_; uint32_t v___x_1664_; uint32_t v___x_1665_; uint8_t v___x_1666_; 
v___x_1659_ = lean_nat_add(v_startInclusive_1655_, v_a_1652_);
lean_dec(v_a_1652_);
v___x_1664_ = lean_string_utf8_get_fast(v_str_1654_, v___x_1659_);
v___x_1665_ = 32;
v___x_1666_ = lean_uint32_dec_eq(v___x_1664_, v___x_1665_);
if (v___x_1666_ == 0)
{
if (v___x_1651_ == 0)
{
goto v___jp_1660_;
}
else
{
lean_dec(v___x_1659_);
return v___x_1651_;
}
}
else
{
goto v___jp_1660_;
}
v___jp_1660_:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = lean_string_utf8_next_fast(v_str_1654_, v___x_1659_);
lean_dec(v___x_1659_);
v___x_1662_ = lean_nat_sub(v___x_1661_, v_startInclusive_1655_);
v_a_1652_ = v___x_1662_;
v_b_1653_ = v_decide_1658_;
goto _start;
}
}
else
{
lean_dec(v_a_1652_);
return v_b_1653_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg___boxed(lean_object* v_s_1667_, lean_object* v___x_1668_, lean_object* v_a_1669_, lean_object* v_b_1670_){
_start:
{
uint8_t v___x_965__boxed_1671_; uint8_t v_b_boxed_1672_; uint8_t v_res_1673_; lean_object* v_r_1674_; 
v___x_965__boxed_1671_ = lean_unbox(v___x_1668_);
v_b_boxed_1672_ = lean_unbox(v_b_1670_);
v_res_1673_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(v_s_1667_, v___x_965__boxed_1671_, v_a_1669_, v_b_boxed_1672_);
lean_dec_ref(v_s_1667_);
v_r_1674_ = lean_box(v_res_1673_);
return v_r_1674_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0(uint8_t v___x_1675_, lean_object* v_s_1676_){
_start:
{
lean_object* v_searcher_1677_; uint8_t v___x_1678_; uint8_t v___x_1679_; 
v_searcher_1677_ = lean_unsigned_to_nat(0u);
v___x_1678_ = 0;
v___x_1679_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(v_s_1676_, v___x_1675_, v_searcher_1677_, v___x_1678_);
return v___x_1679_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0___boxed(lean_object* v___x_1680_, lean_object* v_s_1681_){
_start:
{
uint8_t v___x_988__boxed_1682_; uint8_t v_res_1683_; lean_object* v_r_1684_; 
v___x_988__boxed_1682_ = lean_unbox(v___x_1680_);
v_res_1683_ = l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0(v___x_988__boxed_1682_, v_s_1681_);
lean_dec_ref(v_s_1681_);
v_r_1684_ = lean_box(v_res_1683_);
return v_r_1684_;
}
}
static lean_object* _init_l_Lean_Doc_versoCodeBoundarySpaces___closed__1(void){
_start:
{
lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1686_ = ((lean_object*)(l_Lean_Doc_versoCodeBoundarySpaces___closed__0));
v___x_1687_ = lean_string_utf8_byte_size(v___x_1686_);
return v___x_1687_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_versoCodeBoundarySpaces(lean_object* v_str_1688_){
_start:
{
lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; 
v___x_1689_ = ((lean_object*)(l_Lean_Doc_versoCodeBoundarySpaces___closed__0));
v___x_1690_ = lean_string_utf8_byte_size(v_str_1688_);
v___x_1691_ = lean_obj_once(&l_Lean_Doc_versoCodeBoundarySpaces___closed__1, &l_Lean_Doc_versoCodeBoundarySpaces___closed__1_once, _init_l_Lean_Doc_versoCodeBoundarySpaces___closed__1);
v___x_1692_ = lean_nat_dec_le(v___x_1691_, v___x_1690_);
if (v___x_1692_ == 0)
{
lean_dec_ref(v_str_1688_);
return v___x_1692_;
}
else
{
lean_object* v___x_1693_; uint8_t v___x_1694_; 
v___x_1693_ = lean_unsigned_to_nat(0u);
v___x_1694_ = lean_string_memcmp(v_str_1688_, v___x_1689_, v___x_1693_, v___x_1693_, v___x_1691_);
if (v___x_1694_ == 0)
{
lean_dec_ref(v_str_1688_);
return v___x_1694_;
}
else
{
if (v___x_1692_ == 0)
{
lean_dec_ref(v_str_1688_);
return v___x_1692_;
}
else
{
lean_object* v___x_1695_; uint8_t v___x_1696_; 
v___x_1695_ = lean_nat_sub(v___x_1690_, v___x_1691_);
v___x_1696_ = lean_string_memcmp(v_str_1688_, v___x_1689_, v___x_1695_, v___x_1693_, v___x_1691_);
lean_dec(v___x_1695_);
if (v___x_1696_ == 0)
{
lean_dec_ref(v_str_1688_);
return v___x_1696_;
}
else
{
lean_object* v___x_1697_; uint8_t v___x_1698_; 
v___x_1697_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1697_, 0, v_str_1688_);
lean_ctor_set(v___x_1697_, 1, v___x_1693_);
lean_ctor_set(v___x_1697_, 2, v___x_1690_);
v___x_1698_ = l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0(v___x_1696_, v___x_1697_);
lean_dec_ref_known(v___x_1697_, 3);
return v___x_1698_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeBoundarySpaces___boxed(lean_object* v_str_1699_){
_start:
{
uint8_t v_res_1700_; lean_object* v_r_1701_; 
v_res_1700_ = l_Lean_Doc_versoCodeBoundarySpaces(v_str_1699_);
v_r_1701_ = lean_box(v_res_1700_);
return v_r_1701_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0(lean_object* v_s_1702_, uint8_t v___x_1703_, lean_object* v_inst_1704_, lean_object* v_R_1705_, lean_object* v_a_1706_, uint8_t v_b_1707_, lean_object* v_c_1708_){
_start:
{
uint8_t v___x_1709_; 
v___x_1709_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(v_s_1702_, v___x_1703_, v_a_1706_, v_b_1707_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___boxed(lean_object* v_s_1710_, lean_object* v___x_1711_, lean_object* v_inst_1712_, lean_object* v_R_1713_, lean_object* v_a_1714_, lean_object* v_b_1715_, lean_object* v_c_1716_){
_start:
{
uint8_t v___x_1024__boxed_1717_; uint8_t v_b_boxed_1718_; uint8_t v_res_1719_; lean_object* v_r_1720_; 
v___x_1024__boxed_1717_ = lean_unbox(v___x_1711_);
v_b_boxed_1718_ = lean_unbox(v_b_1715_);
v_res_1719_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0(v_s_1710_, v___x_1024__boxed_1717_, v_inst_1712_, v_R_1713_, v_a_1714_, v_b_boxed_1718_, v_c_1716_);
lean_dec_ref(v_s_1710_);
v_r_1720_ = lean_box(v_res_1719_);
return v_r_1720_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg(lean_object* v_str_1721_, lean_object* v_a_1722_){
_start:
{
lean_object* v_fst_1723_; lean_object* v_snd_1724_; lean_object* v___x_1726_; uint8_t v_isShared_1727_; uint8_t v_isSharedCheck_1751_; 
v_fst_1723_ = lean_ctor_get(v_a_1722_, 0);
v_snd_1724_ = lean_ctor_get(v_a_1722_, 1);
v_isSharedCheck_1751_ = !lean_is_exclusive(v_a_1722_);
if (v_isSharedCheck_1751_ == 0)
{
v___x_1726_ = v_a_1722_;
v_isShared_1727_ = v_isSharedCheck_1751_;
goto v_resetjp_1725_;
}
else
{
lean_inc(v_snd_1724_);
lean_inc(v_fst_1723_);
lean_dec(v_a_1722_);
v___x_1726_ = lean_box(0);
v_isShared_1727_ = v_isSharedCheck_1751_;
goto v_resetjp_1725_;
}
v_resetjp_1725_:
{
lean_object* v___x_1728_; uint8_t v_decide_1729_; 
v___x_1728_ = lean_string_utf8_byte_size(v_str_1721_);
v_decide_1729_ = lean_nat_dec_eq(v_snd_1724_, v___x_1728_);
if (v_decide_1729_ == 0)
{
uint32_t v___x_1730_; lean_object* v___x_1731_; uint32_t v___x_1737_; uint8_t v___x_1738_; 
v___x_1730_ = lean_string_utf8_get_fast(v_str_1721_, v_snd_1724_);
v___x_1731_ = lean_string_utf8_next_fast(v_str_1721_, v_snd_1724_);
lean_dec(v_snd_1724_);
v___x_1737_ = 92;
v___x_1738_ = lean_uint32_dec_eq(v___x_1730_, v___x_1737_);
if (v___x_1738_ == 0)
{
lean_object* v___x_1739_; lean_object* v___x_1740_; 
lean_del_object(v___x_1726_);
v___x_1739_ = lean_string_push(v_fst_1723_, v___x_1730_);
v___x_1740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1740_, 0, v___x_1739_);
lean_ctor_set(v___x_1740_, 1, v___x_1731_);
v_a_1722_ = v___x_1740_;
goto _start;
}
else
{
uint8_t v_decide_1742_; 
v_decide_1742_ = lean_nat_dec_eq(v___x_1731_, v___x_1728_);
if (v_decide_1742_ == 0)
{
if (v___x_1738_ == 0)
{
goto v___jp_1732_;
}
else
{
uint32_t v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
lean_del_object(v___x_1726_);
v___x_1743_ = lean_string_utf8_get_fast(v_str_1721_, v___x_1731_);
v___x_1744_ = lean_string_push(v_fst_1723_, v___x_1743_);
v___x_1745_ = lean_string_utf8_next_fast(v_str_1721_, v___x_1731_);
v___x_1746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1744_);
lean_ctor_set(v___x_1746_, 1, v___x_1745_);
v_a_1722_ = v___x_1746_;
goto _start;
}
}
else
{
goto v___jp_1732_;
}
}
v___jp_1732_:
{
lean_object* v___x_1734_; 
if (v_isShared_1727_ == 0)
{
lean_ctor_set(v___x_1726_, 1, v___x_1731_);
v___x_1734_ = v___x_1726_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1736_; 
v_reuseFailAlloc_1736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1736_, 0, v_fst_1723_);
lean_ctor_set(v_reuseFailAlloc_1736_, 1, v___x_1731_);
v___x_1734_ = v_reuseFailAlloc_1736_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
v_a_1722_ = v___x_1734_;
goto _start;
}
}
}
else
{
lean_object* v___x_1749_; 
if (v_isShared_1727_ == 0)
{
v___x_1749_ = v___x_1726_;
goto v_reusejp_1748_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v_fst_1723_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_snd_1724_);
v___x_1749_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1748_;
}
v_reusejp_1748_:
{
return v___x_1749_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg___boxed(lean_object* v_str_1752_, lean_object* v_a_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg(v_str_1752_, v_a_1753_);
lean_dec_ref(v_str_1752_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(lean_object* v_str_1759_){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v_fst_1762_; 
v___x_1760_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__1));
v___x_1761_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg(v_str_1759_, v___x_1760_);
v_fst_1762_ = lean_ctor_get(v___x_1761_, 0);
lean_inc(v_fst_1762_);
lean_dec_ref(v___x_1761_);
return v_fst_1762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___boxed(lean_object* v_str_1763_){
_start:
{
lean_object* v_res_1764_; 
v_res_1764_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v_str_1763_);
lean_dec_ref(v_str_1763_);
return v_res_1764_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0(lean_object* v_str_1765_, lean_object* v_inst_1766_, lean_object* v_a_1767_){
_start:
{
lean_object* v___x_1768_; 
v___x_1768_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg(v_str_1765_, v_a_1767_);
return v___x_1768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___boxed(lean_object* v_str_1769_, lean_object* v_inst_1770_, lean_object* v_a_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0(v_str_1769_, v_inst_1770_, v_a_1771_);
lean_dec_ref(v_str_1769_);
return v_res_1772_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0(uint32_t v_a_1773_, lean_object* v_x_1774_){
_start:
{
if (lean_obj_tag(v_x_1774_) == 0)
{
uint8_t v___x_1775_; 
v___x_1775_ = 0;
return v___x_1775_;
}
else
{
lean_object* v_head_1776_; lean_object* v_tail_1777_; uint32_t v___x_1778_; uint8_t v___x_1779_; 
v_head_1776_ = lean_ctor_get(v_x_1774_, 0);
v_tail_1777_ = lean_ctor_get(v_x_1774_, 1);
v___x_1778_ = lean_unbox_uint32(v_head_1776_);
v___x_1779_ = lean_uint32_dec_eq(v_a_1773_, v___x_1778_);
if (v___x_1779_ == 0)
{
v_x_1774_ = v_tail_1777_;
goto _start;
}
else
{
return v___x_1779_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0___boxed(lean_object* v_a_1781_, lean_object* v_x_1782_){
_start:
{
uint32_t v_a_boxed_1783_; uint8_t v_res_1784_; lean_object* v_r_1785_; 
v_a_boxed_1783_ = lean_unbox_uint32(v_a_1781_);
lean_dec(v_a_1781_);
v_res_1784_ = l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0(v_a_boxed_1783_, v_x_1782_);
lean_dec(v_x_1782_);
v_r_1785_ = lean_box(v_res_1784_);
return v_r_1785_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg(lean_object* v_delimiters_1786_, lean_object* v___x_1787_, lean_object* v_value_1788_, lean_object* v_a_1789_, lean_object* v_b_1790_){
_start:
{
uint8_t v_decide_1791_; 
v_decide_1791_ = lean_nat_dec_eq(v_a_1789_, v___x_1787_);
if (v_decide_1791_ == 0)
{
uint32_t v___x_1792_; lean_object* v___x_1793_; uint32_t v___x_1794_; uint8_t v___x_1799_; 
v___x_1792_ = lean_string_utf8_get_fast(v_value_1788_, v_a_1789_);
v___x_1793_ = lean_string_utf8_next_fast(v_value_1788_, v_a_1789_);
lean_dec(v_a_1789_);
v___x_1794_ = 92;
v___x_1799_ = lean_uint32_dec_eq(v___x_1792_, v___x_1794_);
if (v___x_1799_ == 0)
{
uint8_t v___x_1800_; 
v___x_1800_ = l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0(v___x_1792_, v_delimiters_1786_);
if (v___x_1800_ == 0)
{
lean_object* v___x_1801_; 
v___x_1801_ = lean_string_push(v_b_1790_, v___x_1792_);
v_a_1789_ = v___x_1793_;
v_b_1790_ = v___x_1801_;
goto _start;
}
else
{
goto v___jp_1795_;
}
}
else
{
goto v___jp_1795_;
}
v___jp_1795_:
{
lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1796_ = lean_string_push(v_b_1790_, v___x_1794_);
v___x_1797_ = lean_string_push(v___x_1796_, v___x_1792_);
v_a_1789_ = v___x_1793_;
v_b_1790_ = v___x_1797_;
goto _start;
}
}
else
{
lean_dec(v_a_1789_);
return v_b_1790_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg___boxed(lean_object* v_delimiters_1803_, lean_object* v___x_1804_, lean_object* v_value_1805_, lean_object* v_a_1806_, lean_object* v_b_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg(v_delimiters_1803_, v___x_1804_, v_value_1805_, v_a_1806_, v_b_1807_);
lean_dec_ref(v_value_1805_);
lean_dec(v___x_1804_);
lean_dec(v_delimiters_1803_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited(lean_object* v_delimiters_1809_, lean_object* v_value_1810_){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1811_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_1812_ = lean_string_utf8_byte_size(v_value_1810_);
v___x_1813_ = lean_unsigned_to_nat(0u);
v___x_1814_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg(v_delimiters_1809_, v___x_1812_, v_value_1810_, v___x_1813_, v___x_1811_);
return v___x_1814_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited___boxed(lean_object* v_delimiters_1815_, lean_object* v_value_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited(v_delimiters_1815_, v_value_1816_);
lean_dec_ref(v_value_1816_);
lean_dec(v_delimiters_1815_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1(lean_object* v_delimiters_1818_, lean_object* v___x_1819_, lean_object* v___x_1820_, lean_object* v_value_1821_, lean_object* v_inst_1822_, lean_object* v_R_1823_, lean_object* v_a_1824_, lean_object* v_b_1825_, lean_object* v_c_1826_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg(v_delimiters_1818_, v___x_1820_, v_value_1821_, v_a_1824_, v_b_1825_);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___boxed(lean_object* v_delimiters_1828_, lean_object* v___x_1829_, lean_object* v___x_1830_, lean_object* v_value_1831_, lean_object* v_inst_1832_, lean_object* v_R_1833_, lean_object* v_a_1834_, lean_object* v_b_1835_, lean_object* v_c_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1(v_delimiters_1828_, v___x_1829_, v___x_1830_, v_value_1831_, v_inst_1832_, v_R_1833_, v_a_1834_, v_b_1835_, v_c_1836_);
lean_dec_ref(v_value_1831_);
lean_dec(v___x_1830_);
lean_dec_ref(v___x_1829_);
lean_dec(v_delimiters_1828_);
return v_res_1837_;
}
}
static lean_object* _init_l_Lean_Doc_escapeVersoLinkUrl___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = 41;
v___x_1839_ = lean_box_uint32(v___x_1838_);
return v___x_1839_;
}
}
static lean_object* _init_l_Lean_Doc_escapeVersoLinkUrl___closed__0(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = lean_box(0);
v___x_1841_ = l_Lean_Doc_escapeVersoLinkUrl___closed__0___boxed__const__1;
v___x_1842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1842_, 0, v___x_1841_);
lean_ctor_set(v___x_1842_, 1, v___x_1840_);
return v___x_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoLinkUrl(lean_object* v_value_1843_){
_start:
{
lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1844_ = lean_obj_once(&l_Lean_Doc_escapeVersoLinkUrl___closed__0, &l_Lean_Doc_escapeVersoLinkUrl___closed__0_once, _init_l_Lean_Doc_escapeVersoLinkUrl___closed__0);
v___x_1845_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited(v___x_1844_, v_value_1843_);
return v___x_1845_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoLinkUrl___boxed(lean_object* v_value_1846_){
_start:
{
lean_object* v_res_1847_; 
v_res_1847_ = l_Lean_Doc_escapeVersoLinkUrl(v_value_1846_);
lean_dec_ref(v_value_1846_);
return v_res_1847_;
}
}
static lean_object* _init_l_Lean_Doc_escapeVersoImageAlt___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_1848_; lean_object* v___x_1849_; 
v___x_1848_ = 93;
v___x_1849_ = lean_box_uint32(v___x_1848_);
return v___x_1849_;
}
}
static lean_object* _init_l_Lean_Doc_escapeVersoImageAlt___closed__0(void){
_start:
{
lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = lean_box(0);
v___x_1851_ = l_Lean_Doc_escapeVersoImageAlt___closed__0___boxed__const__1;
v___x_1852_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1852_, 0, v___x_1851_);
lean_ctor_set(v___x_1852_, 1, v___x_1850_);
return v___x_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoImageAlt(lean_object* v_value_1853_){
_start:
{
lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1854_ = lean_obj_once(&l_Lean_Doc_escapeVersoImageAlt___closed__0, &l_Lean_Doc_escapeVersoImageAlt___closed__0_once, _init_l_Lean_Doc_escapeVersoImageAlt___closed__0);
v___x_1855_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited(v___x_1854_, v_value_1853_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoImageAlt___boxed(lean_object* v_value_1856_){
_start:
{
lean_object* v_res_1857_; 
v_res_1857_ = l_Lean_Doc_escapeVersoImageAlt(v_value_1856_);
lean_dec_ref(v_value_1856_);
return v_res_1857_;
}
}
static lean_object* _init_l_Lean_TSyntax_getVersoText___closed__0(void){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
v___x_1858_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_1859_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v___x_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoText(lean_object* v_s_1860_){
_start:
{
lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1861_ = ((lean_object*)(l_Lean_Doc_versoTextKind));
v___x_1862_ = l_Lean_Syntax_isLit_x3f(v___x_1861_, v_s_1860_);
if (lean_obj_tag(v___x_1862_) == 0)
{
lean_object* v___x_1863_; 
v___x_1863_ = lean_obj_once(&l_Lean_TSyntax_getVersoText___closed__0, &l_Lean_TSyntax_getVersoText___closed__0_once, _init_l_Lean_TSyntax_getVersoText___closed__0);
return v___x_1863_;
}
else
{
lean_object* v_val_1864_; lean_object* v___x_1865_; 
v_val_1864_ = lean_ctor_get(v___x_1862_, 0);
lean_inc(v_val_1864_);
lean_dec_ref_known(v___x_1862_, 1);
v___x_1865_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v_val_1864_);
lean_dec(v_val_1864_);
return v___x_1865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoText___boxed(lean_object* v_s_1866_){
_start:
{
lean_object* v_res_1867_; 
v_res_1867_ = l_Lean_TSyntax_getVersoText(v_s_1866_);
lean_dec(v_s_1866_);
return v_res_1867_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoTextSource(lean_object* v_s_1868_){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1869_ = ((lean_object*)(l_Lean_Doc_versoTextKind));
v___x_1870_ = l_Lean_Syntax_isLit_x3f(v___x_1869_, v_s_1868_);
if (lean_obj_tag(v___x_1870_) == 0)
{
lean_object* v___x_1871_; 
v___x_1871_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
return v___x_1871_;
}
else
{
lean_object* v_val_1872_; 
v_val_1872_ = lean_ctor_get(v___x_1870_, 0);
lean_inc(v_val_1872_);
lean_dec_ref_known(v___x_1870_, 1);
return v_val_1872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoTextSource___boxed(lean_object* v_s_1873_){
_start:
{
lean_object* v_res_1874_; 
v_res_1874_ = l_Lean_TSyntax_getVersoTextSource(v_s_1873_);
lean_dec(v_s_1873_);
return v_res_1874_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoRefName(lean_object* v_s_1875_){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; 
v___x_1876_ = ((lean_object*)(l_Lean_Doc_versoRefKind));
v___x_1877_ = l_Lean_Syntax_isLit_x3f(v___x_1876_, v_s_1875_);
if (lean_obj_tag(v___x_1877_) == 0)
{
lean_object* v___x_1878_; 
v___x_1878_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
return v___x_1878_;
}
else
{
lean_object* v_val_1879_; 
v_val_1879_ = lean_ctor_get(v___x_1877_, 0);
lean_inc(v_val_1879_);
lean_dec_ref_known(v___x_1877_, 1);
return v_val_1879_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoRefName___boxed(lean_object* v_s_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_Lean_TSyntax_getVersoRefName(v_s_1880_);
lean_dec(v_s_1880_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkUrl(lean_object* v_s_1882_){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1883_ = ((lean_object*)(l_Lean_Doc_versoLinkUrlKind));
v___x_1884_ = l_Lean_Syntax_isLit_x3f(v___x_1883_, v_s_1882_);
if (lean_obj_tag(v___x_1884_) == 0)
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_obj_once(&l_Lean_TSyntax_getVersoText___closed__0, &l_Lean_TSyntax_getVersoText___closed__0_once, _init_l_Lean_TSyntax_getVersoText___closed__0);
return v___x_1885_;
}
else
{
lean_object* v_val_1886_; lean_object* v___x_1887_; 
v_val_1886_ = lean_ctor_get(v___x_1884_, 0);
lean_inc(v_val_1886_);
lean_dec_ref_known(v___x_1884_, 1);
v___x_1887_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v_val_1886_);
lean_dec(v_val_1886_);
return v___x_1887_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkUrl___boxed(lean_object* v_s_1888_){
_start:
{
lean_object* v_res_1889_; 
v_res_1889_ = l_Lean_TSyntax_getVersoLinkUrl(v_s_1888_);
lean_dec(v_s_1888_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkRefUrl(lean_object* v_s_1890_){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; 
v___x_1891_ = ((lean_object*)(l_Lean_Doc_versoLinkRefUrlKind));
v___x_1892_ = l_Lean_Syntax_isLit_x3f(v___x_1891_, v_s_1890_);
if (lean_obj_tag(v___x_1892_) == 0)
{
lean_object* v___x_1893_; 
v___x_1893_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
return v___x_1893_;
}
else
{
lean_object* v_val_1894_; 
v_val_1894_ = lean_ctor_get(v___x_1892_, 0);
lean_inc(v_val_1894_);
lean_dec_ref_known(v___x_1892_, 1);
return v_val_1894_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkRefUrl___boxed(lean_object* v_s_1895_){
_start:
{
lean_object* v_res_1896_; 
v_res_1896_ = l_Lean_TSyntax_getVersoLinkRefUrl(v_s_1895_);
lean_dec(v_s_1895_);
return v_res_1896_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoImageAlt(lean_object* v_s_1897_){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1898_ = ((lean_object*)(l_Lean_Doc_versoImageAltKind));
v___x_1899_ = l_Lean_Syntax_isLit_x3f(v___x_1898_, v_s_1897_);
if (lean_obj_tag(v___x_1899_) == 0)
{
lean_object* v___x_1900_; 
v___x_1900_ = lean_obj_once(&l_Lean_TSyntax_getVersoText___closed__0, &l_Lean_TSyntax_getVersoText___closed__0_once, _init_l_Lean_TSyntax_getVersoText___closed__0);
return v___x_1900_;
}
else
{
lean_object* v_val_1901_; lean_object* v___x_1902_; 
v_val_1901_ = lean_ctor_get(v___x_1899_, 0);
lean_inc(v_val_1901_);
lean_dec_ref_known(v___x_1899_, 1);
v___x_1902_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v_val_1901_);
lean_dec(v_val_1901_);
return v___x_1902_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoImageAlt___boxed(lean_object* v_s_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_Lean_TSyntax_getVersoImageAlt(v_s_1903_);
lean_dec(v_s_1903_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLine(lean_object* v_s_1905_){
_start:
{
lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1906_ = ((lean_object*)(l_Lean_Doc_versoCodeLineKind));
v___x_1907_ = l_Lean_Syntax_isLit_x3f(v___x_1906_, v_s_1905_);
if (lean_obj_tag(v___x_1907_) == 0)
{
lean_object* v___x_1908_; 
v___x_1908_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
return v___x_1908_;
}
else
{
lean_object* v_val_1909_; 
v_val_1909_ = lean_ctor_get(v___x_1907_, 0);
lean_inc(v_val_1909_);
lean_dec_ref_known(v___x_1907_, 1);
return v_val_1909_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLine___boxed(lean_object* v_s_1910_){
_start:
{
lean_object* v_res_1911_; 
v_res_1911_ = l_Lean_TSyntax_getVersoCodeLine(v_s_1910_);
lean_dec(v_s_1910_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLines(lean_object* v_s_1912_){
_start:
{
lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1913_ = lean_unsigned_to_nat(0u);
v___x_1914_ = l_Lean_Syntax_getArg(v_s_1912_, v___x_1913_);
v___x_1915_ = l_Lean_Syntax_getArgs(v___x_1914_);
lean_dec(v___x_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLines___boxed(lean_object* v_s_1916_){
_start:
{
lean_object* v_res_1917_; 
v_res_1917_ = l_Lean_TSyntax_getVersoCodeLines(v_s_1916_);
lean_dec(v_s_1916_);
return v_res_1917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0(lean_object* v_as_1918_, size_t v_sz_1919_, size_t v_i_1920_, lean_object* v_b_1921_){
_start:
{
uint8_t v___x_1922_; 
v___x_1922_ = lean_usize_dec_lt(v_i_1920_, v_sz_1919_);
if (v___x_1922_ == 0)
{
return v_b_1921_;
}
else
{
lean_object* v_a_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; size_t v___x_1926_; size_t v___x_1927_; 
v_a_1923_ = lean_array_uget_borrowed(v_as_1918_, v_i_1920_);
v___x_1924_ = l_Lean_TSyntax_getVersoCodeLine(v_a_1923_);
v___x_1925_ = lean_string_append(v_b_1921_, v___x_1924_);
lean_dec_ref(v___x_1924_);
v___x_1926_ = ((size_t)1ULL);
v___x_1927_ = lean_usize_add(v_i_1920_, v___x_1926_);
v_i_1920_ = v___x_1927_;
v_b_1921_ = v___x_1925_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0___boxed(lean_object* v_as_1929_, lean_object* v_sz_1930_, lean_object* v_i_1931_, lean_object* v_b_1932_){
_start:
{
size_t v_sz_boxed_1933_; size_t v_i_boxed_1934_; lean_object* v_res_1935_; 
v_sz_boxed_1933_ = lean_unbox_usize(v_sz_1930_);
lean_dec(v_sz_1930_);
v_i_boxed_1934_ = lean_unbox_usize(v_i_1931_);
lean_dec(v_i_1931_);
v_res_1935_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0(v_as_1929_, v_sz_boxed_1933_, v_i_boxed_1934_, v_b_1932_);
lean_dec_ref(v_as_1929_);
return v_res_1935_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCode(lean_object* v_s_1936_){
_start:
{
lean_object* v_str_1937_; lean_object* v___x_1938_; size_t v_sz_1939_; size_t v___x_1940_; lean_object* v___x_1941_; 
v_str_1937_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_1938_ = l_Lean_TSyntax_getVersoCodeLines(v_s_1936_);
v_sz_1939_ = lean_array_size(v___x_1938_);
v___x_1940_ = ((size_t)0ULL);
v___x_1941_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0(v___x_1938_, v_sz_1939_, v___x_1940_, v_str_1937_);
lean_dec_ref(v___x_1938_);
return v___x_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCode___boxed(lean_object* v_s_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lean_TSyntax_getVersoCode(v_s_1942_);
lean_dec(v_s_1942_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlockLines(lean_object* v_s_1944_){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1945_ = lean_unsigned_to_nat(0u);
v___x_1946_ = l_Lean_Syntax_getArg(v_s_1944_, v___x_1945_);
v___x_1947_ = l_Lean_Syntax_getArgs(v___x_1946_);
lean_dec(v___x_1946_);
return v___x_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlockLines___boxed(lean_object* v_s_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_Lean_TSyntax_getVersoCodeBlockLines(v_s_1948_);
lean_dec(v_s_1948_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlock(lean_object* v_s_1950_){
_start:
{
lean_object* v_out_1951_; lean_object* v___x_1952_; size_t v_sz_1953_; size_t v___x_1954_; lean_object* v___x_1955_; 
v_out_1951_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_1952_ = l_Lean_TSyntax_getVersoCodeBlockLines(v_s_1950_);
v_sz_1953_ = lean_array_size(v___x_1952_);
v___x_1954_ = ((size_t)0ULL);
v___x_1955_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0(v___x_1952_, v_sz_1953_, v___x_1954_, v_out_1951_);
lean_dec_ref(v___x_1952_);
return v___x_1955_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlock___boxed(lean_object* v_s_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Lean_TSyntax_getVersoCodeBlock(v_s_1956_);
lean_dec(v_s_1956_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoText_view(lean_object* v_s_1958_){
_start:
{
lean_object* v___x_1959_; 
v___x_1959_ = l_Lean_TSyntax_getVersoText(v_s_1958_);
return v___x_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoText_view___boxed(lean_object* v_s_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_Doc_VersoText_view(v_s_1960_);
lean_dec(v_s_1960_);
return v_res_1961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoRefName_view(lean_object* v_s_1962_){
_start:
{
lean_object* v___x_1963_; 
v___x_1963_ = l_Lean_TSyntax_getVersoRefName(v_s_1962_);
return v___x_1963_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoRefName_view___boxed(lean_object* v_s_1964_){
_start:
{
lean_object* v_res_1965_; 
v_res_1965_ = l_Lean_Doc_VersoRefName_view(v_s_1964_);
lean_dec(v_s_1964_);
return v_res_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoLinkUrl_view(lean_object* v_s_1966_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_TSyntax_getVersoLinkUrl(v_s_1966_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoLinkUrl_view___boxed(lean_object* v_s_1968_){
_start:
{
lean_object* v_res_1969_; 
v_res_1969_ = l_Lean_Doc_VersoLinkUrl_view(v_s_1968_);
lean_dec(v_s_1968_);
return v_res_1969_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoLinkRefUrl_view(lean_object* v_s_1970_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = l_Lean_TSyntax_getVersoLinkRefUrl(v_s_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoLinkRefUrl_view___boxed(lean_object* v_s_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_Doc_VersoLinkRefUrl_view(v_s_1972_);
lean_dec(v_s_1972_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoImageAlt_view(lean_object* v_s_1974_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l_Lean_TSyntax_getVersoImageAlt(v_s_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoImageAlt_view___boxed(lean_object* v_s_1976_){
_start:
{
lean_object* v_res_1977_; 
v_res_1977_ = l_Lean_Doc_VersoImageAlt_view(v_s_1976_);
lean_dec(v_s_1976_);
return v_res_1977_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCodeLine_view(lean_object* v_s_1978_){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = l_Lean_TSyntax_getVersoCodeLine(v_s_1978_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCodeLine_view___boxed(lean_object* v_s_1980_){
_start:
{
lean_object* v_res_1981_; 
v_res_1981_ = l_Lean_Doc_VersoCodeLine_view(v_s_1980_);
lean_dec(v_s_1980_);
return v_res_1981_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCode_view(lean_object* v_s_1982_){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = l_Lean_TSyntax_getVersoCode(v_s_1982_);
return v___x_1983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCode_view___boxed(lean_object* v_s_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Lean_Doc_VersoCode_view(v_s_1984_);
lean_dec(v_s_1984_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCodeBlock_view(lean_object* v_s_1986_){
_start:
{
lean_object* v___x_1987_; 
v___x_1987_ = l_Lean_TSyntax_getVersoCodeBlock(v_s_1986_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCodeBlock_view___boxed(lean_object* v_s_1988_){
_start:
{
lean_object* v_res_1989_; 
v_res_1989_ = l_Lean_Doc_VersoCodeBlock_view(v_s_1988_);
lean_dec(v_s_1988_);
return v_res_1989_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__3(void){
_start:
{
uint8_t v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_1998_ = 0;
v___x_1999_ = l_Lean_Parser_strLit;
v___x_2000_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__2));
v___x_2001_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__0));
v___x_2002_ = l_Lean_Parser_nodeWithAntiquot(v___x_2001_, v___x_2000_, v___x_1999_, v___x_1998_);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_ArgVal_str___lam__0(lean_object* v_c_2003_, lean_object* v_s_2004_){
_start:
{
lean_object* v___x_2005_; lean_object* v_fn_2006_; lean_object* v___x_2007_; 
v___x_2005_ = lean_obj_once(&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__3, &l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__3);
v_fn_2006_ = lean_ctor_get(v___x_2005_, 1);
lean_inc_ref(v_fn_2006_);
v___x_2007_ = lean_apply_2(v_fn_2006_, v_c_2003_, v_s_2004_);
return v___x_2007_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__2(void){
_start:
{
uint8_t v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2020_ = 0;
v___x_2021_ = l_Lean_Parser_ident;
v___x_2022_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__1));
v___x_2023_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__0));
v___x_2024_ = l_Lean_Parser_nodeWithAntiquot(v___x_2023_, v___x_2022_, v___x_2021_, v___x_2020_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_ArgVal_ident___lam__0(lean_object* v_c_2025_, lean_object* v_s_2026_){
_start:
{
lean_object* v___x_2027_; lean_object* v_fn_2028_; lean_object* v___x_2029_; 
v___x_2027_ = lean_obj_once(&l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__2, &l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__2);
v_fn_2028_ = lean_ctor_get(v___x_2027_, 1);
lean_inc_ref(v_fn_2028_);
v___x_2029_ = lean_apply_2(v_fn_2028_, v_c_2025_, v_s_2026_);
return v___x_2029_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__2(void){
_start:
{
uint8_t v___x_2042_; lean_object* v___x_2043_; lean_object* v___x_2044_; lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2042_ = 0;
v___x_2043_ = l_Lean_Parser_numLit;
v___x_2044_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__1));
v___x_2045_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__0));
v___x_2046_ = l_Lean_Parser_nodeWithAntiquot(v___x_2045_, v___x_2044_, v___x_2043_, v___x_2042_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_ArgVal_num___lam__0(lean_object* v_c_2047_, lean_object* v_s_2048_){
_start:
{
lean_object* v___x_2049_; lean_object* v_fn_2050_; lean_object* v___x_2051_; 
v___x_2049_ = lean_obj_once(&l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__2, &l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__2);
v_fn_2050_ = lean_ctor_get(v___x_2049_, 1);
lean_inc_ref(v_fn_2050_);
v___x_2051_ = lean_apply_2(v_fn_2050_, v_c_2047_, v_s_2048_);
return v___x_2051_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_argVal___lam__0___closed__2(void){
_start:
{
uint8_t v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2063_ = 1;
v___x_2064_ = ((lean_object*)(l_Lean_Doc_Parser_argVal___lam__0___closed__1));
v___x_2065_ = ((lean_object*)(l_Lean_Doc_Parser_argVal___lam__0___closed__0));
v___x_2066_ = l_Lean_Parser_mkAntiquot(v___x_2065_, v___x_2064_, v___x_2063_, v___x_2063_);
return v___x_2066_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_argVal___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; 
v___x_2067_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_num));
v___x_2068_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_ident));
v___x_2069_ = l_Lean_Parser_orelse(v___x_2068_, v___x_2067_);
return v___x_2069_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_argVal___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; 
v___x_2070_ = lean_obj_once(&l_Lean_Doc_Parser_argVal___lam__0___closed__3, &l_Lean_Doc_Parser_argVal___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_argVal___lam__0___closed__3);
v___x_2071_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_str));
v___x_2072_ = l_Lean_Parser_orelse(v___x_2071_, v___x_2070_);
return v___x_2072_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_argVal___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2073_ = lean_obj_once(&l_Lean_Doc_Parser_argVal___lam__0___closed__4, &l_Lean_Doc_Parser_argVal___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_argVal___lam__0___closed__4);
v___x_2074_ = lean_obj_once(&l_Lean_Doc_Parser_argVal___lam__0___closed__2, &l_Lean_Doc_Parser_argVal___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_argVal___lam__0___closed__2);
v___x_2075_ = l_Lean_Parser_withAntiquot(v___x_2074_, v___x_2073_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_argVal___lam__0(lean_object* v_c_2076_, lean_object* v_s_2077_){
_start:
{
lean_object* v___x_2078_; lean_object* v_fn_2079_; lean_object* v___x_2080_; 
v___x_2078_ = lean_obj_once(&l_Lean_Doc_Parser_argVal___lam__0___closed__5, &l_Lean_Doc_Parser_argVal___lam__0___closed__5_once, _init_l_Lean_Doc_Parser_argVal___lam__0___closed__5);
v_fn_2079_ = lean_ctor_get(v___x_2078_, 1);
lean_inc_ref(v_fn_2079_);
v___x_2080_ = lean_apply_2(v_fn_2079_, v_c_2076_, v_s_2077_);
return v___x_2080_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_anon___lam__0___closed__2(void){
_start:
{
uint8_t v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2093_ = 0;
v___x_2094_ = ((lean_object*)(l_Lean_Doc_Parser_argVal));
v___x_2095_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_anon___lam__0___closed__1));
v___x_2096_ = ((lean_object*)(l_Lean_Doc_Syntax_anon___closed__0));
v___x_2097_ = l_Lean_Parser_nodeWithAntiquot(v___x_2096_, v___x_2095_, v___x_2094_, v___x_2093_);
return v___x_2097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_anon___lam__0(lean_object* v_c_2098_, lean_object* v_s_2099_){
_start:
{
lean_object* v___x_2100_; lean_object* v_fn_2101_; lean_object* v___x_2102_; 
v___x_2100_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__2, &l_Lean_Doc_Parser_Arg_anon___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_Arg_anon___lam__0___closed__2);
v_fn_2101_ = lean_ctor_get(v___x_2100_, 1);
lean_inc_ref(v_fn_2101_);
v___x_2102_ = lean_apply_2(v_fn_2101_, v_c_2098_, v_s_2099_);
return v___x_2102_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1(){
_start:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; 
v___x_2109_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_anon___lam__0___closed__1));
v___x_2110_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_anon___regBuiltin_Lean_Doc_Syntax_anon_docString__1___closed__0));
v___x_2111_ = l_Lean_addBuiltinDocString(v___x_2109_, v___x_2110_);
return v___x_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1___boxed(lean_object* v_a_2112_){
_start:
{
lean_object* v_res_2113_; 
v_res_2113_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1();
return v_res_2113_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = ((lean_object*)(l_Lean_Doc_Syntax_named___closed__2));
v___x_2121_ = l_Lean_Parser_symbol(v___x_2120_);
return v___x_2121_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
v___x_2122_ = ((lean_object*)(l_Lean_Doc_Syntax_named___closed__5));
v___x_2123_ = l_Lean_Parser_symbol(v___x_2122_);
return v___x_2123_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2124_; lean_object* v___x_2125_; 
v___x_2124_ = ((lean_object*)(l_Lean_Doc_Syntax_arg__val_quot___closed__13));
v___x_2125_ = l_Lean_Parser_symbol(v___x_2124_);
return v___x_2125_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; 
v___x_2126_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__3, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__3);
v___x_2127_ = ((lean_object*)(l_Lean_Doc_Parser_argVal));
v___x_2128_ = l_Lean_Parser_andthen(v___x_2127_, v___x_2126_);
return v___x_2128_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; 
v___x_2129_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__4, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__4);
v___x_2130_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__2, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__2);
v___x_2131_ = l_Lean_Parser_andthen(v___x_2130_, v___x_2129_);
return v___x_2131_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; 
v___x_2132_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__5, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__5_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__5);
v___x_2133_ = l_Lean_Parser_ident;
v___x_2134_ = l_Lean_Parser_andthen(v___x_2133_, v___x_2132_);
return v___x_2134_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; 
v___x_2135_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__6, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__6_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__6);
v___x_2136_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__1, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__1_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__1);
v___x_2137_ = l_Lean_Parser_andthen(v___x_2136_, v___x_2135_);
return v___x_2137_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__8(void){
_start:
{
uint8_t v___x_2138_; lean_object* v___x_2139_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2138_ = 0;
v___x_2139_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__7, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__7_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__7);
v___x_2140_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named___lam__0___closed__0));
v___x_2141_ = ((lean_object*)(l_Lean_Doc_Syntax_named___closed__0));
v___x_2142_ = l_Lean_Parser_nodeWithAntiquot(v___x_2141_, v___x_2140_, v___x_2139_, v___x_2138_);
return v___x_2142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_named___lam__0(lean_object* v_c_2143_, lean_object* v_s_2144_){
_start:
{
lean_object* v___x_2145_; lean_object* v_fn_2146_; lean_object* v___x_2147_; 
v___x_2145_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__8, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__8_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__8);
v_fn_2146_ = lean_ctor_get(v___x_2145_, 1);
lean_inc_ref(v_fn_2146_);
v___x_2147_ = lean_apply_2(v_fn_2146_, v_c_2143_, v_s_2144_);
return v___x_2147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1(){
_start:
{
lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2154_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named___lam__0___closed__0));
v___x_2155_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___closed__0));
v___x_2156_ = l_Lean_addBuiltinDocString(v___x_2154_, v___x_2155_);
return v___x_2156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1___boxed(lean_object* v_a_2157_){
_start:
{
lean_object* v_res_2158_; 
v_res_2158_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1();
return v_res_2158_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2165_; lean_object* v___x_2166_; lean_object* v___x_2167_; 
v___x_2165_ = ((lean_object*)(l_Lean_Doc_Parser_argVal));
v___x_2166_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__2, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__2);
v___x_2167_ = l_Lean_Parser_andthen(v___x_2166_, v___x_2165_);
return v___x_2167_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2168_; lean_object* v___x_2169_; lean_object* v___x_2170_; 
v___x_2168_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__1, &l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__1_once, _init_l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__1);
v___x_2169_ = l_Lean_Parser_ident;
v___x_2170_ = l_Lean_Parser_andthen(v___x_2169_, v___x_2168_);
return v___x_2170_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__3(void){
_start:
{
uint8_t v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2171_ = 0;
v___x_2172_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__2, &l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__2);
v___x_2173_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__0));
v___x_2174_ = ((lean_object*)(l_Lean_Doc_Syntax_named__no__paren___closed__0));
v___x_2175_ = l_Lean_Parser_nodeWithAntiquot(v___x_2174_, v___x_2173_, v___x_2172_, v___x_2171_);
return v___x_2175_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_named__no__paren___lam__0(lean_object* v_c_2176_, lean_object* v_s_2177_){
_start:
{
lean_object* v___x_2178_; lean_object* v_fn_2179_; lean_object* v___x_2180_; 
v___x_2178_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__3, &l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__3);
v_fn_2179_ = lean_ctor_get(v___x_2178_, 1);
lean_inc_ref(v_fn_2179_);
v___x_2180_ = lean_apply_2(v_fn_2179_, v_c_2176_, v_s_2177_);
return v___x_2180_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1(){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__0));
v___x_2188_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_named___regBuiltin_Lean_Doc_Syntax_named_docString__1___closed__0));
v___x_2189_ = l_Lean_addBuiltinDocString(v___x_2187_, v___x_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1___boxed(lean_object* v_a_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1();
return v_res_2191_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2198_ = ((lean_object*)(l_Lean_Doc_Syntax_flag__on___closed__2));
v___x_2199_ = l_Lean_Parser_symbol(v___x_2198_);
return v___x_2199_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = l_Lean_Parser_ident;
v___x_2201_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__1, &l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__1_once, _init_l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__1);
v___x_2202_ = l_Lean_Parser_andthen(v___x_2201_, v___x_2200_);
return v___x_2202_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__3(void){
_start:
{
uint8_t v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2203_ = 0;
v___x_2204_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__2, &l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__2);
v___x_2205_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__0));
v___x_2206_ = ((lean_object*)(l_Lean_Doc_Syntax_flag__on___closed__0));
v___x_2207_ = l_Lean_Parser_nodeWithAntiquot(v___x_2206_, v___x_2205_, v___x_2204_, v___x_2203_);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_flag__on___lam__0(lean_object* v_c_2208_, lean_object* v_s_2209_){
_start:
{
lean_object* v___x_2210_; lean_object* v_fn_2211_; lean_object* v___x_2212_; 
v___x_2210_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__3, &l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__3);
v_fn_2211_ = lean_ctor_get(v___x_2210_, 1);
lean_inc_ref(v_fn_2211_);
v___x_2212_ = lean_apply_2(v_fn_2211_, v_c_2208_, v_s_2209_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1(){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2219_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__0));
v___x_2220_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__on___regBuiltin_Lean_Doc_Syntax_flag__on_docString__1___closed__0));
v___x_2221_ = l_Lean_addBuiltinDocString(v___x_2219_, v___x_2220_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1___boxed(lean_object* v_a_2222_){
_start:
{
lean_object* v_res_2223_; 
v_res_2223_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1();
return v_res_2223_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = ((lean_object*)(l_Lean_Doc_Syntax_flag__off___closed__2));
v___x_2231_ = l_Lean_Parser_symbol(v___x_2230_);
return v___x_2231_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; 
v___x_2232_ = l_Lean_Parser_ident;
v___x_2233_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__1, &l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__1_once, _init_l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__1);
v___x_2234_ = l_Lean_Parser_andthen(v___x_2233_, v___x_2232_);
return v___x_2234_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__3(void){
_start:
{
uint8_t v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2235_ = 0;
v___x_2236_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__2, &l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__2);
v___x_2237_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__0));
v___x_2238_ = ((lean_object*)(l_Lean_Doc_Syntax_flag__off___closed__0));
v___x_2239_ = l_Lean_Parser_nodeWithAntiquot(v___x_2238_, v___x_2237_, v___x_2236_, v___x_2235_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_flag__off___lam__0(lean_object* v_c_2240_, lean_object* v_s_2241_){
_start:
{
lean_object* v___x_2242_; lean_object* v_fn_2243_; lean_object* v___x_2244_; 
v___x_2242_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__3, &l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__3);
v_fn_2243_ = lean_ctor_get(v___x_2242_, 1);
lean_inc_ref(v_fn_2243_);
v___x_2244_ = lean_apply_2(v_fn_2243_, v_c_2240_, v_s_2241_);
return v___x_2244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1(){
_start:
{
lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v___x_2251_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__0));
v___x_2252_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_flag__off___regBuiltin_Lean_Doc_Syntax_flag__off_docString__1___closed__0));
v___x_2253_ = l_Lean_addBuiltinDocString(v___x_2251_, v___x_2252_);
return v___x_2253_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1___boxed(lean_object* v_a_2254_){
_start:
{
lean_object* v_res_2255_; 
v_res_2255_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1();
return v_res_2255_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___lam__0___closed__2(void){
_start:
{
uint8_t v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v___x_2262_ = 1;
v___x_2263_ = ((lean_object*)(l_Lean_Doc_Parser_arg___lam__0___closed__1));
v___x_2264_ = ((lean_object*)(l_Lean_Doc_Parser_arg___lam__0___closed__0));
v___x_2265_ = l_Lean_Parser_mkAntiquot(v___x_2264_, v___x_2263_, v___x_2262_, v___x_2262_);
return v___x_2265_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; 
v___x_2266_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named__no__paren));
v___x_2267_ = l_Lean_Parser_atomic(v___x_2266_);
return v___x_2267_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2268_; lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2268_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_anon));
v___x_2269_ = lean_obj_once(&l_Lean_Doc_Parser_arg___lam__0___closed__3, &l_Lean_Doc_Parser_arg___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_arg___lam__0___closed__3);
v___x_2270_ = l_Lean_Parser_orelse(v___x_2269_, v___x_2268_);
return v___x_2270_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2271_ = lean_obj_once(&l_Lean_Doc_Parser_arg___lam__0___closed__4, &l_Lean_Doc_Parser_arg___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_arg___lam__0___closed__4);
v___x_2272_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__off));
v___x_2273_ = l_Lean_Parser_orelse(v___x_2272_, v___x_2271_);
return v___x_2273_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2274_ = lean_obj_once(&l_Lean_Doc_Parser_arg___lam__0___closed__5, &l_Lean_Doc_Parser_arg___lam__0___closed__5_once, _init_l_Lean_Doc_Parser_arg___lam__0___closed__5);
v___x_2275_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__on));
v___x_2276_ = l_Lean_Parser_orelse(v___x_2275_, v___x_2274_);
return v___x_2276_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2277_ = lean_obj_once(&l_Lean_Doc_Parser_arg___lam__0___closed__6, &l_Lean_Doc_Parser_arg___lam__0___closed__6_once, _init_l_Lean_Doc_Parser_arg___lam__0___closed__6);
v___x_2278_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named));
v___x_2279_ = l_Lean_Parser_orelse(v___x_2278_, v___x_2277_);
return v___x_2279_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = lean_obj_once(&l_Lean_Doc_Parser_arg___lam__0___closed__7, &l_Lean_Doc_Parser_arg___lam__0___closed__7_once, _init_l_Lean_Doc_Parser_arg___lam__0___closed__7);
v___x_2281_ = lean_obj_once(&l_Lean_Doc_Parser_arg___lam__0___closed__2, &l_Lean_Doc_Parser_arg___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_arg___lam__0___closed__2);
v___x_2282_ = l_Lean_Parser_withAntiquot(v___x_2281_, v___x_2280_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_arg___lam__0(lean_object* v_c_2283_, lean_object* v_s_2284_){
_start:
{
lean_object* v___x_2285_; lean_object* v_fn_2286_; lean_object* v___x_2287_; 
v___x_2285_ = lean_obj_once(&l_Lean_Doc_Parser_arg___lam__0___closed__8, &l_Lean_Doc_Parser_arg___lam__0___closed__8_once, _init_l_Lean_Doc_Parser_arg___lam__0___closed__8);
v_fn_2286_ = lean_ctor_get(v___x_2285_, 1);
lean_inc_ref(v_fn_2286_);
v___x_2287_ = lean_apply_2(v_fn_2286_, v_c_2283_, v_s_2284_);
return v___x_2287_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2300_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__3, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__3);
v___x_2301_ = ((lean_object*)(l_Lean_Doc_Parser_versoLinkUrl));
v___x_2302_ = l_Lean_Parser_andthen(v___x_2301_, v___x_2300_);
return v___x_2302_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2305_; 
v___x_2303_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__2, &l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__2);
v___x_2304_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__1, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__1_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__1);
v___x_2305_ = l_Lean_Parser_andthen(v___x_2304_, v___x_2303_);
return v___x_2305_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__4(void){
_start:
{
uint8_t v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2306_ = 0;
v___x_2307_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__3, &l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__3);
v___x_2308_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__1));
v___x_2309_ = ((lean_object*)(l_Lean_Doc_Syntax_url___closed__0));
v___x_2310_ = l_Lean_Parser_nodeWithAntiquot(v___x_2309_, v___x_2308_, v___x_2307_, v___x_2306_);
return v___x_2310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_LinkTarget_url___lam__0(lean_object* v_c_2311_, lean_object* v_s_2312_){
_start:
{
lean_object* v___x_2313_; lean_object* v_fn_2314_; lean_object* v___x_2315_; 
v___x_2313_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__4, &l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__4);
v_fn_2314_ = lean_ctor_get(v___x_2313_, 1);
lean_inc_ref(v_fn_2314_);
v___x_2315_ = lean_apply_2(v_fn_2314_, v_c_2311_, v_s_2312_);
return v___x_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1(){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2322_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__1));
v___x_2323_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_url___regBuiltin_Lean_Doc_Syntax_url_docString__1___closed__0));
v___x_2324_ = l_Lean_addBuiltinDocString(v___x_2322_, v___x_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1___boxed(lean_object* v_a_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1();
return v_res_2326_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__1(void){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2333_ = ((lean_object*)(l_Lean_Doc_Syntax_ref___closed__2));
v___x_2334_ = l_Lean_Parser_symbol(v___x_2333_);
return v___x_2334_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2335_ = ((lean_object*)(l_Lean_Doc_Syntax_ref___closed__5));
v___x_2336_ = l_Lean_Parser_symbol(v___x_2335_);
return v___x_2336_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2337_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__2, &l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__2);
v___x_2338_ = ((lean_object*)(l_Lean_Doc_Parser_versoRef));
v___x_2339_ = l_Lean_Parser_andthen(v___x_2338_, v___x_2337_);
return v___x_2339_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; 
v___x_2340_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__3, &l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__3);
v___x_2341_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__1, &l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__1_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__1);
v___x_2342_ = l_Lean_Parser_andthen(v___x_2341_, v___x_2340_);
return v___x_2342_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__5(void){
_start:
{
uint8_t v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; 
v___x_2343_ = 0;
v___x_2344_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__4, &l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__4);
v___x_2345_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__0));
v___x_2346_ = ((lean_object*)(l_Lean_Doc_Syntax_ref___closed__0));
v___x_2347_ = l_Lean_Parser_nodeWithAntiquot(v___x_2346_, v___x_2345_, v___x_2344_, v___x_2343_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_LinkTarget_ref___lam__0(lean_object* v_c_2348_, lean_object* v_s_2349_){
_start:
{
lean_object* v___x_2350_; lean_object* v_fn_2351_; lean_object* v___x_2352_; 
v___x_2350_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__5, &l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__5_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__5);
v_fn_2351_ = lean_ctor_get(v___x_2350_, 1);
lean_inc_ref(v_fn_2351_);
v___x_2352_ = lean_apply_2(v_fn_2351_, v_c_2348_, v_s_2349_);
return v___x_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1(){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2359_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__0));
v___x_2360_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ref___regBuiltin_Lean_Doc_Syntax_ref_docString__1___closed__0));
v___x_2361_ = l_Lean_addBuiltinDocString(v___x_2359_, v___x_2360_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1___boxed(lean_object* v_a_2362_){
_start:
{
lean_object* v_res_2363_; 
v_res_2363_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1();
return v_res_2363_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_linkTarget___lam__0___closed__2(void){
_start:
{
uint8_t v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2370_ = 1;
v___x_2371_ = ((lean_object*)(l_Lean_Doc_Parser_linkTarget___lam__0___closed__1));
v___x_2372_ = ((lean_object*)(l_Lean_Doc_Parser_linkTarget___lam__0___closed__0));
v___x_2373_ = l_Lean_Parser_mkAntiquot(v___x_2372_, v___x_2371_, v___x_2370_, v___x_2370_);
return v___x_2373_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_linkTarget___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; 
v___x_2374_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref));
v___x_2375_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_url));
v___x_2376_ = l_Lean_Parser_orelse(v___x_2375_, v___x_2374_);
return v___x_2376_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_linkTarget___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2377_ = lean_obj_once(&l_Lean_Doc_Parser_linkTarget___lam__0___closed__3, &l_Lean_Doc_Parser_linkTarget___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_linkTarget___lam__0___closed__3);
v___x_2378_ = lean_obj_once(&l_Lean_Doc_Parser_linkTarget___lam__0___closed__2, &l_Lean_Doc_Parser_linkTarget___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_linkTarget___lam__0___closed__2);
v___x_2379_ = l_Lean_Parser_withAntiquot(v___x_2378_, v___x_2377_);
return v___x_2379_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_linkTarget___lam__0(lean_object* v_c_2380_, lean_object* v_s_2381_){
_start:
{
lean_object* v___x_2382_; lean_object* v_fn_2383_; lean_object* v___x_2384_; 
v___x_2382_ = lean_obj_once(&l_Lean_Doc_Parser_linkTarget___lam__0___closed__4, &l_Lean_Doc_Parser_linkTarget___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_linkTarget___lam__0___closed__4);
v_fn_2383_ = lean_ctor_get(v___x_2382_, 1);
lean_inc_ref(v_fn_2383_);
v___x_2384_ = lean_apply_2(v_fn_2383_, v_c_2380_, v_s_2381_);
return v___x_2384_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(lean_object* v_x_2390_, lean_object* v_x_2391_){
_start:
{
if (lean_obj_tag(v_x_2390_) == 0)
{
if (lean_obj_tag(v_x_2391_) == 0)
{
uint8_t v___x_2392_; 
v___x_2392_ = 1;
return v___x_2392_;
}
else
{
uint8_t v___x_2393_; 
v___x_2393_ = 0;
return v___x_2393_;
}
}
else
{
if (lean_obj_tag(v_x_2391_) == 0)
{
uint8_t v___x_2394_; 
v___x_2394_ = 0;
return v___x_2394_;
}
else
{
lean_object* v_val_2395_; lean_object* v_val_2396_; uint8_t v___x_2397_; 
v_val_2395_ = lean_ctor_get(v_x_2390_, 0);
v_val_2396_ = lean_ctor_get(v_x_2391_, 0);
v___x_2397_ = l_Lean_Parser_instBEqError_beq(v_val_2395_, v_val_2396_);
return v___x_2397_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1___boxed(lean_object* v_x_2398_, lean_object* v_x_2399_){
_start:
{
uint8_t v_res_2400_; lean_object* v_r_2401_; 
v_res_2400_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_x_2398_, v_x_2399_);
lean_dec(v_x_2399_);
lean_dec(v_x_2398_);
v_r_2401_ = lean_box(v_res_2400_);
return v_r_2401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0(lean_object* v_x_2402_, lean_object* v_st_2403_){
_start:
{
lean_inc_ref(v_st_2403_);
return v_st_2403_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0___boxed(lean_object* v_x_2404_, lean_object* v_st_2405_){
_start:
{
lean_object* v_res_2406_; 
v_res_2406_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0(v_x_2404_, v_st_2405_);
lean_dec_ref(v_st_2405_);
lean_dec_ref(v_x_2404_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__2(lean_object* v_x_2407_, lean_object* v___f_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v___x_2411_; 
v___x_2411_ = l_Lean_Parser_andthenFn(v_x_2407_, v___f_2408_, v___y_2409_, v___y_2410_);
return v___x_2411_;
}
}
LEAN_EXPORT uint8_t l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__0(uint32_t v_head_2412_, uint32_t v_x_2413_){
_start:
{
uint8_t v___x_2414_; 
v___x_2414_ = lean_uint32_dec_eq(v_x_2413_, v_head_2412_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__0___boxed(lean_object* v_head_2415_, lean_object* v_x_2416_){
_start:
{
uint32_t v_head_310__boxed_2417_; uint32_t v_x_311__boxed_2418_; uint8_t v_res_2419_; lean_object* v_r_2420_; 
v_head_310__boxed_2417_ = lean_unbox_uint32(v_head_2415_);
lean_dec(v_head_2415_);
v_x_311__boxed_2418_ = lean_unbox_uint32(v_x_2416_);
lean_dec(v_x_2416_);
v_res_2419_ = l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__0(v_head_310__boxed_2417_, v_x_311__boxed_2418_);
v_r_2420_ = lean_box(v_res_2419_);
return v_r_2420_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__1(uint32_t v_head_2421_, lean_object* v___f_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_){
_start:
{
lean_object* v___x_2425_; lean_object* v___x_2426_; lean_object* v___x_2427_; 
v___x_2425_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_2426_ = lean_string_push(v___x_2425_, v_head_2421_);
v___x_2427_ = l_Lean_Parser_satisfyFn(v___f_2422_, v___x_2426_, v___y_2423_, v___y_2424_);
return v___x_2427_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__1___boxed(lean_object* v_head_2428_, lean_object* v___f_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
uint32_t v_head_319__boxed_2432_; lean_object* v_res_2433_; 
v_head_319__boxed_2432_ = lean_unbox_uint32(v_head_2428_);
lean_dec(v_head_2428_);
v_res_2433_ = l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__1(v_head_319__boxed_2432_, v___f_2429_, v___y_2430_, v___y_2431_);
lean_dec_ref(v___y_2430_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0(lean_object* v_x_2434_, lean_object* v_x_2435_, lean_object* v___y_2436_, lean_object* v___y_2437_){
_start:
{
if (lean_obj_tag(v_x_2435_) == 0)
{
lean_object* v___x_2438_; 
v___x_2438_ = lean_apply_2(v_x_2434_, v___y_2436_, v___y_2437_);
return v___x_2438_;
}
else
{
lean_object* v_head_2439_; lean_object* v_tail_2440_; lean_object* v___f_2441_; lean_object* v___f_2442_; lean_object* v___f_2443_; 
v_head_2439_ = lean_ctor_get(v_x_2435_, 0);
lean_inc_n(v_head_2439_, 2);
v_tail_2440_ = lean_ctor_get(v_x_2435_, 1);
lean_inc(v_tail_2440_);
lean_dec_ref_known(v_x_2435_, 2);
v___f_2441_ = lean_alloc_closure((void*)(l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2441_, 0, v_head_2439_);
v___f_2442_ = lean_alloc_closure((void*)(l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2442_, 0, v_head_2439_);
lean_closure_set(v___f_2442_, 1, v___f_2441_);
v___f_2443_ = lean_alloc_closure((void*)(l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___lam__2), 4, 2);
lean_closure_set(v___f_2443_, 0, v_x_2434_);
lean_closure_set(v___f_2443_, 1, v___f_2442_);
v_x_2434_ = v___f_2443_;
v_x_2435_ = v_tail_2440_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1(lean_object* v_s_2446_, lean_object* v___f_2447_, lean_object* v_c_2448_, lean_object* v_st_2449_){
_start:
{
lean_object* v___x_2450_; lean_object* v_st_x27_2451_; lean_object* v_errorMsg_2452_; lean_object* v___x_2453_; uint8_t v___x_2454_; 
lean_inc_ref(v_s_2446_);
v___x_2450_ = lean_string_data(v_s_2446_);
lean_inc_ref(v_st_2449_);
v_st_x27_2451_ = l_List_foldl___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0(v___f_2447_, v___x_2450_, v_c_2448_, v_st_2449_);
v_errorMsg_2452_ = lean_ctor_get(v_st_x27_2451_, 4);
lean_inc(v_errorMsg_2452_);
v___x_2453_ = lean_box(0);
v___x_2454_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_2452_, v___x_2453_);
lean_dec(v_errorMsg_2452_);
if (v___x_2454_ == 0)
{
lean_object* v_pos_2455_; lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; lean_object* v___x_2459_; 
v_pos_2455_ = lean_ctor_get(v_st_2449_, 2);
lean_inc(v_pos_2455_);
lean_dec_ref(v_st_2449_);
v___x_2456_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0));
v___x_2457_ = lean_string_append(v___x_2456_, v_s_2446_);
lean_dec_ref(v_s_2446_);
v___x_2458_ = lean_string_append(v___x_2457_, v___x_2456_);
v___x_2459_ = l_Lean_Parser_ParserState_mkErrorAt(v_st_x27_2451_, v___x_2458_, v_pos_2455_, v___x_2453_);
return v___x_2459_;
}
else
{
lean_dec_ref(v_st_2449_);
lean_dec_ref(v_s_2446_);
return v_st_x27_2451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(lean_object* v_s_2461_){
_start:
{
lean_object* v___f_2462_; lean_object* v___f_2463_; lean_object* v___x_2464_; uint8_t v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; lean_object* v___x_2468_; lean_object* v___x_2469_; 
v___f_2462_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__0));
v___f_2463_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1), 4, 2);
lean_closure_set(v___f_2463_, 0, v_s_2461_);
lean_closure_set(v___f_2463_, 1, v___f_2462_);
v___x_2464_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2465_ = 1;
v___x_2466_ = lean_box(v___x_2465_);
v___x_2467_ = lean_alloc_closure((void*)(l_Lean_Parser_rawFn___boxed), 4, 2);
lean_closure_set(v___x_2467_, 0, v___f_2463_);
lean_closure_set(v___x_2467_, 1, v___x_2466_);
v___x_2468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2468_, 0, v___x_2464_);
lean_ctor_set(v___x_2468_, 1, v___x_2467_);
v___x_2469_ = l_Lean_Parser_tokenWithAntiquot(v___x_2468_);
return v___x_2469_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0(uint32_t v_ch_2470_, uint32_t v_x_2471_){
_start:
{
uint8_t v___x_2472_; 
v___x_2472_ = lean_uint32_dec_eq(v_x_2471_, v_ch_2470_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0___boxed(lean_object* v_ch_2473_, lean_object* v_x_2474_){
_start:
{
uint32_t v_ch_boxed_2475_; uint32_t v_x_149__boxed_2476_; uint8_t v_res_2477_; lean_object* v_r_2478_; 
v_ch_boxed_2475_ = lean_unbox_uint32(v_ch_2473_);
lean_dec(v_ch_2473_);
v_x_149__boxed_2476_ = lean_unbox_uint32(v_x_2474_);
lean_dec(v_x_2474_);
v_res_2477_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0(v_ch_boxed_2475_, v_x_149__boxed_2476_);
v_r_2478_ = lean_box(v_res_2477_);
return v_r_2478_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1(uint32_t v_ch_2480_, lean_object* v___f_2481_, lean_object* v_c_2482_, lean_object* v_st_2483_){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v_st_x27_2489_; lean_object* v_errorMsg_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; 
v___x_2484_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0));
v___x_2485_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_2486_ = lean_string_push(v___x_2485_, v_ch_2480_);
v___x_2487_ = lean_string_append(v___x_2484_, v___x_2486_);
v___x_2488_ = lean_string_append(v___x_2487_, v___x_2484_);
lean_inc_ref(v_st_2483_);
v_st_x27_2489_ = l_Lean_Parser_takeWhile1Fn(v___f_2481_, v___x_2488_, v_c_2482_, v_st_2483_);
v_errorMsg_2490_ = lean_ctor_get(v_st_x27_2489_, 4);
lean_inc(v_errorMsg_2490_);
v___x_2491_ = lean_box(0);
v___x_2492_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_2490_, v___x_2491_);
lean_dec(v_errorMsg_2490_);
if (v___x_2492_ == 0)
{
lean_object* v_pos_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; 
v_pos_2493_ = lean_ctor_get(v_st_2483_, 2);
lean_inc(v_pos_2493_);
lean_dec_ref(v_st_2483_);
v___x_2494_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___closed__0));
v___x_2495_ = lean_string_append(v___x_2494_, v___x_2486_);
lean_dec_ref(v___x_2486_);
v___x_2496_ = lean_string_append(v___x_2495_, v___x_2484_);
v___x_2497_ = l_Lean_Parser_ParserState_mkErrorAt(v_st_x27_2489_, v___x_2496_, v_pos_2493_, v___x_2491_);
return v___x_2497_;
}
else
{
lean_dec_ref(v___x_2486_);
lean_dec_ref(v_st_2483_);
return v_st_x27_2489_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___boxed(lean_object* v_ch_2498_, lean_object* v___f_2499_, lean_object* v_c_2500_, lean_object* v_st_2501_){
_start:
{
uint32_t v_ch_boxed_2502_; lean_object* v_res_2503_; 
v_ch_boxed_2502_ = lean_unbox_uint32(v_ch_2498_);
lean_dec(v_ch_2498_);
v_res_2503_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1(v_ch_boxed_2502_, v___f_2499_, v_c_2500_, v_st_2501_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(uint32_t v_ch_2504_){
_start:
{
lean_object* v___x_2505_; lean_object* v___f_2506_; lean_object* v___x_2507_; lean_object* v___f_2508_; lean_object* v___x_2509_; uint8_t v___x_2510_; lean_object* v___x_2511_; lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; 
v___x_2505_ = lean_box_uint32(v_ch_2504_);
v___f_2506_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2506_, 0, v___x_2505_);
v___x_2507_ = lean_box_uint32(v_ch_2504_);
v___f_2508_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___boxed), 4, 2);
lean_closure_set(v___f_2508_, 0, v___x_2507_);
lean_closure_set(v___f_2508_, 1, v___f_2506_);
v___x_2509_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2510_ = 1;
v___x_2511_ = lean_box(v___x_2510_);
v___x_2512_ = lean_alloc_closure((void*)(l_Lean_Parser_rawFn___boxed), 4, 2);
lean_closure_set(v___x_2512_, 0, v___f_2508_);
lean_closure_set(v___x_2512_, 1, v___x_2511_);
v___x_2513_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2513_, 0, v___x_2509_);
lean_ctor_set(v___x_2513_, 1, v___x_2512_);
v___x_2514_ = l_Lean_Parser_tokenWithAntiquot(v___x_2513_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___boxed(lean_object* v_ch_2515_){
_start:
{
uint32_t v_ch_boxed_2516_; lean_object* v_res_2517_; 
v_ch_boxed_2516_ = lean_unbox_uint32(v_ch_2515_);
lean_dec(v_ch_2515_);
v_res_2517_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v_ch_boxed_2516_);
return v_res_2517_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0(lean_object* v_c_2519_, lean_object* v_s_2520_){
_start:
{
lean_object* v_toInputContext_2521_; lean_object* v_pos_2522_; uint8_t v___x_2523_; 
v_toInputContext_2521_ = lean_ctor_get(v_c_2519_, 0);
v_pos_2522_ = lean_ctor_get(v_s_2520_, 2);
v___x_2523_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_2521_, v_pos_2522_);
if (v___x_2523_ == 0)
{
lean_object* v_inputString_2524_; uint32_t v_ch_2525_; uint32_t v___x_2526_; uint8_t v___x_2527_; 
lean_inc(v_pos_2522_);
v_inputString_2524_ = lean_ctor_get(v_toInputContext_2521_, 0);
v_ch_2525_ = lean_string_utf8_get_fast(v_inputString_2524_, v_pos_2522_);
v___x_2526_ = 42;
v___x_2527_ = lean_uint32_dec_eq(v_ch_2525_, v___x_2526_);
if (v___x_2527_ == 0)
{
uint32_t v___x_2528_; uint8_t v___x_2529_; 
v___x_2528_ = 45;
v___x_2529_ = lean_uint32_dec_eq(v_ch_2525_, v___x_2528_);
if (v___x_2529_ == 0)
{
uint32_t v___x_2530_; uint8_t v___x_2531_; 
v___x_2530_ = 43;
v___x_2531_ = lean_uint32_dec_eq(v_ch_2525_, v___x_2530_);
if (v___x_2531_ == 0)
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2532_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0___closed__0));
v___x_2533_ = lean_box(0);
v___x_2534_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_2520_, v___x_2532_, v_pos_2522_, v___x_2533_);
return v___x_2534_;
}
else
{
lean_object* v___x_2535_; 
v___x_2535_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2520_, v_c_2519_, v_pos_2522_);
lean_dec(v_pos_2522_);
return v___x_2535_;
}
}
else
{
lean_object* v___x_2536_; 
v___x_2536_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2520_, v_c_2519_, v_pos_2522_);
lean_dec(v_pos_2522_);
return v___x_2536_;
}
}
else
{
lean_object* v___x_2537_; 
v___x_2537_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_2520_, v_c_2519_, v_pos_2522_);
lean_dec(v_pos_2522_);
return v___x_2537_;
}
}
else
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = lean_box(0);
v___x_2539_ = l_Lean_Parser_ParserState_mkEOIError(v_s_2520_, v___x_2538_);
return v___x_2539_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0___boxed(lean_object* v_c_2540_, lean_object* v_s_2541_){
_start:
{
lean_object* v_res_2542_; 
v_res_2542_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0(v_c_2540_, v_s_2541_);
lean_dec_ref(v_c_2540_);
return v_res_2542_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__3(lean_object* v___f_2543_, lean_object* v___f_2544_, lean_object* v___f_2545_, lean_object* v_c_2546_, lean_object* v_s_2547_){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; uint8_t v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v_fn_2555_; lean_object* v___x_2556_; 
v___x_2548_ = lean_box(1);
v___x_2549_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2549_, 0, v___f_2543_);
lean_ctor_set(v___x_2549_, 1, v___f_2544_);
lean_ctor_set(v___x_2549_, 2, v___x_2548_);
v___x_2550_ = 1;
v___x_2551_ = lean_box(v___x_2550_);
v___x_2552_ = lean_alloc_closure((void*)(l_Lean_Parser_rawFn___boxed), 4, 2);
lean_closure_set(v___x_2552_, 0, v___f_2545_);
lean_closure_set(v___x_2552_, 1, v___x_2551_);
v___x_2553_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2553_, 0, v___x_2549_);
lean_ctor_set(v___x_2553_, 1, v___x_2552_);
v___x_2554_ = l_Lean_Parser_tokenWithAntiquot(v___x_2553_);
v_fn_2555_ = lean_ctor_get(v___x_2554_, 1);
lean_inc_ref(v_fn_2555_);
lean_dec_ref(v___x_2554_);
v___x_2556_ = lean_apply_2(v_fn_2555_, v_c_2546_, v_s_2547_);
return v___x_2556_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0(uint32_t v_x_2566_){
_start:
{
uint32_t v___x_2567_; uint8_t v___x_2568_; 
v___x_2567_ = 48;
v___x_2568_ = lean_uint32_dec_le(v___x_2567_, v_x_2566_);
if (v___x_2568_ == 0)
{
return v___x_2568_;
}
else
{
uint32_t v___x_2569_; uint8_t v___x_2570_; 
v___x_2569_ = 57;
v___x_2570_ = lean_uint32_dec_le(v_x_2566_, v___x_2569_);
return v___x_2570_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0___boxed(lean_object* v_x_2571_){
_start:
{
uint32_t v_x_319__boxed_2572_; uint8_t v_res_2573_; lean_object* v_r_2574_; 
v_x_319__boxed_2572_ = lean_unbox_uint32(v_x_2571_);
lean_dec(v_x_2571_);
v_res_2573_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0(v_x_319__boxed_2572_);
v_r_2574_ = lean_box(v_res_2573_);
return v_r_2574_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1(uint32_t v_c_2575_){
_start:
{
uint32_t v___x_2576_; uint8_t v___x_2577_; 
v___x_2576_ = 46;
v___x_2577_ = lean_uint32_dec_eq(v_c_2575_, v___x_2576_);
if (v___x_2577_ == 0)
{
uint32_t v___x_2578_; uint8_t v___x_2579_; 
v___x_2578_ = 41;
v___x_2579_ = lean_uint32_dec_eq(v_c_2575_, v___x_2578_);
return v___x_2579_;
}
else
{
return v___x_2577_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1___boxed(lean_object* v_c_2580_){
_start:
{
uint32_t v_c_boxed_2581_; uint8_t v_res_2582_; lean_object* v_r_2583_; 
v_c_boxed_2581_ = lean_unbox_uint32(v_c_2580_);
lean_dec(v_c_2580_);
v_res_2582_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1(v_c_boxed_2581_);
v_r_2583_ = lean_box(v_res_2582_);
return v_r_2583_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2(lean_object* v___f_2585_, lean_object* v___y_2586_, lean_object* v___y_2587_){
_start:
{
lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2588_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2___closed__0));
v___x_2589_ = l_Lean_Parser_satisfyFn(v___f_2585_, v___x_2588_, v___y_2586_, v___y_2587_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2___boxed(lean_object* v___f_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2(v___f_2590_, v___y_2591_, v___y_2592_);
lean_dec_ref(v___y_2591_);
return v_res_2593_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3(lean_object* v___f_2596_, lean_object* v___f_2597_, lean_object* v_c_2598_, lean_object* v_s_2599_){
_start:
{
lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v_s_x27_2602_; lean_object* v_errorMsg_2603_; lean_object* v___x_2604_; uint8_t v___x_2605_; 
v___x_2600_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3___closed__0));
v___x_2601_ = lean_alloc_closure((void*)(l_Lean_Parser_takeWhile1Fn), 4, 2);
lean_closure_set(v___x_2601_, 0, v___f_2596_);
lean_closure_set(v___x_2601_, 1, v___x_2600_);
lean_inc_ref(v_s_2599_);
v_s_x27_2602_ = l_Lean_Parser_andthenFn(v___x_2601_, v___f_2597_, v_c_2598_, v_s_2599_);
v_errorMsg_2603_ = lean_ctor_get(v_s_x27_2602_, 4);
lean_inc(v_errorMsg_2603_);
v___x_2604_ = lean_box(0);
v___x_2605_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_2603_, v___x_2604_);
lean_dec(v_errorMsg_2603_);
if (v___x_2605_ == 0)
{
lean_object* v_pos_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v_pos_2606_ = lean_ctor_get(v_s_2599_, 2);
lean_inc(v_pos_2606_);
lean_dec_ref(v_s_2599_);
v___x_2607_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3___closed__1));
v___x_2608_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_x27_2602_, v___x_2607_, v_pos_2606_, v___x_2604_);
return v___x_2608_;
}
else
{
lean_dec_ref(v_s_2599_);
return v_s_x27_2602_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__0(lean_object* v_c_2624_){
_start:
{
lean_object* v_toInputContext_2625_; lean_object* v_toParserModuleContext_2626_; lean_object* v_toCacheableParserContext_2627_; lean_object* v_tokens_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2637_; 
v_toInputContext_2625_ = lean_ctor_get(v_c_2624_, 0);
v_toParserModuleContext_2626_ = lean_ctor_get(v_c_2624_, 1);
v_toCacheableParserContext_2627_ = lean_ctor_get(v_c_2624_, 2);
v_tokens_2628_ = lean_ctor_get(v_c_2624_, 3);
v_isSharedCheck_2637_ = !lean_is_exclusive(v_c_2624_);
if (v_isSharedCheck_2637_ == 0)
{
v___x_2630_ = v_c_2624_;
v_isShared_2631_ = v_isSharedCheck_2637_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_tokens_2628_);
lean_inc(v_toCacheableParserContext_2627_);
lean_inc(v_toParserModuleContext_2626_);
lean_inc(v_toInputContext_2625_);
lean_dec(v_c_2624_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2637_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2635_; 
v___x_2632_ = ((lean_object*)(l_Lean_Doc_Syntax_metadata__block___closed__2));
v___x_2633_ = l_Lean_Data_Trie_insert___redArg(v_tokens_2628_, v___x_2632_, v___x_2632_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 3, v___x_2633_);
v___x_2635_ = v___x_2630_;
goto v_reusejp_2634_;
}
else
{
lean_object* v_reuseFailAlloc_2636_; 
v_reuseFailAlloc_2636_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_2636_, 0, v_toInputContext_2625_);
lean_ctor_set(v_reuseFailAlloc_2636_, 1, v_toParserModuleContext_2626_);
lean_ctor_set(v_reuseFailAlloc_2636_, 2, v_toCacheableParserContext_2627_);
lean_ctor_set(v_reuseFailAlloc_2636_, 3, v___x_2633_);
v___x_2635_ = v_reuseFailAlloc_2636_;
goto v_reusejp_2634_;
}
v_reusejp_2634_:
{
return v___x_2635_;
}
}
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__2(void){
_start:
{
uint8_t v___x_2644_; uint8_t v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; 
v___x_2644_ = 0;
v___x_2645_ = 1;
v___x_2646_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__1));
v___x_2647_ = ((lean_object*)(l_Lean_Doc_Syntax_metadata__block___closed__4));
v___x_2648_ = l_Lean_Parser_mkAntiquot(v___x_2647_, v___x_2646_, v___x_2645_, v___x_2644_);
return v___x_2648_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__3(void){
_start:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; 
v___x_2649_ = lean_obj_once(&l_Lean_Doc_Syntax_metadataContents___closed__17, &l_Lean_Doc_Syntax_metadataContents___closed__17_once, _init_l_Lean_Doc_Syntax_metadataContents___closed__17);
v___x_2650_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__2);
v___x_2651_ = l_Lean_Parser_withAntiquot(v___x_2650_, v___x_2649_);
return v___x_2651_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1(lean_object* v___f_2652_, lean_object* v_c_2653_, lean_object* v_s_2654_){
_start:
{
lean_object* v___x_2655_; lean_object* v_fn_2656_; lean_object* v___x_2657_; 
v___x_2655_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__3);
v_fn_2656_ = lean_ctor_get(v___x_2655_, 1);
lean_inc_ref(v_fn_2656_);
v___x_2657_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_2652_, v_fn_2656_, v_c_2653_, v_s_2654_);
return v___x_2657_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_headerMarker___lam__0___closed__2(void){
_start:
{
uint32_t v___x_2671_; lean_object* v___x_2672_; 
v___x_2671_ = 35;
v___x_2672_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_2671_);
return v___x_2672_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_headerMarker___lam__0___closed__3(void){
_start:
{
uint8_t v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; 
v___x_2673_ = 0;
v___x_2674_ = lean_obj_once(&l_Lean_Doc_Parser_headerMarker___lam__0___closed__2, &l_Lean_Doc_Parser_headerMarker___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_headerMarker___lam__0___closed__2);
v___x_2675_ = ((lean_object*)(l_Lean_Doc_Parser_headerMarker___lam__0___closed__1));
v___x_2676_ = ((lean_object*)(l_Lean_Doc_Parser_headerMarker___lam__0___closed__0));
v___x_2677_ = l_Lean_Parser_nodeWithAntiquot(v___x_2676_, v___x_2675_, v___x_2674_, v___x_2673_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_headerMarker___lam__0(lean_object* v_c_2678_, lean_object* v_s_2679_){
_start:
{
lean_object* v___x_2680_; lean_object* v_fn_2681_; lean_object* v___x_2682_; 
v___x_2680_ = lean_obj_once(&l_Lean_Doc_Parser_headerMarker___lam__0___closed__3, &l_Lean_Doc_Parser_headerMarker___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_headerMarker___lam__0___closed__3);
v_fn_2681_ = lean_ctor_get(v___x_2680_, 1);
lean_inc_ref(v_fn_2681_);
v___x_2682_ = lean_apply_2(v_fn_2681_, v_c_2678_, v_s_2679_);
return v___x_2682_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_listMarker___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom));
v___x_2695_ = l_Lean_Parser_atomic(v___x_2694_);
return v___x_2695_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_listMarker___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2696_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom));
v___x_2697_ = lean_obj_once(&l_Lean_Doc_Parser_listMarker___lam__0___closed__2, &l_Lean_Doc_Parser_listMarker___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_listMarker___lam__0___closed__2);
v___x_2698_ = l_Lean_Parser_orelse(v___x_2697_, v___x_2696_);
return v___x_2698_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_listMarker___lam__0___closed__4(void){
_start:
{
uint8_t v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2699_ = 0;
v___x_2700_ = lean_obj_once(&l_Lean_Doc_Parser_listMarker___lam__0___closed__3, &l_Lean_Doc_Parser_listMarker___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_listMarker___lam__0___closed__3);
v___x_2701_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___lam__0___closed__1));
v___x_2702_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___lam__0___closed__0));
v___x_2703_ = l_Lean_Parser_nodeWithAntiquot(v___x_2702_, v___x_2701_, v___x_2700_, v___x_2699_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_listMarker___lam__0(lean_object* v_c_2704_, lean_object* v_s_2705_){
_start:
{
lean_object* v___x_2706_; lean_object* v_fn_2707_; lean_object* v___x_2708_; 
v___x_2706_ = lean_obj_once(&l_Lean_Doc_Parser_listMarker___lam__0___closed__4, &l_Lean_Doc_Parser_listMarker___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_listMarker___lam__0___closed__4);
v_fn_2707_ = lean_ctor_get(v___x_2706_, 1);
lean_inc_ref(v_fn_2707_);
v___x_2708_ = lean_apply_2(v_fn_2707_, v_c_2704_, v_s_2705_);
return v___x_2708_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___lam__0___closed__0(void){
_start:
{
uint8_t v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; 
v___x_2714_ = 0;
v___x_2715_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom));
v___x_2716_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___lam__0___closed__1));
v___x_2717_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___lam__0___closed__0));
v___x_2718_ = l_Lean_Parser_nodeWithAntiquot(v___x_2717_, v___x_2716_, v___x_2715_, v___x_2714_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___lam__0(lean_object* v_c_2719_, lean_object* v_s_2720_){
_start:
{
lean_object* v___x_2721_; lean_object* v_fn_2722_; lean_object* v___x_2723_; 
v___x_2721_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___lam__0___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___lam__0___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___lam__0___closed__0);
v_fn_2722_ = lean_ctor_get(v___x_2721_, 1);
lean_inc_ref(v_fn_2722_);
v___x_2723_ = lean_apply_2(v_fn_2722_, v_c_2719_, v_s_2720_);
return v___x_2723_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___lam__0___closed__0(void){
_start:
{
uint8_t v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; 
v___x_2729_ = 0;
v___x_2730_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom));
v___x_2731_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___lam__0___closed__1));
v___x_2732_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___lam__0___closed__0));
v___x_2733_ = l_Lean_Parser_nodeWithAntiquot(v___x_2732_, v___x_2731_, v___x_2730_, v___x_2729_);
return v___x_2733_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___lam__0(lean_object* v_c_2734_, lean_object* v_s_2735_){
_start:
{
lean_object* v___x_2736_; lean_object* v_fn_2737_; lean_object* v___x_2738_; 
v___x_2736_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___lam__0___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___lam__0___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___lam__0___closed__0);
v_fn_2737_ = lean_ctor_get(v___x_2736_, 1);
lean_inc_ref(v_fn_2737_);
v___x_2738_ = lean_apply_2(v_fn_2737_, v_c_2734_, v_s_2735_);
return v___x_2738_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0(uint32_t v_x_2744_){
_start:
{
uint32_t v___x_2745_; uint8_t v___x_2746_; 
v___x_2745_ = 58;
v___x_2746_ = lean_uint32_dec_eq(v_x_2744_, v___x_2745_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0___boxed(lean_object* v_x_2747_){
_start:
{
uint32_t v_x_134__boxed_2748_; uint8_t v_res_2749_; lean_object* v_r_2750_; 
v_x_134__boxed_2748_ = lean_unbox_uint32(v_x_2747_);
lean_dec(v_x_2747_);
v_res_2749_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0(v_x_134__boxed_2748_);
v_r_2750_ = lean_box(v_res_2749_);
return v_r_2750_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__0(void){
_start:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; 
v___x_2751_ = ((lean_object*)(l_Lean_Doc_Syntax_desc___closed__2));
v___x_2752_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2751_);
return v___x_2752_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3(lean_object* v___f_2754_, lean_object* v___f_2755_, lean_object* v___f_2756_, lean_object* v_c_2757_, lean_object* v_s_2758_){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v_fn_2768_; lean_object* v___x_2769_; 
v___x_2759_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__0);
v___x_2760_ = lean_box(1);
v___x_2761_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2761_, 0, v___f_2754_);
lean_ctor_set(v___x_2761_, 1, v___f_2755_);
lean_ctor_set(v___x_2761_, 2, v___x_2760_);
v___x_2762_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__1));
v___x_2763_ = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(v___x_2763_, 0, v___f_2756_);
lean_closure_set(v___x_2763_, 1, v___x_2762_);
v___x_2764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2764_, 0, v___x_2761_);
lean_ctor_set(v___x_2764_, 1, v___x_2763_);
v___x_2765_ = l_Lean_Parser_notFollowedBy(v___x_2764_, v___x_2762_);
v___x_2766_ = l_Lean_Parser_andthen(v___x_2759_, v___x_2765_);
v___x_2767_ = l_Lean_Parser_atomic(v___x_2766_);
v_fn_2768_ = lean_ctor_get(v___x_2767_, 1);
lean_inc_ref(v_fn_2768_);
lean_dec_ref(v___x_2767_);
v___x_2769_ = lean_apply_2(v_fn_2768_, v_c_2757_, v_s_2758_);
return v___x_2769_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__2(void){
_start:
{
uint32_t v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = 95;
v___x_2786_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_2785_);
return v___x_2786_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__3(void){
_start:
{
uint8_t v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; 
v___x_2787_ = 0;
v___x_2788_ = lean_obj_once(&l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__2, &l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__2);
v___x_2789_ = ((lean_object*)(l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__1));
v___x_2790_ = ((lean_object*)(l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__0));
v___x_2791_ = l_Lean_Parser_nodeWithAntiquot(v___x_2790_, v___x_2789_, v___x_2788_, v___x_2787_);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_emphDelimiter___lam__0(lean_object* v_c_2792_, lean_object* v_s_2793_){
_start:
{
lean_object* v___x_2794_; lean_object* v_fn_2795_; lean_object* v___x_2796_; 
v___x_2794_ = lean_obj_once(&l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__3, &l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__3);
v_fn_2795_ = lean_ctor_get(v___x_2794_, 1);
lean_inc_ref(v_fn_2795_);
v___x_2796_ = lean_apply_2(v_fn_2795_, v_c_2792_, v_s_2793_);
return v___x_2796_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__2(void){
_start:
{
uint32_t v___x_2808_; lean_object* v___x_2809_; 
v___x_2808_ = 42;
v___x_2809_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_2808_);
return v___x_2809_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__3(void){
_start:
{
uint8_t v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2813_; lean_object* v___x_2814_; 
v___x_2810_ = 0;
v___x_2811_ = lean_obj_once(&l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__2, &l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__2);
v___x_2812_ = ((lean_object*)(l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__1));
v___x_2813_ = ((lean_object*)(l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__0));
v___x_2814_ = l_Lean_Parser_nodeWithAntiquot(v___x_2813_, v___x_2812_, v___x_2811_, v___x_2810_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_boldDelimiter___lam__0(lean_object* v_c_2815_, lean_object* v_s_2816_){
_start:
{
lean_object* v___x_2817_; lean_object* v_fn_2818_; lean_object* v___x_2819_; 
v___x_2817_ = lean_obj_once(&l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__3, &l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__3);
v_fn_2818_ = lean_ctor_get(v___x_2817_, 1);
lean_inc_ref(v_fn_2818_);
v___x_2819_ = lean_apply_2(v_fn_2818_, v_c_2815_, v_s_2816_);
return v___x_2819_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2(void){
_start:
{
uint32_t v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = 96;
v___x_2832_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_2831_);
return v___x_2832_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__3(void){
_start:
{
uint8_t v___x_2833_; lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; lean_object* v___x_2837_; 
v___x_2833_ = 0;
v___x_2834_ = lean_obj_once(&l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2, &l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2);
v___x_2835_ = ((lean_object*)(l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__1));
v___x_2836_ = ((lean_object*)(l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__0));
v___x_2837_ = l_Lean_Parser_nodeWithAntiquot(v___x_2836_, v___x_2835_, v___x_2834_, v___x_2833_);
return v___x_2837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_codeDelimiter___lam__0(lean_object* v_c_2838_, lean_object* v_s_2839_){
_start:
{
lean_object* v___x_2840_; lean_object* v_fn_2841_; lean_object* v___x_2842_; 
v___x_2840_ = lean_obj_once(&l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__3, &l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__3);
v_fn_2841_ = lean_ctor_get(v___x_2840_, 1);
lean_inc_ref(v_fn_2841_);
v___x_2842_ = lean_apply_2(v_fn_2841_, v_c_2838_, v_s_2839_);
return v___x_2842_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__2(void){
_start:
{
uint8_t v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2854_ = 0;
v___x_2855_ = lean_obj_once(&l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2, &l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2);
v___x_2856_ = ((lean_object*)(l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__1));
v___x_2857_ = ((lean_object*)(l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__0));
v___x_2858_ = l_Lean_Parser_nodeWithAntiquot(v___x_2857_, v___x_2856_, v___x_2855_, v___x_2854_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_codeBlockFence___lam__0(lean_object* v_c_2859_, lean_object* v_s_2860_){
_start:
{
lean_object* v___x_2861_; lean_object* v_fn_2862_; lean_object* v___x_2863_; 
v___x_2861_ = lean_obj_once(&l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__2, &l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__2);
v_fn_2862_ = lean_ctor_get(v___x_2861_, 1);
lean_inc_ref(v_fn_2862_);
v___x_2863_ = lean_apply_2(v_fn_2862_, v_c_2859_, v_s_2860_);
return v___x_2863_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2876_; lean_object* v___x_2877_; 
v___x_2876_ = ((lean_object*)(l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__2));
v___x_2877_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2876_);
return v___x_2877_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__4(void){
_start:
{
uint8_t v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; 
v___x_2878_ = 0;
v___x_2879_ = lean_obj_once(&l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__3, &l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__3);
v___x_2880_ = ((lean_object*)(l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__1));
v___x_2881_ = ((lean_object*)(l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__0));
v___x_2882_ = l_Lean_Parser_nodeWithAntiquot(v___x_2881_, v___x_2880_, v___x_2879_, v___x_2878_);
return v___x_2882_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_inlineMathMarker___lam__0(lean_object* v_c_2883_, lean_object* v_s_2884_){
_start:
{
lean_object* v___x_2885_; lean_object* v_fn_2886_; lean_object* v___x_2887_; 
v___x_2885_ = lean_obj_once(&l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__4, &l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__4);
v_fn_2886_ = lean_ctor_get(v___x_2885_, 1);
lean_inc_ref(v_fn_2886_);
v___x_2887_ = lean_apply_2(v_fn_2886_, v_c_2883_, v_s_2884_);
return v___x_2887_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; 
v___x_2900_ = ((lean_object*)(l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__2));
v___x_2901_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2900_);
return v___x_2901_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__4(void){
_start:
{
uint8_t v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; 
v___x_2902_ = 0;
v___x_2903_ = lean_obj_once(&l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__3, &l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__3);
v___x_2904_ = ((lean_object*)(l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__1));
v___x_2905_ = ((lean_object*)(l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__0));
v___x_2906_ = l_Lean_Parser_nodeWithAntiquot(v___x_2905_, v___x_2904_, v___x_2903_, v___x_2902_);
return v___x_2906_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_displayMathMarker___lam__0(lean_object* v_c_2907_, lean_object* v_s_2908_){
_start:
{
lean_object* v___x_2909_; lean_object* v_fn_2910_; lean_object* v___x_2911_; 
v___x_2909_ = lean_obj_once(&l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__4, &l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__4);
v_fn_2910_ = lean_ctor_get(v___x_2909_, 1);
lean_inc_ref(v_fn_2910_);
v___x_2911_ = lean_apply_2(v_fn_2910_, v_c_2907_, v_s_2908_);
return v___x_2911_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__2(void){
_start:
{
uint32_t v___x_2923_; lean_object* v___x_2924_; 
v___x_2923_ = 58;
v___x_2924_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_2923_);
return v___x_2924_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__3(void){
_start:
{
uint8_t v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2925_ = 0;
v___x_2926_ = lean_obj_once(&l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__2, &l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__2);
v___x_2927_ = ((lean_object*)(l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__1));
v___x_2928_ = ((lean_object*)(l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__0));
v___x_2929_ = l_Lean_Parser_nodeWithAntiquot(v___x_2928_, v___x_2927_, v___x_2926_, v___x_2925_);
return v___x_2929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_directiveDelimiter___lam__0(lean_object* v_c_2930_, lean_object* v_s_2931_){
_start:
{
lean_object* v___x_2932_; lean_object* v_fn_2933_; lean_object* v___x_2934_; 
v___x_2932_ = lean_obj_once(&l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__3, &l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__3);
v_fn_2933_ = lean_ctor_get(v___x_2932_, 1);
lean_inc_ref(v_fn_2933_);
v___x_2934_ = lean_apply_2(v_fn_2933_, v_c_2930_, v_s_2931_);
return v___x_2934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength(lean_object* v_x_2940_){
_start:
{
if (lean_obj_tag(v_x_2940_) == 1)
{
lean_object* v_args_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; uint8_t v___x_2944_; 
v_args_2941_ = lean_ctor_get(v_x_2940_, 2);
v___x_2942_ = lean_array_get_size(v_args_2941_);
v___x_2943_ = lean_unsigned_to_nat(1u);
v___x_2944_ = lean_nat_dec_eq(v___x_2942_, v___x_2943_);
if (v___x_2944_ == 0)
{
lean_object* v___x_2945_; 
v___x_2945_ = lean_box(0);
return v___x_2945_;
}
else
{
lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2946_ = lean_unsigned_to_nat(0u);
v___x_2947_ = lean_array_fget_borrowed(v_args_2941_, v___x_2946_);
if (lean_obj_tag(v___x_2947_) == 2)
{
lean_object* v_val_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; 
v_val_2948_ = lean_ctor_get(v___x_2947_, 1);
v___x_2949_ = lean_string_length(v_val_2948_);
v___x_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
return v___x_2950_;
}
else
{
lean_object* v___x_2951_; 
v___x_2951_ = lean_box(0);
return v___x_2951_;
}
}
}
else
{
lean_object* v___x_2952_; 
v___x_2952_ = lean_box(0);
return v___x_2952_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength___boxed(lean_object* v_x_2953_){
_start:
{
lean_object* v_res_2954_; 
v_res_2954_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength(v_x_2953_);
lean_dec(v_x_2953_);
return v_res_2954_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0(uint32_t v_ch_2955_, lean_object* v_x_2956_, lean_object* v_x_2957_){
_start:
{
lean_object* v_zero_2958_; uint8_t v_isZero_2959_; 
v_zero_2958_ = lean_unsigned_to_nat(0u);
v_isZero_2959_ = lean_nat_dec_eq(v_x_2956_, v_zero_2958_);
if (v_isZero_2959_ == 1)
{
lean_dec(v_x_2956_);
return v_x_2957_;
}
else
{
lean_object* v_one_2960_; lean_object* v_n_2961_; lean_object* v___x_2962_; 
v_one_2960_ = lean_unsigned_to_nat(1u);
v_n_2961_ = lean_nat_sub(v_x_2956_, v_one_2960_);
lean_dec(v_x_2956_);
v___x_2962_ = lean_string_push(v_x_2957_, v_ch_2955_);
v_x_2956_ = v_n_2961_;
v_x_2957_ = v___x_2962_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0___boxed(lean_object* v_ch_2964_, lean_object* v_x_2965_, lean_object* v_x_2966_){
_start:
{
uint32_t v_ch_boxed_2967_; lean_object* v_res_2968_; 
v_ch_boxed_2967_ = lean_unbox_uint32(v_ch_2964_);
lean_dec(v_ch_2964_);
v_res_2968_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0(v_ch_boxed_2967_, v_x_2965_, v_x_2966_);
return v_res_2968_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths(lean_object* v_delim_2971_, uint32_t v_ch_2972_, lean_object* v_contents_2973_, lean_object* v_c_2974_, lean_object* v_s_2975_){
_start:
{
lean_object* v_fn_2976_; lean_object* v_s_2977_; lean_object* v_stxStack_2978_; lean_object* v_errorMsg_2979_; lean_object* v___x_2980_; uint8_t v___x_2981_; 
v_fn_2976_ = lean_ctor_get(v_delim_2971_, 1);
lean_inc_ref_n(v_fn_2976_, 2);
lean_dec_ref(v_delim_2971_);
lean_inc_ref(v_c_2974_);
v_s_2977_ = lean_apply_2(v_fn_2976_, v_c_2974_, v_s_2975_);
v_stxStack_2978_ = lean_ctor_get(v_s_2977_, 0);
lean_inc_ref(v_stxStack_2978_);
v_errorMsg_2979_ = lean_ctor_get(v_s_2977_, 4);
lean_inc(v_errorMsg_2979_);
v___x_2980_ = lean_box(0);
v___x_2981_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_2979_, v___x_2980_);
lean_dec(v_errorMsg_2979_);
if (v___x_2981_ == 0)
{
lean_dec_ref(v_stxStack_2978_);
lean_dec_ref(v_fn_2976_);
lean_dec_ref(v_c_2974_);
lean_dec_ref(v_contents_2973_);
return v_s_2977_;
}
else
{
lean_object* v_fn_2982_; lean_object* v_s_2983_; lean_object* v_pos_2984_; lean_object* v_errorMsg_2985_; uint8_t v___x_2986_; 
v_fn_2982_ = lean_ctor_get(v_contents_2973_, 1);
lean_inc_ref(v_fn_2982_);
lean_dec_ref(v_contents_2973_);
lean_inc_ref(v_c_2974_);
v_s_2983_ = lean_apply_2(v_fn_2982_, v_c_2974_, v_s_2977_);
v_pos_2984_ = lean_ctor_get(v_s_2983_, 2);
lean_inc(v_pos_2984_);
v_errorMsg_2985_ = lean_ctor_get(v_s_2983_, 4);
lean_inc(v_errorMsg_2985_);
v___x_2986_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_2985_, v___x_2980_);
lean_dec(v_errorMsg_2985_);
if (v___x_2986_ == 0)
{
lean_dec(v_pos_2984_);
lean_dec_ref(v_stxStack_2978_);
lean_dec_ref(v_fn_2976_);
lean_dec_ref(v_c_2974_);
return v_s_2983_;
}
else
{
lean_object* v_s_2987_; lean_object* v_stxStack_2988_; lean_object* v_errorMsg_2989_; uint8_t v___x_2990_; 
v_s_2987_ = lean_apply_2(v_fn_2976_, v_c_2974_, v_s_2983_);
v_stxStack_2988_ = lean_ctor_get(v_s_2987_, 0);
lean_inc_ref(v_stxStack_2988_);
v_errorMsg_2989_ = lean_ctor_get(v_s_2987_, 4);
lean_inc(v_errorMsg_2989_);
v___x_2990_ = l_Option_instBEq_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_2989_, v___x_2980_);
lean_dec(v_errorMsg_2989_);
if (v___x_2990_ == 0)
{
lean_dec_ref(v_stxStack_2988_);
lean_dec(v_pos_2984_);
lean_dec_ref(v_stxStack_2978_);
return v_s_2987_;
}
else
{
lean_object* v_opener_2991_; lean_object* v___x_2992_; 
v_opener_2991_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2978_);
lean_dec_ref(v_stxStack_2978_);
v___x_2992_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength(v_opener_2991_);
lean_dec(v_opener_2991_);
if (lean_obj_tag(v___x_2992_) == 1)
{
lean_object* v_val_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; 
v_val_2993_ = lean_ctor_get(v___x_2992_, 0);
lean_inc(v_val_2993_);
lean_dec_ref_known(v___x_2992_, 1);
v___x_2994_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_2988_);
lean_dec_ref(v_stxStack_2988_);
v___x_2995_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength(v___x_2994_);
lean_dec(v___x_2994_);
if (lean_obj_tag(v___x_2995_) == 1)
{
lean_object* v_val_2996_; uint8_t v___x_2997_; 
v_val_2996_ = lean_ctor_get(v___x_2995_, 0);
lean_inc(v_val_2996_);
lean_dec_ref_known(v___x_2995_, 1);
v___x_2997_ = lean_nat_dec_eq(v_val_2993_, v_val_2996_);
lean_dec(v_val_2996_);
if (v___x_2997_ == 0)
{
lean_object* v___x_2998_; lean_object* v___x_2999_; lean_object* v___x_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; lean_object* v___x_3007_; 
v___x_2998_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0));
v___x_2999_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_3000_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0(v_ch_2972_, v_val_2993_, v___x_2999_);
v___x_3001_ = lean_string_append(v___x_2998_, v___x_3000_);
v___x_3002_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___closed__0));
v___x_3003_ = lean_string_append(v___x_3001_, v___x_3002_);
v___x_3004_ = lean_string_append(v___x_3003_, v___x_3000_);
lean_dec_ref(v___x_3000_);
v___x_3005_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___closed__1));
v___x_3006_ = lean_string_append(v___x_3004_, v___x_3005_);
v___x_3007_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_2987_, v___x_3006_, v_pos_2984_, v___x_2980_);
return v___x_3007_;
}
else
{
lean_dec(v_val_2993_);
lean_dec(v_pos_2984_);
return v_s_2987_;
}
}
else
{
lean_dec(v___x_2995_);
lean_dec(v_val_2993_);
lean_dec(v_pos_2984_);
return v_s_2987_;
}
}
else
{
lean_dec(v___x_2992_);
lean_dec_ref(v_stxStack_2988_);
lean_dec(v_pos_2984_);
return v_s_2987_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___boxed(lean_object* v_delim_3008_, lean_object* v_ch_3009_, lean_object* v_contents_3010_, lean_object* v_c_3011_, lean_object* v_s_3012_){
_start:
{
uint32_t v_ch_boxed_3013_; lean_object* v_res_3014_; 
v_ch_boxed_3013_ = lean_unbox_uint32(v_ch_3009_);
lean_dec(v_ch_3009_);
v_res_3014_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths(v_delim_3008_, v_ch_boxed_3013_, v_contents_3010_, v_c_3011_, v_s_3012_);
return v_res_3014_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2___boxed__const__1(void){
_start:
{
uint32_t v___x_3022_; lean_object* v___x_3023_; 
v___x_3022_ = 96;
v___x_3023_ = lean_box_uint32(v___x_3022_);
return v___x_3023_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2(void){
_start:
{
lean_object* v___x_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; lean_object* v___x_3027_; 
v___x_3024_ = ((lean_object*)(l_Lean_Doc_Parser_versoCode));
v___x_3025_ = ((lean_object*)(l_Lean_Doc_Parser_codeDelimiter));
v___x_3026_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2___boxed__const__1;
v___x_3027_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___boxed), 5, 3);
lean_closure_set(v___x_3027_, 0, v___x_3025_);
lean_closure_set(v___x_3027_, 1, v___x_3026_);
lean_closure_set(v___x_3027_, 2, v___x_3024_);
return v___x_3027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2(lean_object* v___f_3028_, lean_object* v___f_3029_, lean_object* v_c_3030_, lean_object* v_s_3031_){
_start:
{
lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3036_; lean_object* v___x_3037_; uint8_t v___x_3038_; lean_object* v___x_3039_; lean_object* v_fn_3040_; lean_object* v___x_3041_; 
v___x_3032_ = ((lean_object*)(l_Lean_Doc_Syntax_code___closed__0));
v___x_3033_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1));
v___x_3034_ = lean_box(1);
v___x_3035_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3035_, 0, v___f_3028_);
lean_ctor_set(v___x_3035_, 1, v___f_3029_);
lean_ctor_set(v___x_3035_, 2, v___x_3034_);
v___x_3036_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2);
v___x_3037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3037_, 0, v___x_3035_);
lean_ctor_set(v___x_3037_, 1, v___x_3036_);
v___x_3038_ = 0;
v___x_3039_ = l_Lean_Parser_nodeWithAntiquot(v___x_3032_, v___x_3033_, v___x_3037_, v___x_3038_);
v_fn_3040_ = lean_ctor_get(v___x_3039_, 1);
lean_inc_ref(v_fn_3040_);
lean_dec_ref(v___x_3039_);
v___x_3041_ = lean_apply_2(v_fn_3040_, v_c_3030_, v_s_3031_);
return v___x_3041_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1(void){
_start:
{
uint32_t v___x_3055_; lean_object* v___x_3056_; 
v___x_3055_ = 10;
v___x_3056_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_3055_);
return v___x_3056_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2(void){
_start:
{
uint8_t v___x_3057_; lean_object* v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; 
v___x_3057_ = 0;
v___x_3058_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1);
v___x_3059_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0));
v___x_3060_ = ((lean_object*)(l_Lean_Doc_Syntax_linebreak___closed__0));
v___x_3061_ = l_Lean_Parser_nodeWithAntiquot(v___x_3060_, v___x_3059_, v___x_3058_, v___x_3057_);
return v___x_3061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot(lean_object* v_a_3062_, lean_object* v_a_3063_){
_start:
{
lean_object* v___x_3064_; lean_object* v_fn_3065_; lean_object* v___x_3066_; 
v___x_3064_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2);
v_fn_3065_ = lean_ctor_get(v___x_3064_, 1);
lean_inc_ref(v_fn_3065_);
v___x_3066_ = lean_apply_2(v_fn_3065_, v_a_3062_, v_a_3063_);
return v___x_3066_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__2(void){
_start:
{
lean_object* v___x_3074_; lean_object* v___x_3075_; 
v___x_3074_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1));
v___x_3075_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_3074_);
return v___x_3075_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3(void){
_start:
{
lean_object* v___x_3076_; lean_object* v___x_3077_; 
v___x_3076_ = ((lean_object*)(l_Lean_Doc_Syntax_ref___closed__5));
v___x_3077_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_3076_);
return v___x_3077_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4(void){
_start:
{
lean_object* v___x_3078_; lean_object* v___x_3079_; lean_object* v___x_3080_; 
v___x_3078_ = ((lean_object*)(l_Lean_Doc_Parser_linkTarget));
v___x_3079_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3);
v___x_3080_ = l_Lean_Parser_andthen(v___x_3079_, v___x_3078_);
return v___x_3080_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5(void){
_start:
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; 
v___x_3081_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4);
v___x_3082_ = ((lean_object*)(l_Lean_Doc_Parser_versoImageAlt));
v___x_3083_ = l_Lean_Parser_andthen(v___x_3082_, v___x_3081_);
return v___x_3083_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6(void){
_start:
{
lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v___x_3084_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5);
v___x_3085_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__2);
v___x_3086_ = l_Lean_Parser_andthen(v___x_3085_, v___x_3084_);
return v___x_3086_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7(void){
_start:
{
uint8_t v___x_3087_; lean_object* v___x_3088_; lean_object* v___x_3089_; lean_object* v___x_3090_; lean_object* v___x_3091_; 
v___x_3087_ = 0;
v___x_3088_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6);
v___x_3089_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0));
v___x_3090_ = ((lean_object*)(l_Lean_Doc_Syntax_image___closed__0));
v___x_3091_ = l_Lean_Parser_nodeWithAntiquot(v___x_3090_, v___x_3089_, v___x_3088_, v___x_3087_);
return v___x_3091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot(lean_object* v_a_3092_, lean_object* v_a_3093_){
_start:
{
lean_object* v___x_3094_; lean_object* v_fn_3095_; lean_object* v___x_3096_; 
v___x_3094_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7);
v_fn_3095_ = lean_ctor_get(v___x_3094_, 1);
lean_inc_ref(v_fn_3095_);
v___x_3096_ = lean_apply_2(v_fn_3095_, v_a_3092_, v_a_3093_);
return v___x_3096_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1(void){
_start:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3103_ = ((lean_object*)(l_Lean_Doc_Syntax_footnote__ref___closed__2));
v___x_3104_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_3103_);
return v___x_3104_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__2(void){
_start:
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3105_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3);
v___x_3106_ = ((lean_object*)(l_Lean_Doc_Parser_versoRef));
v___x_3107_ = l_Lean_Parser_andthen(v___x_3106_, v___x_3105_);
return v___x_3107_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3(void){
_start:
{
lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3108_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__2);
v___x_3109_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1);
v___x_3110_ = l_Lean_Parser_andthen(v___x_3109_, v___x_3108_);
return v___x_3110_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4(void){
_start:
{
uint8_t v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; 
v___x_3111_ = 0;
v___x_3112_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3);
v___x_3113_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0));
v___x_3114_ = ((lean_object*)(l_Lean_Doc_Syntax_footnote___closed__0));
v___x_3115_ = l_Lean_Parser_nodeWithAntiquot(v___x_3114_, v___x_3113_, v___x_3112_, v___x_3111_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot(lean_object* v_a_3116_, lean_object* v_a_3117_){
_start:
{
lean_object* v___x_3118_; lean_object* v_fn_3119_; lean_object* v___x_3120_; 
v___x_3118_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4);
v_fn_3119_ = lean_ctor_get(v___x_3118_, 1);
lean_inc_ref(v_fn_3119_);
v___x_3120_ = lean_apply_2(v_fn_3119_, v_a_3116_, v_a_3117_);
return v___x_3120_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1(void){
_start:
{
lean_object* v___x_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; 
v___x_3127_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode));
v___x_3128_ = ((lean_object*)(l_Lean_Doc_Parser_inlineMathMarker));
v___x_3129_ = l_Lean_Parser_andthen(v___x_3128_, v___x_3127_);
return v___x_3129_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2(void){
_start:
{
uint8_t v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3130_ = 0;
v___x_3131_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1);
v___x_3132_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0));
v___x_3133_ = ((lean_object*)(l_Lean_Doc_Syntax_inline__math___closed__0));
v___x_3134_ = l_Lean_Parser_nodeWithAntiquot(v___x_3133_, v___x_3132_, v___x_3131_, v___x_3130_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot(lean_object* v_a_3135_, lean_object* v_a_3136_){
_start:
{
lean_object* v___x_3137_; lean_object* v_fn_3138_; lean_object* v___x_3139_; 
v___x_3137_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2);
v_fn_3138_ = lean_ctor_get(v___x_3137_, 1);
lean_inc_ref(v_fn_3138_);
v___x_3139_ = lean_apply_2(v_fn_3138_, v_a_3135_, v_a_3136_);
return v___x_3139_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1(void){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; 
v___x_3146_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode));
v___x_3147_ = ((lean_object*)(l_Lean_Doc_Parser_displayMathMarker));
v___x_3148_ = l_Lean_Parser_andthen(v___x_3147_, v___x_3146_);
return v___x_3148_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2(void){
_start:
{
uint8_t v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; 
v___x_3149_ = 0;
v___x_3150_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1);
v___x_3151_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0));
v___x_3152_ = ((lean_object*)(l_Lean_Doc_Syntax_display__math___closed__0));
v___x_3153_ = l_Lean_Parser_nodeWithAntiquot(v___x_3152_, v___x_3151_, v___x_3150_, v___x_3149_);
return v___x_3153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot(lean_object* v_a_3154_, lean_object* v_a_3155_){
_start:
{
lean_object* v___x_3156_; lean_object* v_fn_3157_; lean_object* v___x_3158_; 
v___x_3156_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2);
v_fn_3157_ = lean_ctor_get(v___x_3156_, 1);
lean_inc_ref(v_fn_3157_);
v___x_3158_ = lean_apply_2(v_fn_3157_, v_a_3154_, v_a_3155_);
return v___x_3158_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0(void){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3161_; 
v___x_3159_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot), 2, 0);
v___x_3160_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_3161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3161_, 0, v___x_3160_);
lean_ctor_set(v___x_3161_, 1, v___x_3159_);
return v___x_3161_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1(void){
_start:
{
lean_object* v___x_3162_; lean_object* v___x_3163_; 
v___x_3162_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0);
v___x_3163_ = l_Lean_Parser_atomic(v___x_3162_);
return v___x_3163_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2(void){
_start:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; lean_object* v___x_3166_; 
v___x_3164_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot), 2, 0);
v___x_3165_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_3166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3166_, 0, v___x_3165_);
lean_ctor_set(v___x_3166_, 1, v___x_3164_);
return v___x_3166_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3(void){
_start:
{
lean_object* v___x_3167_; lean_object* v___x_3168_; lean_object* v___x_3169_; 
v___x_3167_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2);
v___x_3168_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1);
v___x_3169_ = l_Lean_Parser_orelse(v___x_3168_, v___x_3167_);
return v___x_3169_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot(lean_object* v_a_3170_, lean_object* v_a_3171_){
_start:
{
lean_object* v___x_3172_; lean_object* v_fn_3173_; lean_object* v___x_3174_; 
v___x_3172_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3);
v_fn_3173_ = lean_ctor_get(v___x_3172_, 1);
lean_inc_ref(v_fn_3173_);
v___x_3174_ = lean_apply_2(v_fn_3173_, v_a_3170_, v_a_3171_);
return v___x_3174_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1(void){
_start:
{
uint8_t v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; 
v___x_3181_ = 0;
v___x_3182_ = ((lean_object*)(l_Lean_Doc_Parser_versoText));
v___x_3183_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0));
v___x_3184_ = ((lean_object*)(l_Lean_Doc_Syntax_text___closed__0));
v___x_3185_ = l_Lean_Parser_nodeWithAntiquot(v___x_3184_, v___x_3183_, v___x_3182_, v___x_3181_);
return v___x_3185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot(lean_object* v_a_3186_, lean_object* v_a_3187_){
_start:
{
lean_object* v___x_3188_; lean_object* v_fn_3189_; lean_object* v___x_3190_; 
v___x_3188_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1);
v_fn_3189_ = lean_ctor_get(v___x_3188_, 1);
lean_inc_ref(v_fn_3189_);
v___x_3190_ = lean_apply_2(v_fn_3189_, v_a_3186_, v_a_3187_);
return v___x_3190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0(lean_object* v___y_3191_){
_start:
{
lean_inc(v___y_3191_);
return v___y_3191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0___boxed(lean_object* v___y_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0(v___y_3192_);
lean_dec(v___y_3192_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1(lean_object* v___y_3194_){
_start:
{
lean_inc_ref(v___y_3194_);
return v___y_3194_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1___boxed(lean_object* v___y_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1(v___y_3195_);
lean_dec_ref(v___y_3195_);
return v_res_3196_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___boxed__const__1(void){
_start:
{
uint32_t v___x_3209_; lean_object* v___x_3210_; 
v___x_3209_ = 42;
v___x_3210_ = lean_box_uint32(v___x_3209_);
return v___x_3210_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0(void){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3211_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot), 2, 0);
v___x_3212_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3213_, 0, v___x_3212_);
lean_ctor_set(v___x_3213_, 1, v___x_3211_);
return v___x_3213_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___boxed__const__1(void){
_start:
{
uint32_t v___x_3220_; lean_object* v___x_3221_; 
v___x_3220_ = 95;
v___x_3221_ = lean_box_uint32(v___x_3220_);
return v___x_3221_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot(lean_object* v_a_3222_, lean_object* v_a_3223_){
_start:
{
lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3228_; lean_object* v___x_3229_; lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3233_; lean_object* v___x_3234_; uint8_t v___x_3235_; lean_object* v___x_3236_; lean_object* v_fn_3237_; lean_object* v___x_3238_; 
v___x_3224_ = ((lean_object*)(l_Lean_Doc_Syntax_emph___closed__0));
v___x_3225_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0));
v___x_3226_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3227_ = ((lean_object*)(l_Lean_Doc_Parser_emphDelimiter));
v___x_3228_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot), 2, 0);
v___x_3229_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3229_, 0, v___x_3226_);
lean_ctor_set(v___x_3229_, 1, v___x_3228_);
v___x_3230_ = l_Lean_Parser_atomic(v___x_3229_);
v___x_3231_ = l_Lean_Parser_many(v___x_3230_);
v___x_3232_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___boxed__const__1;
v___x_3233_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___boxed), 5, 3);
lean_closure_set(v___x_3233_, 0, v___x_3227_);
lean_closure_set(v___x_3233_, 1, v___x_3232_);
lean_closure_set(v___x_3233_, 2, v___x_3231_);
v___x_3234_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3234_, 0, v___x_3226_);
lean_ctor_set(v___x_3234_, 1, v___x_3233_);
v___x_3235_ = 0;
v___x_3236_ = l_Lean_Parser_nodeWithAntiquot(v___x_3224_, v___x_3225_, v___x_3234_, v___x_3235_);
v_fn_3237_ = lean_ctor_get(v___x_3236_, 1);
lean_inc_ref(v_fn_3237_);
lean_dec_ref(v___x_3236_);
v___x_3238_ = lean_apply_2(v_fn_3237_, v_a_3222_, v_a_3223_);
return v___x_3238_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1(void){
_start:
{
lean_object* v___x_3239_; lean_object* v___x_3240_; lean_object* v___x_3241_; 
v___x_3239_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot), 2, 0);
v___x_3240_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3241_, 0, v___x_3240_);
lean_ctor_set(v___x_3241_, 1, v___x_3239_);
return v___x_3241_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2(void){
_start:
{
lean_object* v___x_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; 
v___x_3242_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot), 2, 0);
v___x_3243_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3244_, 0, v___x_3243_);
lean_ctor_set(v___x_3244_, 1, v___x_3242_);
return v___x_3244_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1(void){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = ((lean_object*)(l_Lean_Doc_Syntax_ref___closed__2));
v___x_3252_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_3251_);
return v___x_3252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot(lean_object* v_a_3253_, lean_object* v_a_3254_){
_start:
{
lean_object* v___x_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; lean_object* v___x_3263_; lean_object* v___x_3264_; lean_object* v___x_3265_; uint8_t v___x_3266_; lean_object* v___x_3267_; lean_object* v_fn_3268_; lean_object* v___x_3269_; 
v___x_3255_ = ((lean_object*)(l_Lean_Doc_Syntax_link___closed__0));
v___x_3256_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0));
v___x_3257_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1);
v___x_3258_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3259_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot), 2, 0);
v___x_3260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3260_, 0, v___x_3258_);
lean_ctor_set(v___x_3260_, 1, v___x_3259_);
v___x_3261_ = l_Lean_Parser_atomic(v___x_3260_);
v___x_3262_ = l_Lean_Parser_many(v___x_3261_);
v___x_3263_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4);
v___x_3264_ = l_Lean_Parser_andthen(v___x_3262_, v___x_3263_);
v___x_3265_ = l_Lean_Parser_andthen(v___x_3257_, v___x_3264_);
v___x_3266_ = 0;
v___x_3267_ = l_Lean_Parser_nodeWithAntiquot(v___x_3255_, v___x_3256_, v___x_3265_, v___x_3266_);
v_fn_3268_ = lean_ctor_get(v___x_3267_, 1);
lean_inc_ref(v_fn_3268_);
lean_dec_ref(v___x_3267_);
v___x_3269_ = lean_apply_2(v_fn_3268_, v_a_3253_, v_a_3254_);
return v___x_3269_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3(void){
_start:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3270_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot), 2, 0);
v___x_3271_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3272_, 0, v___x_3271_);
lean_ctor_set(v___x_3272_, 1, v___x_3270_);
return v___x_3272_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5(void){
_start:
{
uint8_t v___x_3278_; lean_object* v___x_3279_; lean_object* v___x_3280_; lean_object* v___x_3281_; 
v___x_3278_ = 1;
v___x_3279_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4));
v___x_3280_ = ((lean_object*)(l_Lean_Doc_Syntax_inline_quot___closed__0));
v___x_3281_ = l_Lean_Parser_mkAntiquot(v___x_3280_, v___x_3279_, v___x_3278_, v___x_3278_);
return v___x_3281_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6(void){
_start:
{
lean_object* v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___x_3282_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot), 2, 0);
v___x_3283_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3284_, 0, v___x_3283_);
lean_ctor_set(v___x_3284_, 1, v___x_3282_);
return v___x_3284_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1(void){
_start:
{
lean_object* v___x_3291_; lean_object* v___x_3292_; 
v___x_3291_ = ((lean_object*)(l_Lean_Doc_Syntax_ol___closed__6));
v___x_3292_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_3291_);
return v___x_3292_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2(void){
_start:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; 
v___x_3293_ = ((lean_object*)(l_Lean_Doc_Parser_arg));
v___x_3294_ = l_Lean_Parser_many(v___x_3293_);
return v___x_3294_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3(void){
_start:
{
lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3295_ = ((lean_object*)(l_Lean_Doc_Syntax_role___closed__7));
v___x_3296_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_3295_);
return v___x_3296_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6(void){
_start:
{
lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v___x_3300_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1);
v___x_3301_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__5));
v___x_3302_ = l_Lean_Parser_node(v___x_3301_, v___x_3300_);
return v___x_3302_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__7(void){
_start:
{
lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; 
v___x_3303_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3);
v___x_3304_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__5));
v___x_3305_ = l_Lean_Parser_node(v___x_3304_, v___x_3303_);
return v___x_3305_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8(void){
_start:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3308_; 
v___x_3306_ = l_Lean_Parser_skip;
v___x_3307_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__5));
v___x_3308_ = l_Lean_Parser_node(v___x_3307_, v___x_3306_);
return v___x_3308_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot(lean_object* v_a_3309_, lean_object* v_a_3310_){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; uint8_t v___x_3335_; lean_object* v___x_3336_; lean_object* v_fn_3337_; lean_object* v___x_3338_; 
v___x_3311_ = ((lean_object*)(l_Lean_Doc_Syntax_role___closed__0));
v___x_3312_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0));
v___x_3313_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1);
v___x_3314_ = l_Lean_Parser_ident;
v___x_3315_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2);
v___x_3316_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3);
v___x_3317_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6);
v___x_3318_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3319_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot), 2, 0);
v___x_3320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3320_, 0, v___x_3318_);
lean_ctor_set(v___x_3320_, 1, v___x_3319_);
v___x_3321_ = l_Lean_Parser_atomic(v___x_3320_);
lean_inc_ref(v___x_3321_);
v___x_3322_ = l_Lean_Parser_many(v___x_3321_);
v___x_3323_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__7, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__7_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__7);
v___x_3324_ = l_Lean_Parser_andthen(v___x_3322_, v___x_3323_);
v___x_3325_ = l_Lean_Parser_andthen(v___x_3317_, v___x_3324_);
v___x_3326_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8);
v___x_3327_ = l_Lean_Parser_many1(v___x_3321_);
v___x_3328_ = l_Lean_Parser_andthen(v___x_3327_, v___x_3326_);
v___x_3329_ = l_Lean_Parser_andthen(v___x_3326_, v___x_3328_);
v___x_3330_ = l_Lean_Parser_orelse(v___x_3325_, v___x_3329_);
v___x_3331_ = l_Lean_Parser_andthen(v___x_3316_, v___x_3330_);
v___x_3332_ = l_Lean_Parser_andthen(v___x_3315_, v___x_3331_);
v___x_3333_ = l_Lean_Parser_andthen(v___x_3314_, v___x_3332_);
v___x_3334_ = l_Lean_Parser_andthen(v___x_3313_, v___x_3333_);
v___x_3335_ = 0;
v___x_3336_ = l_Lean_Parser_nodeWithAntiquot(v___x_3311_, v___x_3312_, v___x_3334_, v___x_3335_);
v_fn_3337_ = lean_ctor_get(v___x_3336_, 1);
lean_inc_ref(v_fn_3337_);
lean_dec_ref(v___x_3336_);
v___x_3338_ = lean_apply_2(v_fn_3337_, v_a_3309_, v_a_3310_);
return v___x_3338_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot(lean_object* v_c_3339_, lean_object* v_s_3340_){
_start:
{
lean_object* v___x_3341_; lean_object* v___x_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; lean_object* v___x_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; lean_object* v___x_3352_; lean_object* v_fn_3353_; lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; lean_object* v_alts_3366_; lean_object* v_fn_3367_; uint8_t v___x_3368_; lean_object* v___x_3369_; 
v___x_3341_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3342_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0);
v___x_3343_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot), 2, 0);
v___x_3344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3344_, 0, v___x_3341_);
lean_ctor_set(v___x_3344_, 1, v___x_3343_);
v___x_3345_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot), 2, 0);
v___x_3346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3346_, 0, v___x_3341_);
lean_ctor_set(v___x_3346_, 1, v___x_3345_);
v___x_3347_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1);
v___x_3348_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2);
v___x_3349_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot), 2, 0);
v___x_3350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3350_, 0, v___x_3341_);
lean_ctor_set(v___x_3350_, 1, v___x_3349_);
v___x_3351_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3);
v___x_3352_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5);
v_fn_3353_ = lean_ctor_get(v___x_3352_, 1);
v___x_3354_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6);
v___x_3355_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode));
v___x_3356_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot), 2, 0);
v___x_3357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3357_, 0, v___x_3341_);
lean_ctor_set(v___x_3357_, 1, v___x_3356_);
v___x_3358_ = l_Lean_Parser_orelse(v___x_3354_, v___x_3357_);
v___x_3359_ = l_Lean_Parser_orelse(v___x_3351_, v___x_3358_);
v___x_3360_ = l_Lean_Parser_orelse(v___x_3350_, v___x_3359_);
v___x_3361_ = l_Lean_Parser_orelse(v___x_3348_, v___x_3360_);
v___x_3362_ = l_Lean_Parser_orelse(v___x_3347_, v___x_3361_);
v___x_3363_ = l_Lean_Parser_orelse(v___x_3355_, v___x_3362_);
v___x_3364_ = l_Lean_Parser_orelse(v___x_3346_, v___x_3363_);
v___x_3365_ = l_Lean_Parser_orelse(v___x_3344_, v___x_3364_);
v_alts_3366_ = l_Lean_Parser_orelse(v___x_3342_, v___x_3365_);
v_fn_3367_ = lean_ctor_get(v_alts_3366_, 1);
lean_inc_ref(v_fn_3367_);
lean_dec_ref(v_alts_3366_);
v___x_3368_ = 0;
lean_inc_ref(v_fn_3353_);
v___x_3369_ = l_Lean_Parser_withAntiquotFn(v_fn_3353_, v_fn_3367_, v___x_3368_, v_c_3339_, v_s_3340_);
return v___x_3369_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot(lean_object* v_a_3370_, lean_object* v_a_3371_){
_start:
{
lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3379_; lean_object* v___x_3380_; lean_object* v___x_3381_; lean_object* v___x_3382_; uint8_t v___x_3383_; lean_object* v___x_3384_; lean_object* v_fn_3385_; lean_object* v___x_3386_; 
v___x_3372_ = ((lean_object*)(l_Lean_Doc_Syntax_bold___closed__0));
v___x_3373_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2));
v___x_3374_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3375_ = ((lean_object*)(l_Lean_Doc_Parser_boldDelimiter));
v___x_3376_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot), 2, 0);
v___x_3377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3377_, 0, v___x_3374_);
lean_ctor_set(v___x_3377_, 1, v___x_3376_);
v___x_3378_ = l_Lean_Parser_atomic(v___x_3377_);
v___x_3379_ = l_Lean_Parser_many(v___x_3378_);
v___x_3380_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___boxed__const__1;
v___x_3381_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___boxed), 5, 3);
lean_closure_set(v___x_3381_, 0, v___x_3375_);
lean_closure_set(v___x_3381_, 1, v___x_3380_);
lean_closure_set(v___x_3381_, 2, v___x_3379_);
v___x_3382_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3382_, 0, v___x_3374_);
lean_ctor_set(v___x_3382_, 1, v___x_3381_);
v___x_3383_ = 0;
v___x_3384_ = l_Lean_Parser_nodeWithAntiquot(v___x_3372_, v___x_3373_, v___x_3382_, v___x_3383_);
v_fn_3385_ = lean_ctor_get(v___x_3384_, 1);
lean_inc_ref(v_fn_3385_);
lean_dec_ref(v___x_3384_);
v___x_3386_ = lean_apply_2(v_fn_3385_, v_a_3370_, v_a_3371_);
return v___x_3386_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_text___closed__0(void){
_start:
{
lean_object* v___x_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v___x_3387_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot), 2, 0);
v___x_3388_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_3389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3389_, 0, v___x_3388_);
lean_ctor_set(v___x_3389_, 1, v___x_3387_);
return v___x_3389_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_text(void){
_start:
{
lean_object* v___x_3390_; 
v___x_3390_ = lean_obj_once(&l_Lean_Doc_Parser_Inline_text___closed__0, &l_Lean_Doc_Parser_Inline_text___closed__0_once, _init_l_Lean_Doc_Parser_Inline_text___closed__0);
return v___x_3390_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1(){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3397_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0));
v___x_3398_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_emph___regBuiltin_Lean_Doc_Syntax_emph_docString__1___closed__0));
v___x_3399_ = l_Lean_addBuiltinDocString(v___x_3397_, v___x_3398_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1___boxed(lean_object* v_a_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1();
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1(){
_start:
{
lean_object* v___x_3408_; lean_object* v___x_3409_; lean_object* v___x_3410_; 
v___x_3408_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2));
v___x_3409_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_bold___regBuiltin_Lean_Doc_Syntax_bold_docString__1___closed__0));
v___x_3410_ = l_Lean_addBuiltinDocString(v___x_3408_, v___x_3409_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1___boxed(lean_object* v_a_3411_){
_start:
{
lean_object* v_res_3412_; 
v_res_3412_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1();
return v_res_3412_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1(){
_start:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; lean_object* v___x_3417_; 
v___x_3415_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1));
v___x_3416_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_code___regBuiltin_Lean_Doc_Syntax_code_docString__1___closed__0));
v___x_3417_ = l_Lean_addBuiltinDocString(v___x_3415_, v___x_3416_);
return v___x_3417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1___boxed(lean_object* v_a_3418_){
_start:
{
lean_object* v_res_3419_; 
v_res_3419_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1();
return v_res_3419_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_inline__math(void){
_start:
{
lean_object* v___x_3420_; 
v___x_3420_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2);
return v___x_3420_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1(){
_start:
{
lean_object* v___x_3422_; lean_object* v___x_3423_; lean_object* v___x_3424_; 
v___x_3422_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0));
v___x_3423_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_inline__math___regBuiltin_Lean_Doc_Syntax_inline__math_docString__1___closed__0));
v___x_3424_ = l_Lean_addBuiltinDocString(v___x_3422_, v___x_3423_);
return v___x_3424_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1___boxed(lean_object* v_a_3425_){
_start:
{
lean_object* v_res_3426_; 
v_res_3426_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1();
return v_res_3426_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_display__math(void){
_start:
{
lean_object* v___x_3427_; 
v___x_3427_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0);
return v___x_3427_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1(){
_start:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; 
v___x_3429_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0));
v___x_3430_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_display__math___regBuiltin_Lean_Doc_Syntax_display__math_docString__1___closed__0));
v___x_3431_ = l_Lean_addBuiltinDocString(v___x_3429_, v___x_3430_);
return v___x_3431_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1___boxed(lean_object* v_a_3432_){
_start:
{
lean_object* v_res_3433_; 
v_res_3433_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1();
return v_res_3433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1(){
_start:
{
lean_object* v___x_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; 
v___x_3440_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0));
v___x_3441_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link___regBuiltin_Lean_Doc_Syntax_link_docString__1___closed__0));
v___x_3442_ = l_Lean_addBuiltinDocString(v___x_3440_, v___x_3441_);
return v___x_3442_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1___boxed(lean_object* v_a_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1();
return v_res_3444_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_image___closed__0(void){
_start:
{
lean_object* v___x_3445_; lean_object* v___x_3446_; lean_object* v___x_3447_; 
v___x_3445_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot), 2, 0);
v___x_3446_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_3447_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3447_, 0, v___x_3446_);
lean_ctor_set(v___x_3447_, 1, v___x_3445_);
return v___x_3447_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_image(void){
_start:
{
lean_object* v___x_3448_; 
v___x_3448_ = lean_obj_once(&l_Lean_Doc_Parser_Inline_image___closed__0, &l_Lean_Doc_Parser_Inline_image___closed__0_once, _init_l_Lean_Doc_Parser_Inline_image___closed__0);
return v___x_3448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1(){
_start:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v___x_3452_; 
v___x_3450_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0));
v___x_3451_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_image___regBuiltin_Lean_Doc_Syntax_image_docString__1___closed__0));
v___x_3452_ = l_Lean_addBuiltinDocString(v___x_3450_, v___x_3451_);
return v___x_3452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1___boxed(lean_object* v_a_3453_){
_start:
{
lean_object* v_res_3454_; 
v_res_3454_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1();
return v_res_3454_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_footnote___closed__0(void){
_start:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
v___x_3455_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot), 2, 0);
v___x_3456_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_3457_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
lean_ctor_set(v___x_3457_, 1, v___x_3455_);
return v___x_3457_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_footnote(void){
_start:
{
lean_object* v___x_3458_; 
v___x_3458_ = lean_obj_once(&l_Lean_Doc_Parser_Inline_footnote___closed__0, &l_Lean_Doc_Parser_Inline_footnote___closed__0_once, _init_l_Lean_Doc_Parser_Inline_footnote___closed__0);
return v___x_3458_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1(){
_start:
{
lean_object* v___x_3460_; lean_object* v___x_3461_; lean_object* v___x_3462_; 
v___x_3460_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0));
v___x_3461_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote___regBuiltin_Lean_Doc_Syntax_footnote_docString__1___closed__0));
v___x_3462_ = l_Lean_addBuiltinDocString(v___x_3460_, v___x_3461_);
return v___x_3462_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1___boxed(lean_object* v_a_3463_){
_start:
{
lean_object* v_res_3464_; 
v_res_3464_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1();
return v_res_3464_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_linebreak___closed__0(void){
_start:
{
lean_object* v___x_3465_; lean_object* v___x_3466_; lean_object* v___x_3467_; 
v___x_3465_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot), 2, 0);
v___x_3466_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_3467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3467_, 0, v___x_3466_);
lean_ctor_set(v___x_3467_, 1, v___x_3465_);
return v___x_3467_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_linebreak(void){
_start:
{
lean_object* v___x_3468_; 
v___x_3468_ = lean_obj_once(&l_Lean_Doc_Parser_Inline_linebreak___closed__0, &l_Lean_Doc_Parser_Inline_linebreak___closed__0_once, _init_l_Lean_Doc_Parser_Inline_linebreak___closed__0);
return v___x_3468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1(){
_start:
{
lean_object* v___x_3475_; lean_object* v___x_3476_; lean_object* v___x_3477_; 
v___x_3475_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0));
v___x_3476_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_role___regBuiltin_Lean_Doc_Syntax_role_docString__1___closed__0));
v___x_3477_ = l_Lean_addBuiltinDocString(v___x_3475_, v___x_3476_);
return v___x_3477_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1___boxed(lean_object* v_a_3478_){
_start:
{
lean_object* v_res_3479_; 
v_res_3479_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1();
return v_res_3479_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2(void){
_start:
{
lean_object* v___x_3492_; lean_object* v___x_3493_; 
v___x_3492_ = ((lean_object*)(l_Lean_Doc_Parser_inline___closed__1));
v___x_3493_ = l_Lean_Parser_atomic(v___x_3492_);
return v___x_3493_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3(void){
_start:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3494_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2);
v___x_3495_ = l_Lean_Parser_many1(v___x_3494_);
return v___x_3495_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4(void){
_start:
{
uint8_t v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; lean_object* v___x_3499_; lean_object* v___x_3500_; 
v___x_3496_ = 0;
v___x_3497_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3);
v___x_3498_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1));
v___x_3499_ = ((lean_object*)(l_Lean_Doc_Syntax_para___closed__0));
v___x_3500_ = l_Lean_Parser_nodeWithAntiquot(v___x_3499_, v___x_3498_, v___x_3497_, v___x_3496_);
return v___x_3500_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot(lean_object* v_a_3501_, lean_object* v_a_3502_){
_start:
{
lean_object* v___x_3503_; lean_object* v_fn_3504_; lean_object* v___x_3505_; 
v___x_3503_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4);
v_fn_3504_ = lean_ctor_get(v___x_3503_, 1);
lean_inc_ref(v_fn_3504_);
v___x_3505_ = lean_apply_2(v_fn_3504_, v_a_3501_, v_a_3502_);
return v___x_3505_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1(void){
_start:
{
lean_object* v___x_3512_; lean_object* v___x_3513_; lean_object* v___x_3514_; 
v___x_3512_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3);
v___x_3513_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2);
v___x_3514_ = l_Lean_Parser_andthen(v___x_3513_, v___x_3512_);
return v___x_3514_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2(void){
_start:
{
lean_object* v___x_3515_; lean_object* v___x_3516_; lean_object* v___x_3517_; 
v___x_3515_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1);
v___x_3516_ = l_Lean_Parser_ident;
v___x_3517_ = l_Lean_Parser_andthen(v___x_3516_, v___x_3515_);
return v___x_3517_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3(void){
_start:
{
lean_object* v___x_3518_; lean_object* v___x_3519_; lean_object* v___x_3520_; 
v___x_3518_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2);
v___x_3519_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1);
v___x_3520_ = l_Lean_Parser_andthen(v___x_3519_, v___x_3518_);
return v___x_3520_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4(void){
_start:
{
uint8_t v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; 
v___x_3521_ = 0;
v___x_3522_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3);
v___x_3523_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0));
v___x_3524_ = ((lean_object*)(l_Lean_Doc_Syntax_command___closed__0));
v___x_3525_ = l_Lean_Parser_nodeWithAntiquot(v___x_3524_, v___x_3523_, v___x_3522_, v___x_3521_);
return v___x_3525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot(lean_object* v_a_3526_, lean_object* v_a_3527_){
_start:
{
lean_object* v___x_3528_; lean_object* v_fn_3529_; lean_object* v___x_3530_; 
v___x_3528_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4);
v_fn_3529_ = lean_ctor_get(v___x_3528_, 1);
lean_inc_ref(v_fn_3529_);
v___x_3530_ = lean_apply_2(v_fn_3529_, v_a_3526_, v_a_3527_);
return v___x_3530_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1(void){
_start:
{
lean_object* v___x_3537_; lean_object* v___x_3538_; 
v___x_3537_ = ((lean_object*)(l_Lean_Doc_Syntax_metadata__block___closed__2));
v___x_3538_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_3537_);
return v___x_3538_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2(void){
_start:
{
lean_object* v___x_3539_; lean_object* v___x_3540_; lean_object* v___x_3541_; 
v___x_3539_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1);
v___x_3540_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit));
v___x_3541_ = l_Lean_Parser_andthen(v___x_3540_, v___x_3539_);
return v___x_3541_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3(void){
_start:
{
lean_object* v___x_3542_; lean_object* v___x_3543_; lean_object* v___x_3544_; 
v___x_3542_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2);
v___x_3543_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1);
v___x_3544_ = l_Lean_Parser_andthen(v___x_3543_, v___x_3542_);
return v___x_3544_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4(void){
_start:
{
uint8_t v___x_3545_; lean_object* v___x_3546_; lean_object* v___x_3547_; lean_object* v___x_3548_; lean_object* v___x_3549_; 
v___x_3545_ = 0;
v___x_3546_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3);
v___x_3547_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0));
v___x_3548_ = ((lean_object*)(l_Lean_Doc_Syntax_metadata__block___closed__0));
v___x_3549_ = l_Lean_Parser_nodeWithAntiquot(v___x_3548_, v___x_3547_, v___x_3546_, v___x_3545_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot(lean_object* v_a_3550_, lean_object* v_a_3551_){
_start:
{
lean_object* v___x_3552_; lean_object* v_fn_3553_; lean_object* v___x_3554_; 
v___x_3552_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4);
v_fn_3553_ = lean_ctor_get(v___x_3552_, 1);
lean_inc_ref(v_fn_3553_);
v___x_3554_ = lean_apply_2(v_fn_3553_, v_a_3550_, v_a_3551_);
return v___x_3554_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1(void){
_start:
{
lean_object* v___x_3561_; lean_object* v___x_3562_; 
v___x_3561_ = ((lean_object*)(l_Lean_Doc_Syntax_link__ref___closed__2));
v___x_3562_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_3561_);
return v___x_3562_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__2(void){
_start:
{
lean_object* v___x_3563_; lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3563_ = ((lean_object*)(l_Lean_Doc_Parser_versoLinkRefUrl));
v___x_3564_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1);
v___x_3565_ = l_Lean_Parser_andthen(v___x_3564_, v___x_3563_);
return v___x_3565_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3566_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__2);
v___x_3567_ = ((lean_object*)(l_Lean_Doc_Parser_versoRef));
v___x_3568_ = l_Lean_Parser_andthen(v___x_3567_, v___x_3566_);
return v___x_3568_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4(void){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3569_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3);
v___x_3570_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1);
v___x_3571_ = l_Lean_Parser_andthen(v___x_3570_, v___x_3569_);
return v___x_3571_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5(void){
_start:
{
uint8_t v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3572_ = 0;
v___x_3573_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4);
v___x_3574_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0));
v___x_3575_ = ((lean_object*)(l_Lean_Doc_Syntax_link__ref___closed__0));
v___x_3576_ = l_Lean_Parser_nodeWithAntiquot(v___x_3575_, v___x_3574_, v___x_3573_, v___x_3572_);
return v___x_3576_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot(lean_object* v_a_3577_, lean_object* v_a_3578_){
_start:
{
lean_object* v___x_3579_; lean_object* v_fn_3580_; lean_object* v___x_3581_; 
v___x_3579_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5);
v_fn_3580_ = lean_ctor_get(v___x_3579_, 1);
lean_inc_ref(v_fn_3580_);
v___x_3581_ = lean_apply_2(v_fn_3580_, v_a_3577_, v_a_3578_);
return v___x_3581_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1(void){
_start:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3588_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2);
v___x_3589_ = l_Lean_Parser_many(v___x_3588_);
return v___x_3589_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2(void){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3590_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1);
v___x_3591_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1);
v___x_3592_ = l_Lean_Parser_andthen(v___x_3591_, v___x_3590_);
return v___x_3592_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3(void){
_start:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3593_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2);
v___x_3594_ = ((lean_object*)(l_Lean_Doc_Parser_versoRef));
v___x_3595_ = l_Lean_Parser_andthen(v___x_3594_, v___x_3593_);
return v___x_3595_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4(void){
_start:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; lean_object* v___x_3598_; 
v___x_3596_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3);
v___x_3597_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1);
v___x_3598_ = l_Lean_Parser_andthen(v___x_3597_, v___x_3596_);
return v___x_3598_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5(void){
_start:
{
uint8_t v___x_3599_; lean_object* v___x_3600_; lean_object* v___x_3601_; lean_object* v___x_3602_; lean_object* v___x_3603_; 
v___x_3599_ = 0;
v___x_3600_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4);
v___x_3601_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0));
v___x_3602_ = ((lean_object*)(l_Lean_Doc_Syntax_footnote__ref___closed__0));
v___x_3603_ = l_Lean_Parser_nodeWithAntiquot(v___x_3602_, v___x_3601_, v___x_3600_, v___x_3599_);
return v___x_3603_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot(lean_object* v_a_3604_, lean_object* v_a_3605_){
_start:
{
lean_object* v___x_3606_; lean_object* v_fn_3607_; lean_object* v___x_3608_; 
v___x_3606_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5);
v_fn_3607_ = lean_ctor_get(v___x_3606_, 1);
lean_inc_ref(v_fn_3607_);
v___x_3608_ = lean_apply_2(v_fn_3607_, v_a_3604_, v_a_3605_);
return v___x_3608_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1(void){
_start:
{
lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; 
v___x_3615_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3);
v___x_3616_ = ((lean_object*)(l_Lean_Doc_Parser_headerMarker));
v___x_3617_ = l_Lean_Parser_andthen(v___x_3616_, v___x_3615_);
return v___x_3617_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2(void){
_start:
{
uint8_t v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; 
v___x_3618_ = 0;
v___x_3619_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1);
v___x_3620_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0));
v___x_3621_ = ((lean_object*)(l_Lean_Doc_Syntax_header___closed__0));
v___x_3622_ = l_Lean_Parser_nodeWithAntiquot(v___x_3621_, v___x_3620_, v___x_3619_, v___x_3618_);
return v___x_3622_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot(lean_object* v_a_3623_, lean_object* v_a_3624_){
_start:
{
lean_object* v___x_3625_; lean_object* v_fn_3626_; lean_object* v___x_3627_; 
v___x_3625_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2);
v_fn_3626_ = lean_ctor_get(v___x_3625_, 1);
lean_inc_ref(v_fn_3626_);
v___x_3627_ = lean_apply_2(v_fn_3626_, v_a_3623_, v_a_3624_);
return v___x_3627_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1(void){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3634_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2);
v___x_3635_ = l_Lean_Parser_ident;
v___x_3636_ = l_Lean_Parser_andthen(v___x_3635_, v___x_3634_);
return v___x_3636_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2(void){
_start:
{
lean_object* v___x_3637_; lean_object* v___x_3638_; 
v___x_3637_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1);
v___x_3638_ = l_Lean_Parser_optional(v___x_3637_);
return v___x_3638_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3(void){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; 
v___x_3639_ = ((lean_object*)(l_Lean_Doc_Parser_codeBlockFence));
v___x_3640_ = ((lean_object*)(l_Lean_Doc_Parser_versoCodeBlock));
v___x_3641_ = l_Lean_Parser_andthen(v___x_3640_, v___x_3639_);
return v___x_3641_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4(void){
_start:
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; 
v___x_3642_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3);
v___x_3643_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2);
v___x_3644_ = l_Lean_Parser_andthen(v___x_3643_, v___x_3642_);
return v___x_3644_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5(void){
_start:
{
lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3647_; 
v___x_3645_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4);
v___x_3646_ = ((lean_object*)(l_Lean_Doc_Parser_codeBlockFence));
v___x_3647_ = l_Lean_Parser_andthen(v___x_3646_, v___x_3645_);
return v___x_3647_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6(void){
_start:
{
uint8_t v___x_3648_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; 
v___x_3648_ = 0;
v___x_3649_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5);
v___x_3650_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0));
v___x_3651_ = ((lean_object*)(l_Lean_Doc_Syntax_codeblock___closed__0));
v___x_3652_ = l_Lean_Parser_nodeWithAntiquot(v___x_3651_, v___x_3650_, v___x_3649_, v___x_3648_);
return v___x_3652_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot(lean_object* v_a_3653_, lean_object* v_a_3654_){
_start:
{
lean_object* v___x_3655_; lean_object* v_fn_3656_; lean_object* v___x_3657_; 
v___x_3655_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6);
v_fn_3656_ = lean_ctor_get(v___x_3655_, 1);
lean_inc_ref(v_fn_3656_);
v___x_3657_ = lean_apply_2(v_fn_3656_, v_a_3653_, v_a_3654_);
return v___x_3657_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4(void){
_start:
{
lean_object* v___x_3676_; lean_object* v___x_3677_; 
v___x_3676_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__3));
v___x_3677_ = l_Lean_Parser_atomic(v___x_3676_);
return v___x_3677_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5(void){
_start:
{
lean_object* v___x_3678_; lean_object* v___x_3679_; 
v___x_3678_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4);
v___x_3679_ = l_Lean_Parser_many(v___x_3678_);
return v___x_3679_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot(lean_object* v_marker_3694_, lean_object* v_a_3695_, lean_object* v_a_3696_){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; lean_object* v___x_3700_; lean_object* v___x_3701_; lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; uint8_t v___x_3705_; lean_object* v___x_3706_; lean_object* v_fn_3707_; lean_object* v___x_3708_; 
v___x_3697_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__0));
v___x_3698_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3));
v___x_3699_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3700_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot), 2, 0);
v___x_3701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3701_, 0, v___x_3699_);
lean_ctor_set(v___x_3701_, 1, v___x_3700_);
v___x_3702_ = l_Lean_Parser_atomic(v___x_3701_);
v___x_3703_ = l_Lean_Parser_many(v___x_3702_);
v___x_3704_ = l_Lean_Parser_andthen(v_marker_3694_, v___x_3703_);
v___x_3705_ = 0;
v___x_3706_ = l_Lean_Parser_nodeWithAntiquot(v___x_3697_, v___x_3698_, v___x_3704_, v___x_3705_);
v_fn_3707_ = lean_ctor_get(v___x_3706_, 1);
lean_inc_ref(v_fn_3707_);
lean_dec_ref(v___x_3706_);
v___x_3708_ = lean_apply_2(v_fn_3707_, v_a_3695_, v_a_3696_);
return v___x_3708_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot(lean_object* v_a_3709_, lean_object* v_a_3710_){
_start:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; lean_object* v___x_3713_; lean_object* v___x_3714_; lean_object* v___x_3715_; lean_object* v___x_3716_; lean_object* v___x_3717_; lean_object* v___x_3718_; uint8_t v___x_3719_; lean_object* v___x_3720_; lean_object* v_fn_3721_; lean_object* v___x_3722_; 
v___x_3711_ = ((lean_object*)(l_Lean_Doc_Syntax_ul___closed__0));
v___x_3712_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0));
v___x_3713_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3714_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker));
v___x_3715_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot), 3, 1);
lean_closure_set(v___x_3715_, 0, v___x_3714_);
v___x_3716_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3713_);
lean_ctor_set(v___x_3716_, 1, v___x_3715_);
v___x_3717_ = l_Lean_Parser_atomic(v___x_3716_);
v___x_3718_ = l_Lean_Parser_many1(v___x_3717_);
v___x_3719_ = 0;
v___x_3720_ = l_Lean_Parser_nodeWithAntiquot(v___x_3711_, v___x_3712_, v___x_3718_, v___x_3719_);
v_fn_3721_ = lean_ctor_get(v___x_3720_, 1);
lean_inc_ref(v_fn_3721_);
lean_dec_ref(v___x_3720_);
v___x_3722_ = lean_apply_2(v_fn_3721_, v_a_3709_, v_a_3710_);
return v___x_3722_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot(lean_object* v_a_3729_, lean_object* v_a_3730_){
_start:
{
lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; lean_object* v___x_3735_; lean_object* v___x_3736_; lean_object* v___x_3737_; lean_object* v___x_3738_; uint8_t v___x_3739_; lean_object* v___x_3740_; lean_object* v_fn_3741_; lean_object* v___x_3742_; 
v___x_3731_ = ((lean_object*)(l_Lean_Doc_Syntax_ol___closed__0));
v___x_3732_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0));
v___x_3733_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3734_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker));
v___x_3735_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot), 3, 1);
lean_closure_set(v___x_3735_, 0, v___x_3734_);
v___x_3736_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3736_, 0, v___x_3733_);
lean_ctor_set(v___x_3736_, 1, v___x_3735_);
v___x_3737_ = l_Lean_Parser_atomic(v___x_3736_);
v___x_3738_ = l_Lean_Parser_many1(v___x_3737_);
v___x_3739_ = 0;
v___x_3740_ = l_Lean_Parser_nodeWithAntiquot(v___x_3731_, v___x_3732_, v___x_3738_, v___x_3739_);
v_fn_3741_ = lean_ctor_get(v___x_3740_, 1);
lean_inc_ref(v_fn_3741_);
lean_dec_ref(v___x_3740_);
v___x_3742_ = lean_apply_2(v_fn_3741_, v_a_3729_, v_a_3730_);
return v___x_3742_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1(void){
_start:
{
lean_object* v___x_3749_; lean_object* v___x_3750_; 
v___x_3749_ = ((lean_object*)(l_Lean_Doc_Syntax_blockquote___closed__2));
v___x_3750_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_3749_);
return v___x_3750_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot(lean_object* v_a_3751_, lean_object* v_a_3752_){
_start:
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___x_3756_; lean_object* v___x_3757_; lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; uint8_t v___x_3762_; lean_object* v___x_3763_; lean_object* v_fn_3764_; lean_object* v___x_3765_; 
v___x_3753_ = ((lean_object*)(l_Lean_Doc_Syntax_blockquote___closed__0));
v___x_3754_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0));
v___x_3755_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1);
v___x_3756_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3757_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot), 2, 0);
v___x_3758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3758_, 0, v___x_3756_);
lean_ctor_set(v___x_3758_, 1, v___x_3757_);
v___x_3759_ = l_Lean_Parser_atomic(v___x_3758_);
v___x_3760_ = l_Lean_Parser_many(v___x_3759_);
v___x_3761_ = l_Lean_Parser_andthen(v___x_3755_, v___x_3760_);
v___x_3762_ = 0;
v___x_3763_ = l_Lean_Parser_nodeWithAntiquot(v___x_3753_, v___x_3754_, v___x_3761_, v___x_3762_);
v_fn_3764_ = lean_ctor_get(v___x_3763_, 1);
lean_inc_ref(v_fn_3764_);
lean_dec_ref(v___x_3763_);
v___x_3765_ = lean_apply_2(v_fn_3764_, v_a_3751_, v_a_3752_);
return v___x_3765_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0(void){
_start:
{
lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3766_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot), 2, 0);
v___x_3767_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3768_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3768_, 0, v___x_3767_);
lean_ctor_set(v___x_3768_, 1, v___x_3766_);
return v___x_3768_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot(lean_object* v_a_3775_, lean_object* v_a_3776_){
_start:
{
lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3779_; lean_object* v___x_3780_; lean_object* v___x_3781_; lean_object* v___x_3782_; lean_object* v___x_3783_; lean_object* v___x_3784_; lean_object* v___x_3785_; lean_object* v___x_3786_; lean_object* v___x_3787_; lean_object* v___x_3788_; lean_object* v___x_3789_; lean_object* v___x_3790_; uint8_t v___x_3791_; lean_object* v___x_3792_; lean_object* v_fn_3793_; lean_object* v___x_3794_; 
v___x_3777_ = ((lean_object*)(l_Lean_Doc_Syntax_directive___closed__0));
v___x_3778_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0));
v___x_3779_ = ((lean_object*)(l_Lean_Doc_Parser_directiveDelimiter));
v___x_3780_ = l_Lean_Parser_ident;
v___x_3781_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2);
v___x_3782_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3783_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot), 2, 0);
v___x_3784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3784_, 0, v___x_3782_);
lean_ctor_set(v___x_3784_, 1, v___x_3783_);
v___x_3785_ = l_Lean_Parser_atomic(v___x_3784_);
v___x_3786_ = l_Lean_Parser_many(v___x_3785_);
v___x_3787_ = l_Lean_Parser_andthen(v___x_3786_, v___x_3779_);
v___x_3788_ = l_Lean_Parser_andthen(v___x_3781_, v___x_3787_);
v___x_3789_ = l_Lean_Parser_andthen(v___x_3780_, v___x_3788_);
v___x_3790_ = l_Lean_Parser_andthen(v___x_3779_, v___x_3789_);
v___x_3791_ = 0;
v___x_3792_ = l_Lean_Parser_nodeWithAntiquot(v___x_3777_, v___x_3778_, v___x_3790_, v___x_3791_);
v_fn_3793_ = lean_ctor_get(v___x_3792_, 1);
lean_inc_ref(v_fn_3793_);
lean_dec_ref(v___x_3792_);
v___x_3794_ = lean_apply_2(v_fn_3793_, v_a_3775_, v_a_3776_);
return v___x_3794_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6(void){
_start:
{
uint8_t v___x_3800_; lean_object* v___x_3801_; lean_object* v___x_3802_; lean_object* v___x_3803_; 
v___x_3800_ = 1;
v___x_3801_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5));
v___x_3802_ = ((lean_object*)(l_Lean_Doc_Syntax_block_quot___closed__0));
v___x_3803_ = l_Lean_Parser_mkAntiquot(v___x_3802_, v___x_3801_, v___x_3800_, v___x_3800_);
return v___x_3803_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8(void){
_start:
{
lean_object* v___x_3804_; lean_object* v___x_3805_; lean_object* v___x_3806_; 
v___x_3804_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot), 2, 0);
v___x_3805_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3806_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3806_, 0, v___x_3805_);
lean_ctor_set(v___x_3806_, 1, v___x_3804_);
return v___x_3806_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7(void){
_start:
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; 
v___x_3807_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot), 2, 0);
v___x_3808_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3808_);
lean_ctor_set(v___x_3809_, 1, v___x_3807_);
return v___x_3809_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9(void){
_start:
{
lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; 
v___x_3810_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8);
v___x_3811_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7);
v___x_3812_ = l_Lean_Parser_orelse(v___x_3811_, v___x_3810_);
return v___x_3812_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4(void){
_start:
{
lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
v___x_3813_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot), 2, 0);
v___x_3814_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3815_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3814_);
lean_ctor_set(v___x_3815_, 1, v___x_3813_);
return v___x_3815_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10(void){
_start:
{
lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
v___x_3816_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9);
v___x_3817_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4);
v___x_3818_ = l_Lean_Parser_orelse(v___x_3817_, v___x_3816_);
return v___x_3818_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3(void){
_start:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3819_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot), 2, 0);
v___x_3820_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3821_, 0, v___x_3820_);
lean_ctor_set(v___x_3821_, 1, v___x_3819_);
return v___x_3821_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11(void){
_start:
{
lean_object* v___x_3822_; lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3822_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10);
v___x_3823_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3);
v___x_3824_ = l_Lean_Parser_orelse(v___x_3823_, v___x_3822_);
return v___x_3824_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2(void){
_start:
{
lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; 
v___x_3825_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot), 2, 0);
v___x_3826_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3827_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3826_);
lean_ctor_set(v___x_3827_, 1, v___x_3825_);
return v___x_3827_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12(void){
_start:
{
lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; 
v___x_3828_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11);
v___x_3829_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2);
v___x_3830_ = l_Lean_Parser_orelse(v___x_3829_, v___x_3828_);
return v___x_3830_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1(void){
_start:
{
lean_object* v___x_3831_; lean_object* v___x_3832_; lean_object* v___x_3833_; 
v___x_3831_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot), 2, 0);
v___x_3832_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3833_, 0, v___x_3832_);
lean_ctor_set(v___x_3833_, 1, v___x_3831_);
return v___x_3833_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13(void){
_start:
{
lean_object* v___x_3834_; lean_object* v___x_3835_; lean_object* v___x_3836_; 
v___x_3834_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12);
v___x_3835_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1);
v___x_3836_ = l_Lean_Parser_orelse(v___x_3835_, v___x_3834_);
return v___x_3836_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot(lean_object* v_c_3837_, lean_object* v_s_3838_){
_start:
{
lean_object* v___x_3839_; lean_object* v___x_3840_; lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; lean_object* v___x_3851_; lean_object* v_fn_3852_; lean_object* v___x_3853_; lean_object* v___x_3854_; lean_object* v___x_3855_; lean_object* v___x_3856_; lean_object* v___x_3857_; lean_object* v___x_3858_; lean_object* v_alts_3859_; lean_object* v_fn_3860_; uint8_t v___x_3861_; lean_object* v___x_3862_; 
v___x_3839_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3840_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot), 2, 0);
v___x_3841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3841_, 0, v___x_3839_);
lean_ctor_set(v___x_3841_, 1, v___x_3840_);
v___x_3842_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot), 2, 0);
v___x_3843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3839_);
lean_ctor_set(v___x_3843_, 1, v___x_3842_);
v___x_3844_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot), 2, 0);
v___x_3845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3839_);
lean_ctor_set(v___x_3845_, 1, v___x_3844_);
v___x_3846_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot), 2, 0);
v___x_3847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3839_);
lean_ctor_set(v___x_3847_, 1, v___x_3846_);
v___x_3848_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0);
v___x_3849_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot), 2, 0);
v___x_3850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3850_, 0, v___x_3839_);
lean_ctor_set(v___x_3850_, 1, v___x_3849_);
v___x_3851_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6);
v_fn_3852_ = lean_ctor_get(v___x_3851_, 1);
v___x_3853_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13);
v___x_3854_ = l_Lean_Parser_orelse(v___x_3850_, v___x_3853_);
v___x_3855_ = l_Lean_Parser_orelse(v___x_3848_, v___x_3854_);
v___x_3856_ = l_Lean_Parser_orelse(v___x_3847_, v___x_3855_);
v___x_3857_ = l_Lean_Parser_orelse(v___x_3845_, v___x_3856_);
v___x_3858_ = l_Lean_Parser_orelse(v___x_3843_, v___x_3857_);
v_alts_3859_ = l_Lean_Parser_orelse(v___x_3841_, v___x_3858_);
v_fn_3860_ = lean_ctor_get(v_alts_3859_, 1);
lean_inc_ref(v_fn_3860_);
lean_dec_ref(v_alts_3859_);
v___x_3861_ = 0;
lean_inc_ref(v_fn_3852_);
v___x_3862_ = l_Lean_Parser_withAntiquotFn(v_fn_3852_, v_fn_3860_, v___x_3861_, v_c_3837_, v_s_3838_);
return v___x_3862_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot(lean_object* v_a_3863_, lean_object* v_a_3864_){
_start:
{
lean_object* v___x_3865_; lean_object* v___x_3866_; lean_object* v___x_3867_; lean_object* v___x_3868_; lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; uint8_t v___x_3876_; lean_object* v___x_3877_; lean_object* v_fn_3878_; lean_object* v___x_3879_; 
v___x_3865_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__0));
v___x_3866_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2));
v___x_3867_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker));
v___x_3868_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3869_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5);
v___x_3870_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot), 2, 0);
v___x_3871_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3868_);
lean_ctor_set(v___x_3871_, 1, v___x_3870_);
v___x_3872_ = l_Lean_Parser_atomic(v___x_3871_);
v___x_3873_ = l_Lean_Parser_many(v___x_3872_);
v___x_3874_ = l_Lean_Parser_andthen(v___x_3869_, v___x_3873_);
v___x_3875_ = l_Lean_Parser_andthen(v___x_3867_, v___x_3874_);
v___x_3876_ = 0;
v___x_3877_ = l_Lean_Parser_nodeWithAntiquot(v___x_3865_, v___x_3866_, v___x_3875_, v___x_3876_);
v_fn_3878_ = lean_ctor_get(v___x_3877_, 1);
lean_inc_ref(v_fn_3878_);
lean_dec_ref(v___x_3877_);
v___x_3879_ = lean_apply_2(v_fn_3878_, v_a_3863_, v_a_3864_);
return v___x_3879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot(lean_object* v_a_3880_, lean_object* v_a_3881_){
_start:
{
lean_object* v___x_3882_; lean_object* v___x_3883_; lean_object* v___x_3884_; lean_object* v___x_3885_; lean_object* v___x_3886_; lean_object* v___x_3887_; lean_object* v___x_3888_; uint8_t v___x_3889_; lean_object* v___x_3890_; lean_object* v_fn_3891_; lean_object* v___x_3892_; 
v___x_3882_ = ((lean_object*)(l_Lean_Doc_Syntax_dl___closed__0));
v___x_3883_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0));
v___x_3884_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_3885_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot), 2, 0);
v___x_3886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3886_, 0, v___x_3884_);
lean_ctor_set(v___x_3886_, 1, v___x_3885_);
v___x_3887_ = l_Lean_Parser_atomic(v___x_3886_);
v___x_3888_ = l_Lean_Parser_many1(v___x_3887_);
v___x_3889_ = 0;
v___x_3890_ = l_Lean_Parser_nodeWithAntiquot(v___x_3882_, v___x_3883_, v___x_3888_, v___x_3889_);
v_fn_3891_ = lean_ctor_get(v___x_3890_, 1);
lean_inc_ref(v_fn_3891_);
lean_dec_ref(v___x_3890_);
v___x_3892_ = lean_apply_2(v_fn_3891_, v_a_3880_, v_a_3881_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1(){
_start:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3900_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3));
v___x_3901_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_li___regBuiltin_Lean_Doc_Syntax_li_docString__1___closed__0));
v___x_3902_ = l_Lean_addBuiltinDocString(v___x_3900_, v___x_3901_);
return v___x_3902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1___boxed(lean_object* v_a_3903_){
_start:
{
lean_object* v_res_3904_; 
v_res_3904_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1();
return v_res_3904_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1(){
_start:
{
lean_object* v___x_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3911_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2));
v___x_3912_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_desc___regBuiltin_Lean_Doc_Syntax_desc_docString__1___closed__0));
v___x_3913_ = l_Lean_addBuiltinDocString(v___x_3911_, v___x_3912_);
return v___x_3913_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1___boxed(lean_object* v_a_3914_){
_start:
{
lean_object* v_res_3915_; 
v_res_3915_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1();
return v_res_3915_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_para___closed__0(void){
_start:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; lean_object* v___x_3918_; 
v___x_3916_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot), 2, 0);
v___x_3917_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_3918_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3918_, 0, v___x_3917_);
lean_ctor_set(v___x_3918_, 1, v___x_3916_);
return v___x_3918_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_para(void){
_start:
{
lean_object* v___x_3919_; 
v___x_3919_ = lean_obj_once(&l_Lean_Doc_Parser_Block_para___closed__0, &l_Lean_Doc_Parser_Block_para___closed__0_once, _init_l_Lean_Doc_Parser_Block_para___closed__0);
return v___x_3919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1(){
_start:
{
lean_object* v___x_3921_; lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3921_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1));
v___x_3922_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_para___regBuiltin_Lean_Doc_Syntax_para_docString__1___closed__0));
v___x_3923_ = l_Lean_addBuiltinDocString(v___x_3921_, v___x_3922_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1___boxed(lean_object* v_a_3924_){
_start:
{
lean_object* v_res_3925_; 
v_res_3925_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1();
return v_res_3925_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1(){
_start:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; 
v___x_3932_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0));
v___x_3933_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ul___regBuiltin_Lean_Doc_Syntax_ul_docString__1___closed__0));
v___x_3934_ = l_Lean_addBuiltinDocString(v___x_3932_, v___x_3933_);
return v___x_3934_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1___boxed(lean_object* v_a_3935_){
_start:
{
lean_object* v_res_3936_; 
v_res_3936_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1();
return v_res_3936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1(){
_start:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3943_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0));
v___x_3944_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_ol___regBuiltin_Lean_Doc_Syntax_ol_docString__1___closed__0));
v___x_3945_ = l_Lean_addBuiltinDocString(v___x_3943_, v___x_3944_);
return v___x_3945_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1___boxed(lean_object* v_a_3946_){
_start:
{
lean_object* v_res_3947_; 
v_res_3947_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1();
return v_res_3947_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1(){
_start:
{
lean_object* v___x_3954_; lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3954_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0));
v___x_3955_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_dl___regBuiltin_Lean_Doc_Syntax_dl_docString__1___closed__0));
v___x_3956_ = l_Lean_addBuiltinDocString(v___x_3954_, v___x_3955_);
return v___x_3956_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1___boxed(lean_object* v_a_3957_){
_start:
{
lean_object* v_res_3958_; 
v_res_3958_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1();
return v_res_3958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1(){
_start:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v___x_3967_; 
v___x_3965_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0));
v___x_3966_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_blockquote___regBuiltin_Lean_Doc_Syntax_blockquote_docString__1___closed__0));
v___x_3967_ = l_Lean_addBuiltinDocString(v___x_3965_, v___x_3966_);
return v___x_3967_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1___boxed(lean_object* v_a_3968_){
_start:
{
lean_object* v_res_3969_; 
v_res_3969_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1();
return v_res_3969_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_codeblock___closed__0(void){
_start:
{
lean_object* v___x_3970_; lean_object* v___x_3971_; lean_object* v___x_3972_; 
v___x_3970_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot), 2, 0);
v___x_3971_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_3972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3972_, 0, v___x_3971_);
lean_ctor_set(v___x_3972_, 1, v___x_3970_);
return v___x_3972_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_codeblock(void){
_start:
{
lean_object* v___x_3973_; 
v___x_3973_ = lean_obj_once(&l_Lean_Doc_Parser_Block_codeblock___closed__0, &l_Lean_Doc_Parser_Block_codeblock___closed__0_once, _init_l_Lean_Doc_Parser_Block_codeblock___closed__0);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1(){
_start:
{
lean_object* v___x_3975_; lean_object* v___x_3976_; lean_object* v___x_3977_; 
v___x_3975_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0));
v___x_3976_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_codeblock___regBuiltin_Lean_Doc_Syntax_codeblock_docString__1___closed__0));
v___x_3977_ = l_Lean_addBuiltinDocString(v___x_3975_, v___x_3976_);
return v___x_3977_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1___boxed(lean_object* v_a_3978_){
_start:
{
lean_object* v_res_3979_; 
v_res_3979_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1();
return v_res_3979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1(){
_start:
{
lean_object* v___x_3986_; lean_object* v___x_3987_; lean_object* v___x_3988_; 
v___x_3986_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0));
v___x_3987_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_directive___regBuiltin_Lean_Doc_Syntax_directive_docString__1___closed__0));
v___x_3988_ = l_Lean_addBuiltinDocString(v___x_3986_, v___x_3987_);
return v___x_3988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1___boxed(lean_object* v_a_3989_){
_start:
{
lean_object* v_res_3990_; 
v_res_3990_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1();
return v_res_3990_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_header___closed__0(void){
_start:
{
lean_object* v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3991_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot), 2, 0);
v___x_3992_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_3993_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3992_);
lean_ctor_set(v___x_3993_, 1, v___x_3991_);
return v___x_3993_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_header(void){
_start:
{
lean_object* v___x_3994_; 
v___x_3994_ = lean_obj_once(&l_Lean_Doc_Parser_Block_header___closed__0, &l_Lean_Doc_Parser_Block_header___closed__0_once, _init_l_Lean_Doc_Parser_Block_header___closed__0);
return v___x_3994_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1(){
_start:
{
lean_object* v___x_3996_; lean_object* v___x_3997_; lean_object* v___x_3998_; 
v___x_3996_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0));
v___x_3997_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_header___regBuiltin_Lean_Doc_Syntax_header_docString__1___closed__0));
v___x_3998_ = l_Lean_addBuiltinDocString(v___x_3996_, v___x_3997_);
return v___x_3998_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1___boxed(lean_object* v_a_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1();
return v_res_4000_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_link__ref___closed__0(void){
_start:
{
lean_object* v___x_4001_; lean_object* v___x_4002_; lean_object* v___x_4003_; 
v___x_4001_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot), 2, 0);
v___x_4002_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_4003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4003_, 0, v___x_4002_);
lean_ctor_set(v___x_4003_, 1, v___x_4001_);
return v___x_4003_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_link__ref(void){
_start:
{
lean_object* v___x_4004_; 
v___x_4004_ = lean_obj_once(&l_Lean_Doc_Parser_Block_link__ref___closed__0, &l_Lean_Doc_Parser_Block_link__ref___closed__0_once, _init_l_Lean_Doc_Parser_Block_link__ref___closed__0);
return v___x_4004_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1(){
_start:
{
lean_object* v___x_4006_; lean_object* v___x_4007_; lean_object* v___x_4008_; 
v___x_4006_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0));
v___x_4007_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_link__ref___regBuiltin_Lean_Doc_Syntax_link__ref_docString__1___closed__0));
v___x_4008_ = l_Lean_addBuiltinDocString(v___x_4006_, v___x_4007_);
return v___x_4008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1___boxed(lean_object* v_a_4009_){
_start:
{
lean_object* v_res_4010_; 
v_res_4010_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1();
return v_res_4010_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_footnote__ref___closed__0(void){
_start:
{
lean_object* v___x_4011_; lean_object* v___x_4012_; lean_object* v___x_4013_; 
v___x_4011_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot), 2, 0);
v___x_4012_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_4013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4013_, 0, v___x_4012_);
lean_ctor_set(v___x_4013_, 1, v___x_4011_);
return v___x_4013_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_footnote__ref(void){
_start:
{
lean_object* v___x_4014_; 
v___x_4014_ = lean_obj_once(&l_Lean_Doc_Parser_Block_footnote__ref___closed__0, &l_Lean_Doc_Parser_Block_footnote__ref___closed__0_once, _init_l_Lean_Doc_Parser_Block_footnote__ref___closed__0);
return v___x_4014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1(){
_start:
{
lean_object* v___x_4016_; lean_object* v___x_4017_; lean_object* v___x_4018_; 
v___x_4016_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0));
v___x_4017_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_footnote__ref___regBuiltin_Lean_Doc_Syntax_footnote__ref_docString__1___closed__0));
v___x_4018_ = l_Lean_addBuiltinDocString(v___x_4016_, v___x_4017_);
return v___x_4018_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1___boxed(lean_object* v_a_4019_){
_start:
{
lean_object* v_res_4020_; 
v_res_4020_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1();
return v_res_4020_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_metadata__block___closed__0(void){
_start:
{
lean_object* v___x_4021_; lean_object* v___x_4022_; lean_object* v___x_4023_; 
v___x_4021_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot), 2, 0);
v___x_4022_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_4023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4023_, 0, v___x_4022_);
lean_ctor_set(v___x_4023_, 1, v___x_4021_);
return v___x_4023_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_metadata__block(void){
_start:
{
lean_object* v___x_4024_; 
v___x_4024_ = lean_obj_once(&l_Lean_Doc_Parser_Block_metadata__block___closed__0, &l_Lean_Doc_Parser_Block_metadata__block___closed__0_once, _init_l_Lean_Doc_Parser_Block_metadata__block___closed__0);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1(){
_start:
{
lean_object* v___x_4026_; lean_object* v___x_4027_; lean_object* v___x_4028_; 
v___x_4026_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0));
v___x_4027_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_metadata__block___regBuiltin_Lean_Doc_Syntax_metadata__block_docString__1___closed__0));
v___x_4028_ = l_Lean_addBuiltinDocString(v___x_4026_, v___x_4027_);
return v___x_4028_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1___boxed(lean_object* v_a_4029_){
_start:
{
lean_object* v_res_4030_; 
v_res_4030_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1();
return v_res_4030_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_command___closed__0(void){
_start:
{
lean_object* v___x_4031_; lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4031_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot), 2, 0);
v___x_4032_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_4033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4032_);
lean_ctor_set(v___x_4033_, 1, v___x_4031_);
return v___x_4033_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_command(void){
_start:
{
lean_object* v___x_4034_; 
v___x_4034_ = lean_obj_once(&l_Lean_Doc_Parser_Block_command___closed__0, &l_Lean_Doc_Parser_Block_command___closed__0_once, _init_l_Lean_Doc_Parser_Block_command___closed__0);
return v___x_4034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1(){
_start:
{
lean_object* v___x_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
v___x_4036_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0));
v___x_4037_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Syntax_command___regBuiltin_Lean_Doc_Syntax_command_docString__1___closed__0));
v___x_4038_ = l_Lean_addBuiltinDocString(v___x_4036_, v___x_4037_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1___boxed(lean_object* v_a_4039_){
_start:
{
lean_object* v_res_4040_; 
v_res_4040_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1();
return v_res_4040_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_document___lam__0___closed__2(void){
_start:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4052_ = ((lean_object*)(l_Lean_Doc_Parser_block));
v___x_4053_ = l_Lean_Parser_atomic(v___x_4052_);
return v___x_4053_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_document___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4054_ = lean_obj_once(&l_Lean_Doc_Parser_document___lam__0___closed__2, &l_Lean_Doc_Parser_document___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_document___lam__0___closed__2);
v___x_4055_ = l_Lean_Parser_many(v___x_4054_);
return v___x_4055_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_document___lam__0___closed__4(void){
_start:
{
uint8_t v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4056_ = 0;
v___x_4057_ = lean_obj_once(&l_Lean_Doc_Parser_document___lam__0___closed__3, &l_Lean_Doc_Parser_document___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_document___lam__0___closed__3);
v___x_4058_ = ((lean_object*)(l_Lean_Doc_Parser_document___lam__0___closed__1));
v___x_4059_ = ((lean_object*)(l_Lean_Doc_Parser_document___lam__0___closed__0));
v___x_4060_ = l_Lean_Parser_nodeWithAntiquot(v___x_4059_, v___x_4058_, v___x_4057_, v___x_4056_);
return v___x_4060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document___lam__0(lean_object* v_c_4061_, lean_object* v_s_4062_){
_start:
{
lean_object* v___x_4063_; lean_object* v_fn_4064_; lean_object* v___x_4065_; 
v___x_4063_ = lean_obj_once(&l_Lean_Doc_Parser_document___lam__0___closed__4, &l_Lean_Doc_Parser_document___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_document___lam__0___closed__4);
v_fn_4064_ = lean_ctor_get(v___x_4063_, 1);
lean_inc_ref(v_fn_4064_);
v___x_4065_ = lean_apply_2(v_fn_4064_, v_c_4061_, v_s_4062_);
return v___x_4065_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0(size_t v_sz_4071_, size_t v_i_4072_, lean_object* v_bs_4073_){
_start:
{
uint8_t v___x_4074_; 
v___x_4074_ = lean_usize_dec_lt(v_i_4072_, v_sz_4071_);
if (v___x_4074_ == 0)
{
return v_bs_4073_;
}
else
{
lean_object* v_v_4075_; lean_object* v___x_4076_; lean_object* v_bs_x27_4077_; size_t v___x_4078_; size_t v___x_4079_; lean_object* v___x_4080_; 
v_v_4075_ = lean_array_uget(v_bs_4073_, v_i_4072_);
v___x_4076_ = lean_unsigned_to_nat(0u);
v_bs_x27_4077_ = lean_array_uset(v_bs_4073_, v_i_4072_, v___x_4076_);
v___x_4078_ = ((size_t)1ULL);
v___x_4079_ = lean_usize_add(v_i_4072_, v___x_4078_);
v___x_4080_ = lean_array_uset(v_bs_x27_4077_, v_i_4072_, v_v_4075_);
v_i_4072_ = v___x_4079_;
v_bs_4073_ = v___x_4080_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0___boxed(lean_object* v_sz_4082_, lean_object* v_i_4083_, lean_object* v_bs_4084_){
_start:
{
size_t v_sz_boxed_4085_; size_t v_i_boxed_4086_; lean_object* v_res_4087_; 
v_sz_boxed_4085_ = lean_unbox_usize(v_sz_4082_);
lean_dec(v_sz_4082_);
v_i_boxed_4086_ = lean_unbox_usize(v_i_4083_);
lean_dec(v_i_4083_);
v_res_4087_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0(v_sz_boxed_4085_, v_i_boxed_4086_, v_bs_4084_);
return v_res_4087_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoBlocks(lean_object* v_doc_4088_){
_start:
{
lean_object* v___x_4089_; lean_object* v___x_4090_; lean_object* v___x_4091_; size_t v_sz_4092_; size_t v___x_4093_; lean_object* v___x_4094_; 
v___x_4089_ = lean_unsigned_to_nat(0u);
v___x_4090_ = l_Lean_Syntax_getArg(v_doc_4088_, v___x_4089_);
v___x_4091_ = l_Lean_Syntax_getArgs(v___x_4090_);
lean_dec(v___x_4090_);
v_sz_4092_ = lean_array_size(v___x_4091_);
v___x_4093_ = ((size_t)0ULL);
v___x_4094_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0(v_sz_4092_, v___x_4093_, v___x_4091_);
return v___x_4094_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoBlocks___boxed(lean_object* v_doc_4095_){
_start:
{
lean_object* v_res_4096_; 
v_res_4096_ = l_Lean_TSyntax_getVersoBlocks(v_doc_4095_);
lean_dec(v_doc_4095_);
return v_res_4096_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoDelimiter(lean_object* v_delim_4097_){
_start:
{
lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4098_ = lean_unsigned_to_nat(0u);
v___x_4099_ = l_Lean_Syntax_getArg(v_delim_4097_, v___x_4098_);
v___x_4100_ = l_Lean_Syntax_getAtomVal(v___x_4099_);
lean_dec(v___x_4099_);
return v___x_4100_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoDelimiter___boxed(lean_object* v_delim_4101_){
_start:
{
lean_object* v_res_4102_; 
v_res_4102_ = l_Lean_TSyntax_getVersoDelimiter(v_delim_4101_);
lean_dec(v_delim_4101_);
return v_res_4102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoDocument_view(lean_object* v_doc_4103_){
_start:
{
lean_object* v___x_4104_; 
v___x_4104_ = l_Lean_TSyntax_getVersoBlocks(v_doc_4103_);
return v___x_4104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoDocument_view___boxed(lean_object* v_doc_4105_){
_start:
{
lean_object* v_res_4106_; 
v_res_4106_ = l_Lean_Doc_VersoDocument_view(v_doc_4105_);
lean_dec(v_doc_4105_);
return v_res_4106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoDelimiter_view(lean_object* v_delim_4107_){
_start:
{
lean_object* v___x_4108_; 
v___x_4108_ = l_Lean_TSyntax_getVersoDelimiter(v_delim_4107_);
return v___x_4108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoDelimiter_view___boxed(lean_object* v_delim_4109_){
_start:
{
lean_object* v_res_4110_; 
v_res_4110_ = l_Lean_Doc_VersoDelimiter_view(v_delim_4109_);
lean_dec(v_delim_4109_);
return v_res_4110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___lam__0(lean_object* v_s_4113_){
_start:
{
lean_inc(v_s_4113_);
return v_s_4113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___lam__0___boxed(lean_object* v_s_4114_){
_start:
{
lean_object* v_res_4115_; 
v_res_4115_ = l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___lam__0(v_s_4114_);
lean_dec(v_s_4114_);
return v_res_4115_;
}
}
lean_object* runtime_initialize_Lean_Parser_Term_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_DocString_Types(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DocString_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DocString_Types(builtin);
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
l_Lean_Doc_escapeVersoLinkUrl___closed__0___boxed__const__1 = _init_l_Lean_Doc_escapeVersoLinkUrl___closed__0___boxed__const__1();
lean_mark_persistent(l_Lean_Doc_escapeVersoLinkUrl___closed__0___boxed__const__1);
l_Lean_Doc_escapeVersoImageAlt___closed__0___boxed__const__1 = _init_l_Lean_Doc_escapeVersoImageAlt___closed__0___boxed__const__1();
lean_mark_persistent(l_Lean_Doc_escapeVersoImageAlt___closed__0___boxed__const__1);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2___boxed__const__1 = _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2___boxed__const__1);
l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___boxed__const__1 = _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___boxed__const__1);
l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___boxed__const__1 = _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___boxed__const__1);
l_Lean_Doc_Parser_Inline_text = _init_l_Lean_Doc_Parser_Inline_text();
lean_mark_persistent(l_Lean_Doc_Parser_Inline_text);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Inline_inline__math = _init_l_Lean_Doc_Parser_Inline_inline__math();
lean_mark_persistent(l_Lean_Doc_Parser_Inline_inline__math);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Inline_display__math = _init_l_Lean_Doc_Parser_Inline_display__math();
lean_mark_persistent(l_Lean_Doc_Parser_Inline_display__math);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Inline_image = _init_l_Lean_Doc_Parser_Inline_image();
lean_mark_persistent(l_Lean_Doc_Parser_Inline_image);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Inline_footnote = _init_l_Lean_Doc_Parser_Inline_footnote();
lean_mark_persistent(l_Lean_Doc_Parser_Inline_footnote);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Inline_linebreak = _init_l_Lean_Doc_Parser_Inline_linebreak();
lean_mark_persistent(l_Lean_Doc_Parser_Inline_linebreak);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Block_para = _init_l_Lean_Doc_Parser_Block_para();
lean_mark_persistent(l_Lean_Doc_Parser_Block_para);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Block_codeblock = _init_l_Lean_Doc_Parser_Block_codeblock();
lean_mark_persistent(l_Lean_Doc_Parser_Block_codeblock);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Block_header = _init_l_Lean_Doc_Parser_Block_header();
lean_mark_persistent(l_Lean_Doc_Parser_Block_header);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Block_link__ref = _init_l_Lean_Doc_Parser_Block_link__ref();
lean_mark_persistent(l_Lean_Doc_Parser_Block_link__ref);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Block_footnote__ref = _init_l_Lean_Doc_Parser_Block_footnote__ref();
lean_mark_persistent(l_Lean_Doc_Parser_Block_footnote__ref);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Block_metadata__block = _init_l_Lean_Doc_Parser_Block_metadata__block();
lean_mark_persistent(l_Lean_Doc_Parser_Block_metadata__block);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Doc_Parser_Block_command = _init_l_Lean_Doc_Parser_Block_command();
lean_mark_persistent(l_Lean_Doc_Parser_Block_command);
res = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1();
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
lean_object* initialize_Lean_DocString_Types(uint8_t builtin);
lean_object* initialize_Lean_Parser_Term_Basic(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DocString_Syntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Term_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_DocString_Types(builtin);
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
