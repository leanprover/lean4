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
lean_object* l_Lean_Parser_symbol(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* l_Lean_Parser_satisfyFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthenFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_string_length(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_string_utf8_byte_size(lean_object*);
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_ident;
extern lean_object* l_Lean_Parser_numLit;
extern lean_object* l_Lean_Parser_strLit;
lean_object* l_Lean_Parser_node(lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_skip;
lean_object* l_Lean_Parser_many1(lean_object*);
lean_object* l_Lean_Parser_withAntiquotFn(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Syntax_isLit_x3f(lean_object*, lean_object*);
lean_object* l_Lean_Data_Trie_insert___redArg(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_pushNone;
lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
lean_object* l_Lean_Parser_checkColEq(lean_object*);
extern lean_object* l_Lean_Parser_Term_structInstField;
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkColGe(lean_object*);
lean_object* l_Lean_Parser_sepBy(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_withPosition(lean_object*);
lean_object* l_Lean_Parser_Term_structInstFields(lean_object*);
lean_object* l_Lean_Parser_adaptUncacheableContextFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_satisfyFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_notFollowedBy(lean_object*, lean_object*);
lean_object* l_Lean_Parser_optional(lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Syntax_getAtomVal(lean_object*);
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_id___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_id___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___closed__0_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___closed__0_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse(lean_object*);
static const lean_string_object l_Lean_Doc_Parser_versoText___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "versoText"};
static const lean_object* l_Lean_Doc_Parser_versoText___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__0_value;
static const lean_string_object l_Lean_Doc_Parser_versoText___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Doc_Parser_versoText___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_versoText___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Doc"};
static const lean_object* l_Lean_Doc_Parser_versoText___lam__0___closed__2 = (const lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value;
static const lean_string_object l_Lean_Doc_Parser_versoText___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Doc_Parser_versoText___lam__0___closed__3 = (const lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Doc_Parser_versoText___lam__0___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoText___lam__0___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__4_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoText___lam__0___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__4_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoText___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__4_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 255, 240, 17, 75, 250, 253, 95)}};
static const lean_object* l_Lean_Doc_Parser_versoText___lam__0___closed__4 = (const lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Doc_Parser_versoText___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_versoText___lam__0___closed__5;
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
static const lean_ctor_object l_Lean_Doc_Parser_versoRef___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoRef___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoRef___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoRef___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoRef___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
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
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
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
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
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
static const lean_ctor_object l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
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
static const lean_ctor_object l_Lean_Doc_Parser_versoCode___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCode___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCode___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCode___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCode___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
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
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
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
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
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
LEAN_EXPORT const lean_object* l_Lean_Doc_versoTextKind = (const lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__4_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoRefKind = (const lean_object*)&l_Lean_Doc_Parser_versoRef___lam__0___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoLinkUrlKind = (const lean_object*)&l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoLinkRefUrlKind = (const lean_object*)&l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoImageAltKind = (const lean_object*)&l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoCodeKind = (const lean_object*)&l_Lean_Doc_Parser_versoCode___lam__0___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoCodeLineKind = (const lean_object*)&l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_versoCodeBlockKind = (const lean_object*)&l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__1_value;
static const lean_string_object l_Lean_Doc_parseFailureKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "parseFailure"};
static const lean_object* l_Lean_Doc_parseFailureKind___closed__0 = (const lean_object*)&l_Lean_Doc_parseFailureKind___closed__0_value;
static const lean_ctor_object l_Lean_Doc_parseFailureKind___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_parseFailureKind___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_parseFailureKind___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_parseFailureKind___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_parseFailureKind___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
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
static const lean_string_object l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "str"};
static const lean_object* l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__2 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__3_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(41, 57, 249, 217, 203, 152, 202, 12)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__3_value_aux_3),((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(165, 66, 72, 255, 161, 123, 180, 197)}};
static const lean_object* l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__3 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__3_value;
static lean_once_cell_t l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_ArgVal_str___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_ArgVal_str___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_ArgVal_str___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_ArgVal_str___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_str___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_str___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_ArgVal_str___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_str___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_ArgVal_str = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_str___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ArgVal.ident"};
static const lean_object* l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__0_value;
static const lean_string_object l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(41, 57, 249, 217, 203, 152, 202, 12)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__2_value_aux_3),((lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(46, 191, 138, 67, 72, 90, 15, 127)}};
static const lean_object* l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__2 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_ArgVal_ident___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_ArgVal_ident___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_ArgVal_ident___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_ArgVal_ident___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_ident___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_ArgVal_ident___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_ArgVal_ident = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_ident___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "ArgVal.num"};
static const lean_object* l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__0_value;
static const lean_string_object l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(41, 57, 249, 217, 203, 152, 202, 12)}};
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__2_value_aux_3),((lean_object*)&l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(233, 188, 228, 197, 246, 25, 189, 153)}};
static const lean_object* l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__2 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_ArgVal_num___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_ArgVal_num___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_ArgVal_num___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_ArgVal_num___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_num___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_ArgVal_num___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_ArgVal_num___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_ArgVal_num___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_num___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_ArgVal_num = (const lean_object*)&l_Lean_Doc_Parser_ArgVal_num___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_argVal___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "argVal"};
static const lean_object* l_Lean_Doc_Parser_argVal___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_argVal___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_argVal___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_argVal___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_argVal___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_argVal___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_argVal___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
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
static const lean_string_object l_Lean_Doc_Parser_Arg_anon___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "anon"};
static const lean_object* l_Lean_Doc_Parser_Arg_anon___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__0_value;
static const lean_string_object l_Lean_Doc_Parser_Arg_anon___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Arg"};
static const lean_object* l_Lean_Doc_Parser_Arg_anon___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Doc_Parser_Arg_anon___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_anon___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_anon___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_anon___lam__0___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_anon___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__2_value_aux_3),((lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(108, 126, 223, 228, 215, 141, 22, 177)}};
static const lean_object* l_Lean_Doc_Parser_Arg_anon___lam__0___closed__2 = (const lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_anon___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_anon___lam__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_anon___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Arg_anon___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_Arg_anon___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Arg_anon___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_anon___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Arg_anon___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Arg_anon___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Arg_anon___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Arg_anon___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Arg_anon = (const lean_object*)&l_Lean_Doc_Parser_Arg_anon___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "Anonymous positional argument"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Parser_Arg_named___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "named"};
static const lean_object* l_Lean_Doc_Parser_Arg_named___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_named___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named___lam__0___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named___lam__0___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_Parser_Arg_named___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(195, 213, 136, 95, 26, 15, 91, 243)}};
static const lean_object* l_Lean_Doc_Parser_Arg_named___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Arg_named___lam__0___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_Arg_named___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Lean_Doc_Parser_Arg_named___lam__0___closed__2 = (const lean_object*)&l_Lean_Doc_Parser_Arg_named___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___lam__0___closed__3;
static const lean_string_object l_Lean_Doc_Parser_Arg_named___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_Doc_Parser_Arg_named___lam__0___closed__4 = (const lean_object*)&l_Lean_Doc_Parser_Arg_named___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___lam__0___closed__5;
static const lean_string_object l_Lean_Doc_Parser_Arg_named___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Lean_Doc_Parser_Arg_named___lam__0___closed__6 = (const lean_object*)&l_Lean_Doc_Parser_Arg_named___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___lam__0___closed__7;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___lam__0___closed__8;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___lam__0___closed__9;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___lam__0___closed__10;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___lam__0___closed__11;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named___lam__0___closed__12;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_named___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Arg_named___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_Arg_named___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Arg_named___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_named___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Arg_named___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Arg_named___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Arg_named___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Arg_named = (const lean_object*)&l_Lean_Doc_Parser_Arg_named___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Named argument"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "named_no_paren"};
static const lean_object* l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 130, 4, 13, 153, 240, 131, 1)}};
static const lean_object* l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__1_value;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__2;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__4;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_named__no__paren___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Arg_named__no__paren___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_Arg_named__no__paren___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Arg_named__no__paren___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Arg_named__no__paren___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Arg_named__no__paren___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Arg_named__no__paren = (const lean_object*)&l_Lean_Doc_Parser_Arg_named__no__paren___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "flag_on"};
static const lean_object* l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 11, 92, 179, 92, 210, 69, 32)}};
static const lean_object* l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__2 = (const lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__4;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_flag__on___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Arg_flag__on___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_Arg_flag__on___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Arg_flag__on___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__on___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Arg_flag__on___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Arg_flag__on = (const lean_object*)&l_Lean_Doc_Parser_Arg_flag__on___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Boolean flag, turned on"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "flag_off"};
static const lean_object* l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(66, 217, 102, 251, 143, 78, 17, 105)}};
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 14, 2, 143, 165, 169, 65, 229)}};
static const lean_object* l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__2 = (const lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__4;
static lean_once_cell_t l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_flag__off___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Arg_flag__off___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_Arg_flag__off___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Arg_flag__off___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Arg_flag__off___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Arg_flag__off___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Arg_flag__off = (const lean_object*)&l_Lean_Doc_Parser_Arg_flag__off___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "Boolean flag, turned off"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Parser_arg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "arg"};
static const lean_object* l_Lean_Doc_Parser_arg___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_arg___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_arg___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_arg___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_arg___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_arg___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_arg___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
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
static const lean_string_object l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "url"};
static const lean_object* l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__0_value;
static const lean_string_object l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "LinkTarget"};
static const lean_object* l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__1_value;
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__2_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(13, 244, 114, 61, 113, 148, 117, 178)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__2_value_aux_3),((lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(57, 222, 147, 211, 241, 202, 7, 251)}};
static const lean_object* l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__2 = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__3;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__4;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__5;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_LinkTarget_url___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_LinkTarget_url___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_LinkTarget_url___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_LinkTarget_url___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_url___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_LinkTarget_url___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_LinkTarget_url = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "A URL target, written explicitly. Use square brackets for a named target."};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "ref"};
static const lean_object* l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__1_value_aux_2),((lean_object*)&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(13, 244, 114, 61, 113, 148, 117, 178)}};
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__1_value_aux_3),((lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 54, 241, 38, 78, 206, 156, 5)}};
static const lean_object* l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__2 = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__3;
static const lean_string_object l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__4 = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__5;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__6;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__7;
static lean_once_cell_t l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_LinkTarget_ref___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_LinkTarget_ref___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Doc_Parser_LinkTarget_ref___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_LinkTarget_ref___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_LinkTarget_ref___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_LinkTarget_ref___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_LinkTarget_ref = (const lean_object*)&l_Lean_Doc_Parser_LinkTarget_ref___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 85, .m_capacity = 85, .m_length = 84, .m_data = "A named reference to a URL defined elsewhere. Use parentheses to write the URL here."};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1___boxed(lean_object*);
static const lean_string_object l_Lean_Doc_Parser_linkTarget___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "linkTarget"};
static const lean_object* l_Lean_Doc_Parser_linkTarget___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_linkTarget___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_linkTarget___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_linkTarget___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_linkTarget___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_linkTarget___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_linkTarget___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__0(uint32_t, uint32_t);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__1(uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "%%%"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__0___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__0(lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "metadataContents"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "structInstFields"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__2_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__3_value_aux_1),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__3_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(0, 82, 141, 43, 62, 171, 163, 69)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__3 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__3_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__4;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__5 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__5_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__6;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sepBy"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__7 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__7_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(196, 56, 254, 223, 11, 70, 55, 147)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__8 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__8_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__9 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__9_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__10;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__11;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "irrelevant"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__12 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__12_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__13;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__14;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__15;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "line break"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__16 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__16_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__17;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__18;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__19;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__20;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__21;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__22;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__23;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__24_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__24;
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
static const lean_ctor_object l_Lean_Doc_Parser_headerMarker___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_headerMarker___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_headerMarker___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_headerMarker___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_headerMarker___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
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
static const lean_ctor_object l_Lean_Doc_Parser_listMarker___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_listMarker___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_listMarker___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_listMarker___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_listMarker___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
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
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__0_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__1;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "':'"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__2_value;
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
static const lean_ctor_object l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
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
static const lean_ctor_object l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
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
static const lean_ctor_object l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
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
static const lean_ctor_object l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
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
static const lean_ctor_object l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
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
static const lean_ctor_object l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
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
static const lean_ctor_object l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
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
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "code"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Inline"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__0_value),LEAN_SCALAR_PTR_LITERAL(232, 30, 73, 79, 76, 254, 8, 196)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__3___boxed__const__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__1_value),((lean_object*)&l_Lean_Doc_Parser_versoText___closed__2_value)} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1_value;
LEAN_EXPORT const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "linebreak"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(175, 150, 35, 119, 78, 160, 253, 84)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "image"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(63, 170, 102, 209, 119, 14, 254, 233)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "!["};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__2_value;
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
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__8;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "footnote"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 121, 147, 210, 143, 103, 0, 217)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "[^"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__2_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__5;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "inline_math"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 236, 9, 179, 133, 206, 252, 7)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "display_math"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(194, 39, 73, 53, 10, 24, 181, 77)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__3;
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
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "text"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(223, 133, 107, 199, 31, 216, 160, 200)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1___boxed(lean_object*);
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__0_value;
static const lean_closure_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "bold"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(162, 21, 54, 220, 135, 144, 211, 134)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__0_value),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___boxed__const__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "emph"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__1_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(47, 215, 18, 85, 144, 91, 153, 50)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "link"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 237, 8, 103, 58, 149, 183, 251)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__2;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "inline"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4_value),LEAN_SCALAR_PTR_LITERAL(8, 108, 76, 164, 130, 208, 234, 146)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__7;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "role"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__1_value),LEAN_SCALAR_PTR_LITERAL(42, 167, 130, 205, 218, 188, 181, 74)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(163, 233, 178, 241, 96, 238, 218, 92)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__5 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__5_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__7 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__7_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__7_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__9;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__10;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__11;
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
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 120, .m_capacity = 120, .m_length = 119, .m_data = "Emphasis, often rendered as italics.\n\nEmphasis may be nested by using longer sequences of `_` for the outer delimiters."};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Inline_bold___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Inline_bold___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Inline_bold___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Inline_bold___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Inline_bold___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Inline_bold___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Inline_bold___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Inline_bold = (const lean_object*)&l_Lean_Doc_Parser_Inline_bold___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 163, .m_capacity = 163, .m_length = 162, .m_data = "Bold emphasis.\n\nA single `*` suffices to make text bold. Use `_` for emphasis.\n\nBold text may be nested by using longer sequences of `*` for the outer delimiters."};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1___boxed(lean_object*);
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Inline_code = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 447, .m_capacity = 447, .m_length = 446, .m_data = "Literal code.\n\nCode may begin with any non-zero number of backticks. It must be terminated with the same number,\nand it may not contain a sequence of backticks that is at least as long as its starting or ending\ndelimiters.\n\nIf the first and last characters are space, and it contains at least one non-space character, then\nthe resulting string has a single space stripped from each end. Thus, ``` `` `x `` ``` represents\n``\"`x\"``, not ``\" `x \"``."};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Inline_inline__math;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = "Inline mathematical notation (equivalent to LaTeX's `$` notation)"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Inline_display__math;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Display-mode mathematical notation"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Inline_link___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Inline_link___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Inline_link___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Inline_link___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Inline_link___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Inline_link___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Inline_link___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Inline_link = (const lean_object*)&l_Lean_Doc_Parser_Inline_link___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 125, .m_capacity = 125, .m_length = 124, .m_data = "A link. The link's target may either be a concrete URL (written in parentheses) or a named URL\n(written in square brackets)."};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Inline_image___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Inline_image___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Inline_image;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 220, .m_capacity = 220, .m_length = 219, .m_data = "An image, with alternate text and a URL.\n\nThe alternate text is a plain string, rather than Verso markup.\n\nThe image URL may either be a concrete URL (written in parentheses) or a named URL (written in\nsquare brackets)."};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Inline_footnote___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Inline_footnote___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Inline_footnote;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 92, .m_capacity = 92, .m_length = 91, .m_data = "A footnote use site.\n\nFootnotes must be defined elsewhere using the `[^NAME]: TEXT` syntax."};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1___closed__0_value;
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
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 763, .m_capacity = 763, .m_length = 762, .m_data = "A _role_ is an extension to the Verso document language in an inline position.\n\nText is given a role using the following syntax: `{NAME ARGS*}[CONTENT]`. The `NAME` is an\nidentifier that determines which role is being used, akin to a function name. Each of the `ARGS` may\nhave the following forms:\n* A value, which is a string literal, natural number, or identifier\n* A named argument, of the form `(NAME := VALUE)`\n* A flag, of the form `+NAME` or `-NAME`\n\nThe `CONTENT` is a sequence of inline content. If there is only one piece of content and it has\nbeginning and ending delimiters (e.g. code literals, links, or images, but not ordinary text), then\nthe `[` and `]` may be omitted. In particular, `` {NAME ARGS*}`x` `` is equivalent to\n``{NAME ARGS*}[`x`]``."};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_inline___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_inline___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_inline___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_inline___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_inline___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_inline___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_inline___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_inline = (const lean_object*)&l_Lean_Doc_Parser_inline___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "para"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "Block"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(10, 167, 213, 66, 92, 160, 222, 146)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "command"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(11, 232, 253, 29, 141, 75, 139, 21)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "metadata_block"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(99, 125, 116, 48, 167, 45, 110, 42)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__5;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "link_ref"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(141, 199, 233, 128, 119, 237, 18, 215)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "]:"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__2_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__6;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "footnote_ref"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(97, 53, 29, 246, 154, 171, 121, 154)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__6;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(242, 176, 128, 73, 36, 235, 244, 141)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "codeblock"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 32, 43, 99, 217, 167, 97, 87)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1_value;
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
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__7;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "dl"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__1_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(165, 15, 76, 66, 114, 120, 124, 74)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "DescItem.item"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "item"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__2_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "DescItem"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__1_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(99, 70, 30, 3, 105, 156, 130, 115)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(37, 193, 144, 210, 183, 212, 114, 89)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4_value),((lean_object*)&l_Lean_Doc_Parser_inline___closed__0_value)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__3 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__3_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ul"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__1_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(144, 45, 1, 212, 241, 159, 201, 84)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ListItem.item"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__0_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ListItem"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__1_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(154, 153, 101, 209, 126, 16, 11, 208)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__2_value),LEAN_SCALAR_PTR_LITERAL(200, 123, 16, 134, 76, 179, 171, 228)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "ol"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__1_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(222, 199, 227, 191, 40, 60, 185, 243)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "blockquote"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(130, 145, 178, 243, 42, 6, 105, 104)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ">"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__2 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__2_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__3;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "directive"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__1_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__1_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__1_value),LEAN_SCALAR_PTR_LITERAL(205, 190, 169, 215, 54, 10, 232, 8)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__1_value_aux_3),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0_value),LEAN_SCALAR_PTR_LITERAL(211, 234, 1, 42, 159, 198, 19, 176)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__1 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot(lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "block"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5_value;
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
static const lean_ctor_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6_value_aux_2),((lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5_value),LEAN_SCALAR_PTR_LITERAL(183, 72, 202, 40, 103, 170, 246, 9)}};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6_value;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1;
static lean_once_cell_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__14;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_ListItem_item___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_listMarker___closed__1_value)} };
static const lean_object* l_Lean_Doc_Parser_ListItem_item___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_ListItem_item___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_ListItem_item___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_ListItem_item___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_ListItem_item___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_ListItem_item___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_ListItem_item = (const lean_object*)&l_Lean_Doc_Parser_ListItem_item___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "A list item"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_DescItem_item___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_DescItem_item___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_DescItem_item___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_DescItem_item___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_DescItem_item___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_DescItem_item___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_DescItem_item___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_DescItem_item = (const lean_object*)&l_Lean_Doc_Parser_DescItem_item___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "A description of an item"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Block_para___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Block_para___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Block_para;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Paragraph"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Block_ul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Block_ul___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Block_ul___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Block_ul___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Block_ul___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Block_ul___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Block_ul___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Block_ul = (const lean_object*)&l_Lean_Doc_Parser_Block_ul___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Unordered List"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Block_ol___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Block_ol___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Block_ol___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Block_ol___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Block_ol___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Block_ol___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Block_ol___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Block_ol = (const lean_object*)&l_Lean_Doc_Parser_Block_ol___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Ordered list"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Block_dl___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Block_dl___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Block_dl___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Block_dl___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Block_dl___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Block_dl___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Block_dl___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Block_dl = (const lean_object*)&l_Lean_Doc_Parser_Block_dl___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Description list"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Block_blockquote___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Block_blockquote___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Block_blockquote___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Block_blockquote___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Block_blockquote___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Block_blockquote___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Block_blockquote___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Block_blockquote = (const lean_object*)&l_Lean_Doc_Parser_Block_blockquote___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 91, .m_capacity = 91, .m_length = 90, .m_data = "A quotation, which contains a sequence of blocks that are at least as indented as the `>`."};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Block_codeblock___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Block_codeblock___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Block_codeblock;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1332, .m_capacity = 1332, .m_length = 1331, .m_data = "A code block that contains literal code. The contents of a code block are not written in Verso\nsyntax.\n\nCode blocks have the following syntax:\n````\n```(NAME ARGS*)\?\nCONTENT\n```\n````\n\n`CONTENT` is a literal string. If the `CONTENT` contains a sequence of three or more backticks, then\nthe opening and closing ` ``` ` (called _fences_) must have more backticks than the longest\nsequence in `CONTENT`. Additionally, the opening and closing fences must have the same number of\nbackticks.\n\nIf `NAME` and `ARGS` are not provided, then the code block represents literal text. If provided, the\n`NAME` is an identifier that selects an interpretation of the block. Unlike Markdown, this name is\nnot necessarily the language in which the code is written, though many custom code blocks are, in\npractice, named after the language that they contain. `NAME` is more akin to a function name that\ndetermines the interpretation of the code block's contents. Each of the `ARGS` may have the\nfollowing forms:\n* A value, which is a string literal, natural number, or identifier\n* A named argument, of the form `(NAME := VALUE)`\n* A flag, of the form `+NAME` or `-NAME`\n\nThe `CONTENT` is interpreted according to the indentation of the fences. If the fences are indented\n`n` spaces, then `n` spaces are removed from the start of each line of `CONTENT`."};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_Block_directive___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_Block_directive___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_Block_directive___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_Block_directive___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_Block_directive___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_Block_directive___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_Block_directive___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_Block_directive = (const lean_object*)&l_Lean_Doc_Parser_Block_directive___closed__1_value;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 730, .m_capacity = 730, .m_length = 729, .m_data = "A _directive_, which is an extension to the Verso language in block position. The contents of a\ndirective are written in Verso syntax.\n\nDirectives have the following syntax:\n```\n:::NAME ARGS*\nCONTENT*\n:::\n```\n\nThe `NAME` is an identifier that determines which directive is being used, akin to a function name.\nEach of the `ARGS` may have the following forms:\n* A value, which is a string literal, natural number, or identifier\n* A named argument, of the form `(NAME := VALUE)`\n* A flag, of the form `+NAME` or `-NAME`\n\nThe `CONTENT` is a sequence of block content. Directives may be nested by using more colons in\nthe outer directive. For example:\n```\n::::outer +flag (arg := 5)\nA paragraph.\n:::inner \"label\"\n* 1\n* 2\n:::\n::::\n```"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Block_header___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Block_header___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Block_header;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 202, .m_capacity = 202, .m_length = 201, .m_data = "A header\n\nHeaders must be correctly nested to form a tree structure. The first header in a document must\nstart with `#`, and subsequent headers must have at most one more `#` than the preceding header."};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Block_link__ref___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Block_link__ref___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Block_link__ref;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 50, .m_capacity = 50, .m_length = 49, .m_data = "A named URL that can be used in links and images."};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Block_footnote__ref___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Block_footnote__ref___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Block_footnote__ref;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A footnote definition."};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Block_metadata__block___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Block_metadata__block___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Block_metadata__block;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Metadata for the preceding header."};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1___boxed(lean_object*);
static lean_once_cell_t l_Lean_Doc_Parser_Block_command___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Doc_Parser_Block_command___closed__0;
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Block_command;
static const lean_string_object l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 390, .m_capacity = 390, .m_length = 389, .m_data = "A block-level command, which invokes an extension during documentation processing.\n\nThe `NAME` is an identifier that determines which command is being used, akin to a function name.\nEach of the `ARGS` may have the following forms:\n* A value, which is a string literal, natural number, or identifier\n* A named argument, of the form `(NAME := VALUE)`\n* A flag, of the form `+NAME` or `-NAME`"};
static const lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1___closed__0 = (const lean_object*)&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1();
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1___boxed(lean_object*);
static const lean_closure_object l_Lean_Doc_Parser_block___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Doc_Parser_block___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_block___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_block___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_versoText___closed__3_value),((lean_object*)&l_Lean_Doc_Parser_block___closed__0_value)}};
static const lean_object* l_Lean_Doc_Parser_block___closed__1 = (const lean_object*)&l_Lean_Doc_Parser_block___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Doc_Parser_block = (const lean_object*)&l_Lean_Doc_Parser_block___closed__1_value;
static const lean_string_object l_Lean_Doc_Parser_document___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "document"};
static const lean_object* l_Lean_Doc_Parser_document___lam__0___closed__0 = (const lean_object*)&l_Lean_Doc_Parser_document___lam__0___closed__0_value;
static const lean_ctor_object l_Lean_Doc_Parser_document___lam__0___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__1_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Doc_Parser_document___lam__0___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_document___lam__0___closed__1_value_aux_0),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__2_value),LEAN_SCALAR_PTR_LITERAL(78, 12, 7, 185, 212, 110, 129, 118)}};
static const lean_ctor_object l_Lean_Doc_Parser_document___lam__0___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Doc_Parser_document___lam__0___closed__1_value_aux_1),((lean_object*)&l_Lean_Doc_Parser_versoText___lam__0___closed__3_value),LEAN_SCALAR_PTR_LITERAL(191, 226, 227, 15, 42, 238, 219, 32)}};
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
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___lam__0(lean_object* v_p_1_, lean_object* v_c_2_, lean_object* v_s_3_){
_start:
{
lean_object* v___x_4_; lean_object* v___x_5_; lean_object* v_fn_6_; lean_object* v___x_7_; 
v___x_4_ = lean_box(0);
v___x_5_ = lean_apply_1(v_p_1_, v___x_4_);
v_fn_6_ = lean_ctor_get(v___x_5_, 1);
lean_inc_ref(v_fn_6_);
lean_dec_ref(v___x_5_);
v___x_7_ = lean_apply_2(v_fn_6_, v_c_2_, v_s_3_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse(lean_object* v_p_12_){
_start:
{
lean_object* v___f_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v___f_13_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___lam__0), 3, 1);
lean_closure_set(v___f_13_, 0, v_p_12_);
v___x_14_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_onFirstUse___closed__1));
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v___x_14_);
lean_ctor_set(v___x_15_, 1, v___f_13_);
return v___x_15_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoText___lam__0___closed__5(void){
_start:
{
uint8_t v___x_25_; uint8_t v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v___x_25_ = 0;
v___x_26_ = 1;
v___x_27_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___lam__0___closed__4));
v___x_28_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___lam__0___closed__0));
v___x_29_ = l_Lean_Parser_mkAntiquot(v___x_28_, v___x_27_, v___x_26_, v___x_25_);
return v___x_29_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoText___lam__0(lean_object* v_c_30_, lean_object* v_s_31_){
_start:
{
lean_object* v___x_32_; lean_object* v_fn_33_; lean_object* v___x_34_; 
v___x_32_ = lean_obj_once(&l_Lean_Doc_Parser_versoText___lam__0___closed__5, &l_Lean_Doc_Parser_versoText___lam__0___closed__5_once, _init_l_Lean_Doc_Parser_versoText___lam__0___closed__5);
v_fn_33_ = lean_ctor_get(v___x_32_, 1);
lean_inc_ref(v_fn_33_);
v___x_34_ = lean_apply_2(v_fn_33_, v_c_30_, v_s_31_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoText___lam__1(lean_object* v___y_35_){
_start:
{
lean_inc(v___y_35_);
return v___y_35_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoText___lam__1___boxed(lean_object* v___y_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Doc_Parser_versoText___lam__1(v___y_36_);
lean_dec(v___y_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoText___lam__2(lean_object* v___y_38_){
_start:
{
lean_inc_ref(v___y_38_);
return v___y_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoText___lam__2___boxed(lean_object* v___y_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_Lean_Doc_Parser_versoText___lam__2(v___y_39_);
lean_dec_ref(v___y_39_);
return v_res_40_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoRef___lam__0___closed__2(void){
_start:
{
uint8_t v___x_58_; uint8_t v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_58_ = 0;
v___x_59_ = 1;
v___x_60_ = ((lean_object*)(l_Lean_Doc_Parser_versoRef___lam__0___closed__1));
v___x_61_ = ((lean_object*)(l_Lean_Doc_Parser_versoRef___lam__0___closed__0));
v___x_62_ = l_Lean_Parser_mkAntiquot(v___x_61_, v___x_60_, v___x_59_, v___x_58_);
return v___x_62_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoRef___lam__0(lean_object* v_c_63_, lean_object* v_s_64_){
_start:
{
lean_object* v___x_65_; lean_object* v_fn_66_; lean_object* v___x_67_; 
v___x_65_ = lean_obj_once(&l_Lean_Doc_Parser_versoRef___lam__0___closed__2, &l_Lean_Doc_Parser_versoRef___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_versoRef___lam__0___closed__2);
v_fn_66_ = lean_ctor_get(v___x_65_, 1);
lean_inc_ref(v_fn_66_);
v___x_67_ = lean_apply_2(v_fn_66_, v_c_63_, v_s_64_);
return v___x_67_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__2(void){
_start:
{
uint8_t v___x_79_; uint8_t v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_79_ = 0;
v___x_80_ = 1;
v___x_81_ = ((lean_object*)(l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__1));
v___x_82_ = ((lean_object*)(l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__0));
v___x_83_ = l_Lean_Parser_mkAntiquot(v___x_82_, v___x_81_, v___x_80_, v___x_79_);
return v___x_83_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoLinkUrl___lam__0(lean_object* v_c_84_, lean_object* v_s_85_){
_start:
{
lean_object* v___x_86_; lean_object* v_fn_87_; lean_object* v___x_88_; 
v___x_86_ = lean_obj_once(&l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__2, &l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_versoLinkUrl___lam__0___closed__2);
v_fn_87_ = lean_ctor_get(v___x_86_, 1);
lean_inc_ref(v_fn_87_);
v___x_88_ = lean_apply_2(v_fn_87_, v_c_84_, v_s_85_);
return v___x_88_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__2(void){
_start:
{
uint8_t v___x_100_; uint8_t v___x_101_; lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_104_; 
v___x_100_ = 0;
v___x_101_ = 1;
v___x_102_ = ((lean_object*)(l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__1));
v___x_103_ = ((lean_object*)(l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__0));
v___x_104_ = l_Lean_Parser_mkAntiquot(v___x_103_, v___x_102_, v___x_101_, v___x_100_);
return v___x_104_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoLinkRefUrl___lam__0(lean_object* v_c_105_, lean_object* v_s_106_){
_start:
{
lean_object* v___x_107_; lean_object* v_fn_108_; lean_object* v___x_109_; 
v___x_107_ = lean_obj_once(&l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__2, &l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_versoLinkRefUrl___lam__0___closed__2);
v_fn_108_ = lean_ctor_get(v___x_107_, 1);
lean_inc_ref(v_fn_108_);
v___x_109_ = lean_apply_2(v_fn_108_, v_c_105_, v_s_106_);
return v___x_109_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__2(void){
_start:
{
uint8_t v___x_121_; uint8_t v___x_122_; lean_object* v___x_123_; lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_121_ = 0;
v___x_122_ = 1;
v___x_123_ = ((lean_object*)(l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__1));
v___x_124_ = ((lean_object*)(l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__0));
v___x_125_ = l_Lean_Parser_mkAntiquot(v___x_124_, v___x_123_, v___x_122_, v___x_121_);
return v___x_125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoImageAlt___lam__0(lean_object* v_c_126_, lean_object* v_s_127_){
_start:
{
lean_object* v___x_128_; lean_object* v_fn_129_; lean_object* v___x_130_; 
v___x_128_ = lean_obj_once(&l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__2, &l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_versoImageAlt___lam__0___closed__2);
v_fn_129_ = lean_ctor_get(v___x_128_, 1);
lean_inc_ref(v_fn_129_);
v___x_130_ = lean_apply_2(v_fn_129_, v_c_126_, v_s_127_);
return v___x_130_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoCode___lam__0___closed__2(void){
_start:
{
uint8_t v___x_142_; uint8_t v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_142_ = 0;
v___x_143_ = 1;
v___x_144_ = ((lean_object*)(l_Lean_Doc_Parser_versoCode___lam__0___closed__1));
v___x_145_ = ((lean_object*)(l_Lean_Doc_Parser_versoCode___lam__0___closed__0));
v___x_146_ = l_Lean_Parser_mkAntiquot(v___x_145_, v___x_144_, v___x_143_, v___x_142_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoCode___lam__0(lean_object* v_c_147_, lean_object* v_s_148_){
_start:
{
lean_object* v___x_149_; lean_object* v_fn_150_; lean_object* v___x_151_; 
v___x_149_ = lean_obj_once(&l_Lean_Doc_Parser_versoCode___lam__0___closed__2, &l_Lean_Doc_Parser_versoCode___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_versoCode___lam__0___closed__2);
v_fn_150_ = lean_ctor_get(v___x_149_, 1);
lean_inc_ref(v_fn_150_);
v___x_151_ = lean_apply_2(v_fn_150_, v_c_147_, v_s_148_);
return v___x_151_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__2(void){
_start:
{
uint8_t v___x_163_; uint8_t v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_163_ = 0;
v___x_164_ = 1;
v___x_165_ = ((lean_object*)(l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__1));
v___x_166_ = ((lean_object*)(l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__0));
v___x_167_ = l_Lean_Parser_mkAntiquot(v___x_166_, v___x_165_, v___x_164_, v___x_163_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoCodeLine___lam__0(lean_object* v_c_168_, lean_object* v_s_169_){
_start:
{
lean_object* v___x_170_; lean_object* v_fn_171_; lean_object* v___x_172_; 
v___x_170_ = lean_obj_once(&l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__2, &l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_versoCodeLine___lam__0___closed__2);
v_fn_171_ = lean_ctor_get(v___x_170_, 1);
lean_inc_ref(v_fn_171_);
v___x_172_ = lean_apply_2(v_fn_171_, v_c_168_, v_s_169_);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__2(void){
_start:
{
uint8_t v___x_184_; uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_184_ = 0;
v___x_185_ = 1;
v___x_186_ = ((lean_object*)(l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__1));
v___x_187_ = ((lean_object*)(l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__0));
v___x_188_ = l_Lean_Parser_mkAntiquot(v___x_187_, v___x_186_, v___x_185_, v___x_184_);
return v___x_188_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_versoCodeBlock___lam__0(lean_object* v_c_189_, lean_object* v_s_190_){
_start:
{
lean_object* v___x_191_; lean_object* v_fn_192_; lean_object* v___x_193_; 
v___x_191_ = lean_obj_once(&l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__2, &l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_versoCodeBlock___lam__0___closed__2);
v_fn_192_ = lean_ctor_get(v___x_191_, 1);
lean_inc_ref(v_fn_192_);
v___x_193_ = lean_apply_2(v_fn_192_, v_c_189_, v_s_190_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg(lean_object* v___x_214_, lean_object* v_str_215_, lean_object* v_a_216_, lean_object* v_b_217_){
_start:
{
uint8_t v_decide_218_; 
v_decide_218_ = lean_nat_dec_eq(v_a_216_, v___x_214_);
if (v_decide_218_ == 0)
{
lean_object* v_fst_219_; lean_object* v_snd_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_244_; 
v_fst_219_ = lean_ctor_get(v_b_217_, 0);
v_snd_220_ = lean_ctor_get(v_b_217_, 1);
v_isSharedCheck_244_ = !lean_is_exclusive(v_b_217_);
if (v_isSharedCheck_244_ == 0)
{
v___x_222_ = v_b_217_;
v_isShared_223_ = v_isSharedCheck_244_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_snd_220_);
lean_inc(v_fst_219_);
lean_dec(v_b_217_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_244_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
uint32_t v___x_224_; lean_object* v___x_225_; uint32_t v___x_226_; uint8_t v___x_227_; 
v___x_224_ = lean_string_utf8_get_fast(v_str_215_, v_a_216_);
v___x_225_ = lean_string_utf8_next_fast(v_str_215_, v_a_216_);
lean_dec(v_a_216_);
v___x_226_ = 96;
v___x_227_ = lean_uint32_dec_eq(v___x_224_, v___x_226_);
if (v___x_227_ == 0)
{
lean_object* v_best_228_; lean_object* v___x_230_; 
lean_dec(v_snd_220_);
v_best_228_ = lean_unsigned_to_nat(0u);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 1, v_best_228_);
v___x_230_ = v___x_222_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_fst_219_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_best_228_);
v___x_230_ = v_reuseFailAlloc_232_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
v_a_216_ = v___x_225_;
v_b_217_ = v___x_230_;
goto _start;
}
}
else
{
lean_object* v___x_233_; lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_233_ = lean_unsigned_to_nat(1u);
v___x_234_ = lean_nat_add(v_snd_220_, v___x_233_);
lean_dec(v_snd_220_);
v___x_235_ = lean_nat_dec_lt(v_fst_219_, v___x_234_);
if (v___x_235_ == 0)
{
lean_object* v___x_237_; 
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 1, v___x_234_);
v___x_237_ = v___x_222_;
goto v_reusejp_236_;
}
else
{
lean_object* v_reuseFailAlloc_239_; 
v_reuseFailAlloc_239_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_239_, 0, v_fst_219_);
lean_ctor_set(v_reuseFailAlloc_239_, 1, v___x_234_);
v___x_237_ = v_reuseFailAlloc_239_;
goto v_reusejp_236_;
}
v_reusejp_236_:
{
v_a_216_ = v___x_225_;
v_b_217_ = v___x_237_;
goto _start;
}
}
else
{
lean_object* v___x_241_; 
lean_dec(v_fst_219_);
lean_inc(v___x_234_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 1, v___x_234_);
lean_ctor_set(v___x_222_, 0, v___x_234_);
v___x_241_ = v___x_222_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___x_234_);
v___x_241_ = v_reuseFailAlloc_243_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
v_a_216_ = v___x_225_;
v_b_217_ = v___x_241_;
goto _start;
}
}
}
}
}
else
{
lean_dec(v_a_216_);
return v_b_217_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg___boxed(lean_object* v___x_245_, lean_object* v_str_246_, lean_object* v_a_247_, lean_object* v_b_248_){
_start:
{
lean_object* v_res_249_; 
v_res_249_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg(v___x_245_, v_str_246_, v_a_247_, v_b_248_);
lean_dec_ref(v_str_246_);
lean_dec(v___x_245_);
return v_res_249_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_longestBacktickRun(lean_object* v_str_252_){
_start:
{
lean_object* v_best_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v_fst_257_; 
v_best_253_ = lean_unsigned_to_nat(0u);
v___x_254_ = ((lean_object*)(l_Lean_Doc_longestBacktickRun___closed__0));
v___x_255_ = lean_string_utf8_byte_size(v_str_252_);
v___x_256_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg(v___x_255_, v_str_252_, v_best_253_, v___x_254_);
v_fst_257_ = lean_ctor_get(v___x_256_, 0);
lean_inc(v_fst_257_);
lean_dec_ref(v___x_256_);
return v_fst_257_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_longestBacktickRun___boxed(lean_object* v_str_258_){
_start:
{
lean_object* v_res_259_; 
v_res_259_ = l_Lean_Doc_longestBacktickRun(v_str_258_);
lean_dec_ref(v_str_258_);
return v_res_259_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0(lean_object* v___x_260_, lean_object* v___x_261_, lean_object* v_str_262_, lean_object* v_inst_263_, lean_object* v_R_264_, lean_object* v_a_265_, lean_object* v_b_266_, lean_object* v_c_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___redArg(v___x_261_, v_str_262_, v_a_265_, v_b_266_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0___boxed(lean_object* v___x_269_, lean_object* v___x_270_, lean_object* v_str_271_, lean_object* v_inst_272_, lean_object* v_R_273_, lean_object* v_a_274_, lean_object* v_b_275_, lean_object* v_c_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_WellFounded_opaqueFix_u2083___at___00Lean_Doc_longestBacktickRun_spec__0(v___x_269_, v___x_270_, v_str_271_, v_inst_272_, v_R_273_, v_a_274_, v_b_275_, v_c_276_);
lean_dec_ref(v_str_271_);
lean_dec(v___x_270_);
lean_dec_ref(v___x_269_);
return v_res_277_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(lean_object* v_s_278_, uint8_t v___x_279_, lean_object* v_a_280_, uint8_t v_b_281_){
_start:
{
lean_object* v_str_282_; lean_object* v_startInclusive_283_; lean_object* v_endExclusive_284_; lean_object* v___x_285_; uint8_t v_decide_286_; 
v_str_282_ = lean_ctor_get(v_s_278_, 0);
v_startInclusive_283_ = lean_ctor_get(v_s_278_, 1);
v_endExclusive_284_ = lean_ctor_get(v_s_278_, 2);
v___x_285_ = lean_nat_sub(v_endExclusive_284_, v_startInclusive_283_);
v_decide_286_ = lean_nat_dec_eq(v_a_280_, v___x_285_);
lean_dec(v___x_285_);
if (v_decide_286_ == 0)
{
lean_object* v___x_287_; uint32_t v___x_292_; uint32_t v___x_293_; uint8_t v___x_294_; 
v___x_287_ = lean_nat_add(v_startInclusive_283_, v_a_280_);
lean_dec(v_a_280_);
v___x_292_ = lean_string_utf8_get_fast(v_str_282_, v___x_287_);
v___x_293_ = 32;
v___x_294_ = lean_uint32_dec_eq(v___x_292_, v___x_293_);
if (v___x_294_ == 0)
{
if (v___x_279_ == 0)
{
goto v___jp_288_;
}
else
{
lean_dec(v___x_287_);
return v___x_279_;
}
}
else
{
goto v___jp_288_;
}
v___jp_288_:
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_string_utf8_next_fast(v_str_282_, v___x_287_);
lean_dec(v___x_287_);
v___x_290_ = lean_nat_sub(v___x_289_, v_startInclusive_283_);
v_a_280_ = v___x_290_;
v_b_281_ = v_decide_286_;
goto _start;
}
}
else
{
lean_dec(v_a_280_);
return v_b_281_;
}
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_278_ = stack[0].m_obj;
uint8_t v___x_279_ = stack[1].m_num;
lean_object* v_a_280_ = stack[2].m_obj;
uint8_t v_b_281_ = stack[3].m_num;
uint8_t v_res_295_;
v_res_295_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(v_s_278_, v___x_279_, v_a_280_, v_b_281_);
stack->m_num = v_res_295_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg___boxed(lean_object* v_s_296_, lean_object* v___x_297_, lean_object* v_a_298_, lean_object* v_b_299_){
_start:
{
uint8_t v___x_973__boxed_300_; uint8_t v_b_boxed_301_; uint8_t v_res_302_; lean_object* v_r_303_; 
v___x_973__boxed_300_ = lean_unbox(v___x_297_);
v_b_boxed_301_ = lean_unbox(v_b_299_);
v_res_302_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(v_s_296_, v___x_973__boxed_300_, v_a_298_, v_b_boxed_301_);
lean_dec_ref(v_s_296_);
v_r_303_ = lean_box(v_res_302_);
return v_r_303_;
}
}
uint8_t l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0(uint8_t v___x_304_, lean_object* v_s_305_){
_start:
{
lean_object* v_searcher_306_; uint8_t v___x_307_; uint8_t v___x_308_; 
v_searcher_306_ = lean_unsigned_to_nat(0u);
v___x_307_ = 0;
v___x_308_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(v_s_305_, v___x_304_, v_searcher_306_, v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT void l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_304_ = stack[0].m_num;
lean_object* v_s_305_ = stack[1].m_obj;
uint8_t v_res_309_;
v_res_309_ = l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0(v___x_304_, v_s_305_);
stack->m_num = v_res_309_;
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0___boxed(lean_object* v___x_310_, lean_object* v_s_311_){
_start:
{
uint8_t v___x_1008__boxed_312_; uint8_t v_res_313_; lean_object* v_r_314_; 
v___x_1008__boxed_312_ = lean_unbox(v___x_310_);
v_res_313_ = l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0(v___x_1008__boxed_312_, v_s_311_);
lean_dec_ref(v_s_311_);
v_r_314_ = lean_box(v_res_313_);
return v_r_314_;
}
}
uint8_t l_Lean_Doc_versoCodeBoundarySpaces(lean_object* v_str_316_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_317_ = lean_string_utf8_byte_size(v_str_316_);
v___x_318_ = lean_unsigned_to_nat(1u);
v___x_319_ = lean_nat_dec_le(v___x_318_, v___x_317_);
if (v___x_319_ == 0)
{
lean_dec_ref(v_str_316_);
return v___x_319_;
}
else
{
lean_object* v___x_320_; lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_320_ = ((lean_object*)(l_Lean_Doc_versoCodeBoundarySpaces___closed__0));
v___x_321_ = lean_unsigned_to_nat(0u);
v___x_322_ = lean_string_memcmp(v_str_316_, v___x_320_, v___x_321_, v___x_321_, v___x_318_);
if (v___x_322_ == 0)
{
lean_dec_ref(v_str_316_);
return v___x_322_;
}
else
{
if (v___x_319_ == 0)
{
lean_dec_ref(v_str_316_);
return v___x_319_;
}
else
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = lean_nat_sub(v___x_317_, v___x_318_);
v___x_324_ = lean_string_memcmp(v_str_316_, v___x_320_, v___x_323_, v___x_321_, v___x_318_);
lean_dec(v___x_323_);
if (v___x_324_ == 0)
{
lean_dec_ref(v_str_316_);
return v___x_324_;
}
else
{
lean_object* v___x_325_; uint8_t v___x_326_; 
v___x_325_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_325_, 0, v_str_316_);
lean_ctor_set(v___x_325_, 1, v___x_321_);
lean_ctor_set(v___x_325_, 2, v___x_317_);
v___x_326_ = l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0(v___x_324_, v___x_325_);
lean_dec_ref_known(v___x_325_, 3);
return v___x_326_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Doc_versoCodeBoundarySpaces_0interp(lean_interpreter_value* stack)
{
lean_object* v_str_316_ = stack[0].m_obj;
uint8_t v_res_327_;
v_res_327_ = l_Lean_Doc_versoCodeBoundarySpaces(v_str_316_);
stack->m_num = v_res_327_;
}
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeBoundarySpaces___boxed(lean_object* v_str_328_){
_start:
{
uint8_t v_res_329_; lean_object* v_r_330_; 
v_res_329_ = l_Lean_Doc_versoCodeBoundarySpaces(v_str_328_);
v_r_330_ = lean_box(v_res_329_);
return v_r_330_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0(lean_object* v_s_331_, uint8_t v___x_332_, lean_object* v_inst_333_, lean_object* v_R_334_, lean_object* v_a_335_, uint8_t v_b_336_, lean_object* v_c_337_){
_start:
{
uint8_t v___x_338_; 
v___x_338_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(v_s_331_, v___x_332_, v_a_335_, v_b_336_);
return v___x_338_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_331_ = stack[0].m_obj;
uint8_t v___x_332_ = stack[1].m_num;
lean_object* v_a_335_ = stack[4].m_obj;
uint8_t v_b_336_ = stack[5].m_num;
uint8_t v_res_339_;
v_res_339_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0(v_s_331_, v___x_332_, lean_box(0), lean_box(0), v_a_335_, v_b_336_, lean_box(0));
stack->m_num = v_res_339_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___boxed(lean_object* v_s_340_, lean_object* v___x_341_, lean_object* v_inst_342_, lean_object* v_R_343_, lean_object* v_a_344_, lean_object* v_b_345_, lean_object* v_c_346_){
_start:
{
uint8_t v___x_1053__boxed_347_; uint8_t v_b_boxed_348_; uint8_t v_res_349_; lean_object* v_r_350_; 
v___x_1053__boxed_347_ = lean_unbox(v___x_341_);
v_b_boxed_348_ = lean_unbox(v_b_345_);
v_res_349_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0(v_s_340_, v___x_1053__boxed_347_, v_inst_342_, v_R_343_, v_a_344_, v_b_boxed_348_, v_c_346_);
lean_dec_ref(v_s_340_);
v_r_350_ = lean_box(v_res_349_);
return v_r_350_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg(lean_object* v_str_351_, lean_object* v_a_352_){
_start:
{
lean_object* v_fst_353_; lean_object* v_snd_354_; lean_object* v___x_356_; uint8_t v_isShared_357_; uint8_t v_isSharedCheck_381_; 
v_fst_353_ = lean_ctor_get(v_a_352_, 0);
v_snd_354_ = lean_ctor_get(v_a_352_, 1);
v_isSharedCheck_381_ = !lean_is_exclusive(v_a_352_);
if (v_isSharedCheck_381_ == 0)
{
v___x_356_ = v_a_352_;
v_isShared_357_ = v_isSharedCheck_381_;
goto v_resetjp_355_;
}
else
{
lean_inc(v_snd_354_);
lean_inc(v_fst_353_);
lean_dec(v_a_352_);
v___x_356_ = lean_box(0);
v_isShared_357_ = v_isSharedCheck_381_;
goto v_resetjp_355_;
}
v_resetjp_355_:
{
lean_object* v___x_358_; uint8_t v_decide_359_; 
v___x_358_ = lean_string_utf8_byte_size(v_str_351_);
v_decide_359_ = lean_nat_dec_eq(v_snd_354_, v___x_358_);
if (v_decide_359_ == 0)
{
uint32_t v___x_360_; lean_object* v___x_361_; uint32_t v___x_367_; uint8_t v___x_368_; 
v___x_360_ = lean_string_utf8_get_fast(v_str_351_, v_snd_354_);
v___x_361_ = lean_string_utf8_next_fast(v_str_351_, v_snd_354_);
lean_dec(v_snd_354_);
v___x_367_ = 92;
v___x_368_ = lean_uint32_dec_eq(v___x_360_, v___x_367_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; 
lean_del_object(v___x_356_);
v___x_369_ = lean_string_push(v_fst_353_, v___x_360_);
v___x_370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
lean_ctor_set(v___x_370_, 1, v___x_361_);
v_a_352_ = v___x_370_;
goto _start;
}
else
{
uint8_t v_decide_372_; 
v_decide_372_ = lean_nat_dec_eq(v___x_361_, v___x_358_);
if (v_decide_372_ == 0)
{
if (v___x_368_ == 0)
{
goto v___jp_362_;
}
else
{
uint32_t v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; 
lean_del_object(v___x_356_);
v___x_373_ = lean_string_utf8_get_fast(v_str_351_, v___x_361_);
v___x_374_ = lean_string_push(v_fst_353_, v___x_373_);
v___x_375_ = lean_string_utf8_next_fast(v_str_351_, v___x_361_);
v___x_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_374_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v_a_352_ = v___x_376_;
goto _start;
}
}
else
{
goto v___jp_362_;
}
}
v___jp_362_:
{
lean_object* v___x_364_; 
if (v_isShared_357_ == 0)
{
lean_ctor_set(v___x_356_, 1, v___x_361_);
v___x_364_ = v___x_356_;
goto v_reusejp_363_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v_fst_353_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v___x_361_);
v___x_364_ = v_reuseFailAlloc_366_;
goto v_reusejp_363_;
}
v_reusejp_363_:
{
v_a_352_ = v___x_364_;
goto _start;
}
}
}
else
{
lean_object* v___x_379_; 
if (v_isShared_357_ == 0)
{
v___x_379_ = v___x_356_;
goto v_reusejp_378_;
}
else
{
lean_object* v_reuseFailAlloc_380_; 
v_reuseFailAlloc_380_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_380_, 0, v_fst_353_);
lean_ctor_set(v_reuseFailAlloc_380_, 1, v_snd_354_);
v___x_379_ = v_reuseFailAlloc_380_;
goto v_reusejp_378_;
}
v_reusejp_378_:
{
return v___x_379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg___boxed(lean_object* v_str_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg(v_str_382_, v_a_383_);
lean_dec_ref(v_str_382_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(lean_object* v_str_389_){
_start:
{
lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v_fst_392_; 
v___x_390_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__1));
v___x_391_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg(v_str_389_, v___x_390_);
v_fst_392_ = lean_ctor_get(v___x_391_, 0);
lean_inc(v_fst_392_);
lean_dec_ref(v___x_391_);
return v_fst_392_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___boxed(lean_object* v_str_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v_str_393_);
lean_dec_ref(v_str_393_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0(lean_object* v_str_395_, lean_object* v_inst_396_, lean_object* v_a_397_){
_start:
{
lean_object* v___x_398_; 
v___x_398_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg(v_str_395_, v_a_397_);
return v___x_398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___boxed(lean_object* v_str_399_, lean_object* v_inst_400_, lean_object* v_a_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0(v_str_399_, v_inst_400_, v_a_401_);
lean_dec_ref(v_str_399_);
return v_res_402_;
}
}
uint8_t l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0(uint32_t v_a_403_, lean_object* v_x_404_){
_start:
{
if (lean_obj_tag(v_x_404_) == 0)
{
uint8_t v___x_405_; 
v___x_405_ = 0;
return v___x_405_;
}
else
{
lean_object* v_head_406_; lean_object* v_tail_407_; uint32_t v___x_408_; uint8_t v___x_409_; 
v_head_406_ = lean_ctor_get(v_x_404_, 0);
v_tail_407_ = lean_ctor_get(v_x_404_, 1);
v___x_408_ = lean_unbox_uint32(v_head_406_);
v___x_409_ = lean_uint32_dec_eq(v_a_403_, v___x_408_);
if (v___x_409_ == 0)
{
v_x_404_ = v_tail_407_;
goto _start;
}
else
{
return v___x_409_;
}
}
}
}
LEAN_EXPORT void l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_a_403_ = stack[0].m_num;
lean_object* v_x_404_ = stack[1].m_obj;
uint8_t v_res_411_;
v_res_411_ = l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0(v_a_403_, v_x_404_);
stack->m_num = v_res_411_;
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0___boxed(lean_object* v_a_412_, lean_object* v_x_413_){
_start:
{
uint32_t v_a_boxed_414_; uint8_t v_res_415_; lean_object* v_r_416_; 
v_a_boxed_414_ = lean_unbox_uint32(v_a_412_);
lean_dec(v_a_412_);
v_res_415_ = l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0(v_a_boxed_414_, v_x_413_);
lean_dec(v_x_413_);
v_r_416_ = lean_box(v_res_415_);
return v_r_416_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg(lean_object* v_delimiters_417_, lean_object* v___x_418_, lean_object* v_value_419_, lean_object* v_a_420_, lean_object* v_b_421_){
_start:
{
uint8_t v_decide_422_; 
v_decide_422_ = lean_nat_dec_eq(v_a_420_, v___x_418_);
if (v_decide_422_ == 0)
{
uint32_t v___x_423_; lean_object* v___x_424_; uint32_t v___x_425_; uint8_t v___x_430_; 
v___x_423_ = lean_string_utf8_get_fast(v_value_419_, v_a_420_);
v___x_424_ = lean_string_utf8_next_fast(v_value_419_, v_a_420_);
lean_dec(v_a_420_);
v___x_425_ = 92;
v___x_430_ = lean_uint32_dec_eq(v___x_423_, v___x_425_);
if (v___x_430_ == 0)
{
uint8_t v___x_431_; 
v___x_431_ = l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0(v___x_423_, v_delimiters_417_);
if (v___x_431_ == 0)
{
lean_object* v___x_432_; 
v___x_432_ = lean_string_push(v_b_421_, v___x_423_);
v_a_420_ = v___x_424_;
v_b_421_ = v___x_432_;
goto _start;
}
else
{
goto v___jp_426_;
}
}
else
{
goto v___jp_426_;
}
v___jp_426_:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_string_push(v_b_421_, v___x_425_);
v___x_428_ = lean_string_push(v___x_427_, v___x_423_);
v_a_420_ = v___x_424_;
v_b_421_ = v___x_428_;
goto _start;
}
}
else
{
lean_dec(v_a_420_);
return v_b_421_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg___boxed(lean_object* v_delimiters_434_, lean_object* v___x_435_, lean_object* v_value_436_, lean_object* v_a_437_, lean_object* v_b_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg(v_delimiters_434_, v___x_435_, v_value_436_, v_a_437_, v_b_438_);
lean_dec_ref(v_value_436_);
lean_dec(v___x_435_);
lean_dec(v_delimiters_434_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited(lean_object* v_delimiters_440_, lean_object* v_value_441_){
_start:
{
lean_object* v___x_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_442_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_443_ = lean_string_utf8_byte_size(v_value_441_);
v___x_444_ = lean_unsigned_to_nat(0u);
v___x_445_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg(v_delimiters_440_, v___x_443_, v_value_441_, v___x_444_, v___x_442_);
return v___x_445_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited___boxed(lean_object* v_delimiters_446_, lean_object* v_value_447_){
_start:
{
lean_object* v_res_448_; 
v_res_448_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited(v_delimiters_446_, v_value_447_);
lean_dec_ref(v_value_447_);
lean_dec(v_delimiters_446_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1(lean_object* v_delimiters_449_, lean_object* v___x_450_, lean_object* v___x_451_, lean_object* v_value_452_, lean_object* v_inst_453_, lean_object* v_R_454_, lean_object* v_a_455_, lean_object* v_b_456_, lean_object* v_c_457_){
_start:
{
lean_object* v___x_458_; 
v___x_458_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg(v_delimiters_449_, v___x_451_, v_value_452_, v_a_455_, v_b_456_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___boxed(lean_object* v_delimiters_459_, lean_object* v___x_460_, lean_object* v___x_461_, lean_object* v_value_462_, lean_object* v_inst_463_, lean_object* v_R_464_, lean_object* v_a_465_, lean_object* v_b_466_, lean_object* v_c_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1(v_delimiters_459_, v___x_460_, v___x_461_, v_value_462_, v_inst_463_, v_R_464_, v_a_465_, v_b_466_, v_c_467_);
lean_dec_ref(v_value_462_);
lean_dec(v___x_461_);
lean_dec_ref(v___x_460_);
lean_dec(v_delimiters_459_);
return v_res_468_;
}
}
static lean_object* _init_l_Lean_Doc_escapeVersoLinkUrl___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_469_; lean_object* v___x_470_; 
v___x_469_ = 41;
v___x_470_ = lean_box_uint32(v___x_469_);
return v___x_470_;
}
}
static lean_object* _init_l_Lean_Doc_escapeVersoLinkUrl___closed__0(void){
_start:
{
lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_471_ = lean_box(0);
v___x_472_ = l_Lean_Doc_escapeVersoLinkUrl___closed__0___boxed__const__1;
v___x_473_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
lean_ctor_set(v___x_473_, 1, v___x_471_);
return v___x_473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoLinkUrl(lean_object* v_value_474_){
_start:
{
lean_object* v___x_475_; lean_object* v___x_476_; 
v___x_475_ = lean_obj_once(&l_Lean_Doc_escapeVersoLinkUrl___closed__0, &l_Lean_Doc_escapeVersoLinkUrl___closed__0_once, _init_l_Lean_Doc_escapeVersoLinkUrl___closed__0);
v___x_476_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited(v___x_475_, v_value_474_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoLinkUrl___boxed(lean_object* v_value_477_){
_start:
{
lean_object* v_res_478_; 
v_res_478_ = l_Lean_Doc_escapeVersoLinkUrl(v_value_477_);
lean_dec_ref(v_value_477_);
return v_res_478_;
}
}
static lean_object* _init_l_Lean_Doc_escapeVersoImageAlt___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_479_; lean_object* v___x_480_; 
v___x_479_ = 93;
v___x_480_ = lean_box_uint32(v___x_479_);
return v___x_480_;
}
}
static lean_object* _init_l_Lean_Doc_escapeVersoImageAlt___closed__0(void){
_start:
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_481_ = lean_box(0);
v___x_482_ = l_Lean_Doc_escapeVersoImageAlt___closed__0___boxed__const__1;
v___x_483_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_483_, 0, v___x_482_);
lean_ctor_set(v___x_483_, 1, v___x_481_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoImageAlt(lean_object* v_value_484_){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; 
v___x_485_ = lean_obj_once(&l_Lean_Doc_escapeVersoImageAlt___closed__0, &l_Lean_Doc_escapeVersoImageAlt___closed__0_once, _init_l_Lean_Doc_escapeVersoImageAlt___closed__0);
v___x_486_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited(v___x_485_, v_value_484_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoImageAlt___boxed(lean_object* v_value_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Lean_Doc_escapeVersoImageAlt(v_value_487_);
lean_dec_ref(v_value_487_);
return v_res_488_;
}
}
static lean_object* _init_l_Lean_TSyntax_getVersoText___closed__0(void){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_490_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoText(lean_object* v_s_491_){
_start:
{
lean_object* v___x_492_; lean_object* v___x_493_; 
v___x_492_ = ((lean_object*)(l_Lean_Doc_versoTextKind));
v___x_493_ = l_Lean_Syntax_isLit_x3f(v___x_492_, v_s_491_);
if (lean_obj_tag(v___x_493_) == 0)
{
lean_object* v___x_494_; 
v___x_494_ = lean_obj_once(&l_Lean_TSyntax_getVersoText___closed__0, &l_Lean_TSyntax_getVersoText___closed__0_once, _init_l_Lean_TSyntax_getVersoText___closed__0);
return v___x_494_;
}
else
{
lean_object* v_val_495_; lean_object* v___x_496_; 
v_val_495_ = lean_ctor_get(v___x_493_, 0);
lean_inc(v_val_495_);
lean_dec_ref_known(v___x_493_, 1);
v___x_496_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v_val_495_);
lean_dec(v_val_495_);
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoText___boxed(lean_object* v_s_497_){
_start:
{
lean_object* v_res_498_; 
v_res_498_ = l_Lean_TSyntax_getVersoText(v_s_497_);
lean_dec(v_s_497_);
return v_res_498_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoTextSource(lean_object* v_s_499_){
_start:
{
lean_object* v___x_500_; lean_object* v___x_501_; 
v___x_500_ = ((lean_object*)(l_Lean_Doc_versoTextKind));
v___x_501_ = l_Lean_Syntax_isLit_x3f(v___x_500_, v_s_499_);
if (lean_obj_tag(v___x_501_) == 0)
{
lean_object* v___x_502_; 
v___x_502_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
return v___x_502_;
}
else
{
lean_object* v_val_503_; 
v_val_503_ = lean_ctor_get(v___x_501_, 0);
lean_inc(v_val_503_);
lean_dec_ref_known(v___x_501_, 1);
return v_val_503_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoTextSource___boxed(lean_object* v_s_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Lean_TSyntax_getVersoTextSource(v_s_504_);
lean_dec(v_s_504_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoRefName(lean_object* v_s_506_){
_start:
{
lean_object* v___x_507_; lean_object* v___x_508_; 
v___x_507_ = ((lean_object*)(l_Lean_Doc_versoRefKind));
v___x_508_ = l_Lean_Syntax_isLit_x3f(v___x_507_, v_s_506_);
if (lean_obj_tag(v___x_508_) == 0)
{
lean_object* v___x_509_; 
v___x_509_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
return v___x_509_;
}
else
{
lean_object* v_val_510_; 
v_val_510_ = lean_ctor_get(v___x_508_, 0);
lean_inc(v_val_510_);
lean_dec_ref_known(v___x_508_, 1);
return v_val_510_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoRefName___boxed(lean_object* v_s_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Lean_TSyntax_getVersoRefName(v_s_511_);
lean_dec(v_s_511_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkUrl(lean_object* v_s_513_){
_start:
{
lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_514_ = ((lean_object*)(l_Lean_Doc_versoLinkUrlKind));
v___x_515_ = l_Lean_Syntax_isLit_x3f(v___x_514_, v_s_513_);
if (lean_obj_tag(v___x_515_) == 0)
{
lean_object* v___x_516_; 
v___x_516_ = lean_obj_once(&l_Lean_TSyntax_getVersoText___closed__0, &l_Lean_TSyntax_getVersoText___closed__0_once, _init_l_Lean_TSyntax_getVersoText___closed__0);
return v___x_516_;
}
else
{
lean_object* v_val_517_; lean_object* v___x_518_; 
v_val_517_ = lean_ctor_get(v___x_515_, 0);
lean_inc(v_val_517_);
lean_dec_ref_known(v___x_515_, 1);
v___x_518_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v_val_517_);
lean_dec(v_val_517_);
return v___x_518_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkUrl___boxed(lean_object* v_s_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_TSyntax_getVersoLinkUrl(v_s_519_);
lean_dec(v_s_519_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkRefUrl(lean_object* v_s_521_){
_start:
{
lean_object* v___x_522_; lean_object* v___x_523_; 
v___x_522_ = ((lean_object*)(l_Lean_Doc_versoLinkRefUrlKind));
v___x_523_ = l_Lean_Syntax_isLit_x3f(v___x_522_, v_s_521_);
if (lean_obj_tag(v___x_523_) == 0)
{
lean_object* v___x_524_; 
v___x_524_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
return v___x_524_;
}
else
{
lean_object* v_val_525_; 
v_val_525_ = lean_ctor_get(v___x_523_, 0);
lean_inc(v_val_525_);
lean_dec_ref_known(v___x_523_, 1);
return v_val_525_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkRefUrl___boxed(lean_object* v_s_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Lean_TSyntax_getVersoLinkRefUrl(v_s_526_);
lean_dec(v_s_526_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoImageAlt(lean_object* v_s_528_){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = ((lean_object*)(l_Lean_Doc_versoImageAltKind));
v___x_530_ = l_Lean_Syntax_isLit_x3f(v___x_529_, v_s_528_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_object* v___x_531_; 
v___x_531_ = lean_obj_once(&l_Lean_TSyntax_getVersoText___closed__0, &l_Lean_TSyntax_getVersoText___closed__0_once, _init_l_Lean_TSyntax_getVersoText___closed__0);
return v___x_531_;
}
else
{
lean_object* v_val_532_; lean_object* v___x_533_; 
v_val_532_ = lean_ctor_get(v___x_530_, 0);
lean_inc(v_val_532_);
lean_dec_ref_known(v___x_530_, 1);
v___x_533_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v_val_532_);
lean_dec(v_val_532_);
return v___x_533_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoImageAlt___boxed(lean_object* v_s_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Lean_TSyntax_getVersoImageAlt(v_s_534_);
lean_dec(v_s_534_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLine(lean_object* v_s_536_){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = ((lean_object*)(l_Lean_Doc_versoCodeLineKind));
v___x_538_ = l_Lean_Syntax_isLit_x3f(v___x_537_, v_s_536_);
if (lean_obj_tag(v___x_538_) == 0)
{
lean_object* v___x_539_; 
v___x_539_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
return v___x_539_;
}
else
{
lean_object* v_val_540_; 
v_val_540_ = lean_ctor_get(v___x_538_, 0);
lean_inc(v_val_540_);
lean_dec_ref_known(v___x_538_, 1);
return v_val_540_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLine___boxed(lean_object* v_s_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_TSyntax_getVersoCodeLine(v_s_541_);
lean_dec(v_s_541_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLines(lean_object* v_s_543_){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_544_ = lean_unsigned_to_nat(0u);
v___x_545_ = l_Lean_Syntax_getArg(v_s_543_, v___x_544_);
v___x_546_ = l_Lean_Syntax_getArgs(v___x_545_);
lean_dec(v___x_545_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLines___boxed(lean_object* v_s_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l_Lean_TSyntax_getVersoCodeLines(v_s_547_);
lean_dec(v_s_547_);
return v_res_548_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0(lean_object* v_as_549_, size_t v_sz_550_, size_t v_i_551_, lean_object* v_b_552_){
_start:
{
uint8_t v___x_553_; 
v___x_553_ = lean_usize_dec_lt(v_i_551_, v_sz_550_);
if (v___x_553_ == 0)
{
return v_b_552_;
}
else
{
lean_object* v_a_554_; lean_object* v___x_555_; lean_object* v___x_556_; size_t v___x_557_; size_t v___x_558_; 
v_a_554_ = lean_array_uget_borrowed(v_as_549_, v_i_551_);
v___x_555_ = l_Lean_TSyntax_getVersoCodeLine(v_a_554_);
v___x_556_ = lean_string_append(v_b_552_, v___x_555_);
lean_dec_ref(v___x_555_);
v___x_557_ = ((size_t)1ULL);
v___x_558_ = lean_usize_add(v_i_551_, v___x_557_);
v_i_551_ = v___x_558_;
v_b_552_ = v___x_556_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_549_ = stack[0].m_obj;
size_t v_sz_550_ = stack[1].m_num;
size_t v_i_551_ = stack[2].m_num;
lean_object* v_b_552_ = stack[3].m_obj;
lean_object* v_res_560_;
v_res_560_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0(v_as_549_, v_sz_550_, v_i_551_, v_b_552_);
stack->m_obj
 = v_res_560_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0___boxed(lean_object* v_as_561_, lean_object* v_sz_562_, lean_object* v_i_563_, lean_object* v_b_564_){
_start:
{
size_t v_sz_boxed_565_; size_t v_i_boxed_566_; lean_object* v_res_567_; 
v_sz_boxed_565_ = lean_unbox_usize(v_sz_562_);
lean_dec(v_sz_562_);
v_i_boxed_566_ = lean_unbox_usize(v_i_563_);
lean_dec(v_i_563_);
v_res_567_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0(v_as_561_, v_sz_boxed_565_, v_i_boxed_566_, v_b_564_);
lean_dec_ref(v_as_561_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCode(lean_object* v_s_568_){
_start:
{
lean_object* v_str_569_; lean_object* v___x_570_; size_t v_sz_571_; size_t v___x_572_; lean_object* v___x_573_; 
v_str_569_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_570_ = l_Lean_TSyntax_getVersoCodeLines(v_s_568_);
v_sz_571_ = lean_array_size(v___x_570_);
v___x_572_ = ((size_t)0ULL);
v___x_573_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0(v___x_570_, v_sz_571_, v___x_572_, v_str_569_);
lean_dec_ref(v___x_570_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCode___boxed(lean_object* v_s_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lean_TSyntax_getVersoCode(v_s_574_);
lean_dec(v_s_574_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlockLines(lean_object* v_s_576_){
_start:
{
lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; 
v___x_577_ = lean_unsigned_to_nat(0u);
v___x_578_ = l_Lean_Syntax_getArg(v_s_576_, v___x_577_);
v___x_579_ = l_Lean_Syntax_getArgs(v___x_578_);
lean_dec(v___x_578_);
return v___x_579_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlockLines___boxed(lean_object* v_s_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l_Lean_TSyntax_getVersoCodeBlockLines(v_s_580_);
lean_dec(v_s_580_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlock(lean_object* v_s_582_){
_start:
{
lean_object* v_out_583_; lean_object* v___x_584_; size_t v_sz_585_; size_t v___x_586_; lean_object* v___x_587_; 
v_out_583_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_584_ = l_Lean_TSyntax_getVersoCodeBlockLines(v_s_582_);
v_sz_585_ = lean_array_size(v___x_584_);
v___x_586_ = ((size_t)0ULL);
v___x_587_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0(v___x_584_, v_sz_585_, v___x_586_, v_out_583_);
lean_dec_ref(v___x_584_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlock___boxed(lean_object* v_s_588_){
_start:
{
lean_object* v_res_589_; 
v_res_589_ = l_Lean_TSyntax_getVersoCodeBlock(v_s_588_);
lean_dec(v_s_588_);
return v_res_589_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoText_view(lean_object* v_s_590_){
_start:
{
lean_object* v___x_591_; 
v___x_591_ = l_Lean_TSyntax_getVersoText(v_s_590_);
return v___x_591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoText_view___boxed(lean_object* v_s_592_){
_start:
{
lean_object* v_res_593_; 
v_res_593_ = l_Lean_Doc_VersoText_view(v_s_592_);
lean_dec(v_s_592_);
return v_res_593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoRefName_view(lean_object* v_s_594_){
_start:
{
lean_object* v___x_595_; 
v___x_595_ = l_Lean_TSyntax_getVersoRefName(v_s_594_);
return v___x_595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoRefName_view___boxed(lean_object* v_s_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l_Lean_Doc_VersoRefName_view(v_s_596_);
lean_dec(v_s_596_);
return v_res_597_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoLinkUrl_view(lean_object* v_s_598_){
_start:
{
lean_object* v___x_599_; 
v___x_599_ = l_Lean_TSyntax_getVersoLinkUrl(v_s_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoLinkUrl_view___boxed(lean_object* v_s_600_){
_start:
{
lean_object* v_res_601_; 
v_res_601_ = l_Lean_Doc_VersoLinkUrl_view(v_s_600_);
lean_dec(v_s_600_);
return v_res_601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoLinkRefUrl_view(lean_object* v_s_602_){
_start:
{
lean_object* v___x_603_; 
v___x_603_ = l_Lean_TSyntax_getVersoLinkRefUrl(v_s_602_);
return v___x_603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoLinkRefUrl_view___boxed(lean_object* v_s_604_){
_start:
{
lean_object* v_res_605_; 
v_res_605_ = l_Lean_Doc_VersoLinkRefUrl_view(v_s_604_);
lean_dec(v_s_604_);
return v_res_605_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoImageAlt_view(lean_object* v_s_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = l_Lean_TSyntax_getVersoImageAlt(v_s_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoImageAlt_view___boxed(lean_object* v_s_608_){
_start:
{
lean_object* v_res_609_; 
v_res_609_ = l_Lean_Doc_VersoImageAlt_view(v_s_608_);
lean_dec(v_s_608_);
return v_res_609_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCodeLine_view(lean_object* v_s_610_){
_start:
{
lean_object* v___x_611_; 
v___x_611_ = l_Lean_TSyntax_getVersoCodeLine(v_s_610_);
return v___x_611_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCodeLine_view___boxed(lean_object* v_s_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Lean_Doc_VersoCodeLine_view(v_s_612_);
lean_dec(v_s_612_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCode_view(lean_object* v_s_614_){
_start:
{
lean_object* v___x_615_; 
v___x_615_ = l_Lean_TSyntax_getVersoCode(v_s_614_);
return v___x_615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCode_view___boxed(lean_object* v_s_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Lean_Doc_VersoCode_view(v_s_616_);
lean_dec(v_s_616_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCodeBlock_view(lean_object* v_s_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_Lean_TSyntax_getVersoCodeBlock(v_s_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCodeBlock_view___boxed(lean_object* v_s_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Lean_Doc_VersoCodeBlock_view(v_s_620_);
lean_dec(v_s_620_);
return v_res_621_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__4(void){
_start:
{
uint8_t v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_631_ = 0;
v___x_632_ = l_Lean_Parser_strLit;
v___x_633_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__3));
v___x_634_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__0));
v___x_635_ = l_Lean_Parser_nodeWithAntiquot(v___x_634_, v___x_633_, v___x_632_, v___x_631_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_ArgVal_str___lam__0(lean_object* v_c_636_, lean_object* v_s_637_){
_start:
{
lean_object* v___x_638_; lean_object* v_fn_639_; lean_object* v___x_640_; 
v___x_638_ = lean_obj_once(&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__4, &l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__4);
v_fn_639_ = lean_ctor_get(v___x_638_, 1);
lean_inc_ref(v_fn_639_);
v___x_640_ = lean_apply_2(v_fn_639_, v_c_636_, v_s_637_);
return v___x_640_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__3(void){
_start:
{
uint8_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; 
v___x_654_ = 0;
v___x_655_ = l_Lean_Parser_ident;
v___x_656_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__2));
v___x_657_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__0));
v___x_658_ = l_Lean_Parser_nodeWithAntiquot(v___x_657_, v___x_656_, v___x_655_, v___x_654_);
return v___x_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_ArgVal_ident___lam__0(lean_object* v_c_659_, lean_object* v_s_660_){
_start:
{
lean_object* v___x_661_; lean_object* v_fn_662_; lean_object* v___x_663_; 
v___x_661_ = lean_obj_once(&l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__3, &l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__3);
v_fn_662_ = lean_ctor_get(v___x_661_, 1);
lean_inc_ref(v_fn_662_);
v___x_663_ = lean_apply_2(v_fn_662_, v_c_659_, v_s_660_);
return v___x_663_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__3(void){
_start:
{
uint8_t v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; 
v___x_677_ = 0;
v___x_678_ = l_Lean_Parser_numLit;
v___x_679_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__2));
v___x_680_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__0));
v___x_681_ = l_Lean_Parser_nodeWithAntiquot(v___x_680_, v___x_679_, v___x_678_, v___x_677_);
return v___x_681_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_ArgVal_num___lam__0(lean_object* v_c_682_, lean_object* v_s_683_){
_start:
{
lean_object* v___x_684_; lean_object* v_fn_685_; lean_object* v___x_686_; 
v___x_684_ = lean_obj_once(&l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__3, &l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__3);
v_fn_685_ = lean_ctor_get(v___x_684_, 1);
lean_inc_ref(v_fn_685_);
v___x_686_ = lean_apply_2(v_fn_685_, v_c_682_, v_s_683_);
return v___x_686_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_argVal___lam__0___closed__2(void){
_start:
{
uint8_t v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_698_ = 1;
v___x_699_ = ((lean_object*)(l_Lean_Doc_Parser_argVal___lam__0___closed__1));
v___x_700_ = ((lean_object*)(l_Lean_Doc_Parser_argVal___lam__0___closed__0));
v___x_701_ = l_Lean_Parser_mkAntiquot(v___x_700_, v___x_699_, v___x_698_, v___x_698_);
return v___x_701_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_argVal___lam__0___closed__3(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_702_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_num));
v___x_703_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_ident));
v___x_704_ = l_Lean_Parser_orelse(v___x_703_, v___x_702_);
return v___x_704_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_argVal___lam__0___closed__4(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = lean_obj_once(&l_Lean_Doc_Parser_argVal___lam__0___closed__3, &l_Lean_Doc_Parser_argVal___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_argVal___lam__0___closed__3);
v___x_706_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_str));
v___x_707_ = l_Lean_Parser_orelse(v___x_706_, v___x_705_);
return v___x_707_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_argVal___lam__0___closed__5(void){
_start:
{
lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; 
v___x_708_ = lean_obj_once(&l_Lean_Doc_Parser_argVal___lam__0___closed__4, &l_Lean_Doc_Parser_argVal___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_argVal___lam__0___closed__4);
v___x_709_ = lean_obj_once(&l_Lean_Doc_Parser_argVal___lam__0___closed__2, &l_Lean_Doc_Parser_argVal___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_argVal___lam__0___closed__2);
v___x_710_ = l_Lean_Parser_withAntiquot(v___x_709_, v___x_708_);
return v___x_710_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_argVal___lam__0(lean_object* v_c_711_, lean_object* v_s_712_){
_start:
{
lean_object* v___x_713_; lean_object* v_fn_714_; lean_object* v___x_715_; 
v___x_713_ = lean_obj_once(&l_Lean_Doc_Parser_argVal___lam__0___closed__5, &l_Lean_Doc_Parser_argVal___lam__0___closed__5_once, _init_l_Lean_Doc_Parser_argVal___lam__0___closed__5);
v_fn_714_ = lean_ctor_get(v___x_713_, 1);
lean_inc_ref(v_fn_714_);
v___x_715_ = lean_apply_2(v_fn_714_, v_c_711_, v_s_712_);
return v___x_715_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_anon___lam__0___closed__3(void){
_start:
{
uint8_t v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_729_ = 0;
v___x_730_ = ((lean_object*)(l_Lean_Doc_Parser_argVal));
v___x_731_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_anon___lam__0___closed__2));
v___x_732_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_anon___lam__0___closed__0));
v___x_733_ = l_Lean_Parser_nodeWithAntiquot(v___x_732_, v___x_731_, v___x_730_, v___x_729_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_anon___lam__0(lean_object* v_c_734_, lean_object* v_s_735_){
_start:
{
lean_object* v___x_736_; lean_object* v_fn_737_; lean_object* v___x_738_; 
v___x_736_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__3, &l_Lean_Doc_Parser_Arg_anon___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_Arg_anon___lam__0___closed__3);
v_fn_737_ = lean_ctor_get(v___x_736_, 1);
lean_inc_ref(v_fn_737_);
v___x_738_ = lean_apply_2(v_fn_737_, v_c_734_, v_s_735_);
return v___x_738_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1(){
_start:
{
lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; 
v___x_746_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_anon___lam__0___closed__2));
v___x_747_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1___closed__0));
v___x_748_ = l_Lean_addBuiltinDocString(v___x_746_, v___x_747_);
return v___x_748_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_749_;
v_res_749_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1();
stack->m_obj
 = v_res_749_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1___boxed(lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1();
return v_res_751_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__3(void){
_start:
{
lean_object* v___x_760_; lean_object* v___x_761_; 
v___x_760_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named___lam__0___closed__2));
v___x_761_ = l_Lean_Parser_symbol(v___x_760_);
return v___x_761_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__5(void){
_start:
{
lean_object* v___x_763_; lean_object* v___x_764_; 
v___x_763_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named___lam__0___closed__4));
v___x_764_ = l_Lean_Parser_symbol(v___x_763_);
return v___x_764_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__7(void){
_start:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named___lam__0___closed__6));
v___x_767_ = l_Lean_Parser_symbol(v___x_766_);
return v___x_767_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__8(void){
_start:
{
lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; 
v___x_768_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__7, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__7_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__7);
v___x_769_ = ((lean_object*)(l_Lean_Doc_Parser_argVal));
v___x_770_ = l_Lean_Parser_andthen(v___x_769_, v___x_768_);
return v___x_770_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__9(void){
_start:
{
lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; 
v___x_771_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__8, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__8_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__8);
v___x_772_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__5, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__5_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__5);
v___x_773_ = l_Lean_Parser_andthen(v___x_772_, v___x_771_);
return v___x_773_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__10(void){
_start:
{
lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_774_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__9, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__9_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__9);
v___x_775_ = l_Lean_Parser_ident;
v___x_776_ = l_Lean_Parser_andthen(v___x_775_, v___x_774_);
return v___x_776_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__11(void){
_start:
{
lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; 
v___x_777_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__10, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__10_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__10);
v___x_778_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__3, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__3);
v___x_779_ = l_Lean_Parser_andthen(v___x_778_, v___x_777_);
return v___x_779_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__12(void){
_start:
{
uint8_t v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; 
v___x_780_ = 0;
v___x_781_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__11, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__11_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__11);
v___x_782_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named___lam__0___closed__1));
v___x_783_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named___lam__0___closed__0));
v___x_784_ = l_Lean_Parser_nodeWithAntiquot(v___x_783_, v___x_782_, v___x_781_, v___x_780_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_named___lam__0(lean_object* v_c_785_, lean_object* v_s_786_){
_start:
{
lean_object* v___x_787_; lean_object* v_fn_788_; lean_object* v___x_789_; 
v___x_787_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__12, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__12_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__12);
v_fn_788_ = lean_ctor_get(v___x_787_, 1);
lean_inc_ref(v_fn_788_);
v___x_789_ = lean_apply_2(v_fn_788_, v_c_785_, v_s_786_);
return v___x_789_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1(){
_start:
{
lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; 
v___x_797_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named___lam__0___closed__1));
v___x_798_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1___closed__0));
v___x_799_ = l_Lean_addBuiltinDocString(v___x_797_, v___x_798_);
return v___x_799_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_800_;
v_res_800_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1();
stack->m_obj
 = v_res_800_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1___boxed(lean_object* v_a_801_){
_start:
{
lean_object* v_res_802_; 
v_res_802_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1();
return v_res_802_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__2(void){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_810_ = ((lean_object*)(l_Lean_Doc_Parser_argVal));
v___x_811_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__5, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__5_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__5);
v___x_812_ = l_Lean_Parser_andthen(v___x_811_, v___x_810_);
return v___x_812_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__3(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_813_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__2, &l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__2);
v___x_814_ = l_Lean_Parser_ident;
v___x_815_ = l_Lean_Parser_andthen(v___x_814_, v___x_813_);
return v___x_815_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__4(void){
_start:
{
uint8_t v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_816_ = 0;
v___x_817_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__3, &l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__3);
v___x_818_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__1));
v___x_819_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__0));
v___x_820_ = l_Lean_Parser_nodeWithAntiquot(v___x_819_, v___x_818_, v___x_817_, v___x_816_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_named__no__paren___lam__0(lean_object* v_c_821_, lean_object* v_s_822_){
_start:
{
lean_object* v___x_823_; lean_object* v_fn_824_; lean_object* v___x_825_; 
v___x_823_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__4, &l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__4);
v_fn_824_ = lean_ctor_get(v___x_823_, 1);
lean_inc_ref(v_fn_824_);
v___x_825_ = lean_apply_2(v_fn_824_, v_c_821_, v_s_822_);
return v___x_825_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1(){
_start:
{
lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_832_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__1));
v___x_833_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1___closed__0));
v___x_834_ = l_Lean_addBuiltinDocString(v___x_832_, v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_835_;
v_res_835_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1();
stack->m_obj
 = v_res_835_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1___boxed(lean_object* v_a_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1();
return v_res_837_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__3(void){
_start:
{
lean_object* v___x_846_; lean_object* v___x_847_; 
v___x_846_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__2));
v___x_847_ = l_Lean_Parser_symbol(v___x_846_);
return v___x_847_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__4(void){
_start:
{
lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; 
v___x_848_ = l_Lean_Parser_ident;
v___x_849_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__3, &l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__3);
v___x_850_ = l_Lean_Parser_andthen(v___x_849_, v___x_848_);
return v___x_850_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__5(void){
_start:
{
uint8_t v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_851_ = 0;
v___x_852_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__4, &l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__4);
v___x_853_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__1));
v___x_854_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__0));
v___x_855_ = l_Lean_Parser_nodeWithAntiquot(v___x_854_, v___x_853_, v___x_852_, v___x_851_);
return v___x_855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_flag__on___lam__0(lean_object* v_c_856_, lean_object* v_s_857_){
_start:
{
lean_object* v___x_858_; lean_object* v_fn_859_; lean_object* v___x_860_; 
v___x_858_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__5, &l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__5_once, _init_l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__5);
v_fn_859_ = lean_ctor_get(v___x_858_, 1);
lean_inc_ref(v_fn_859_);
v___x_860_ = lean_apply_2(v_fn_859_, v_c_856_, v_s_857_);
return v___x_860_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1(){
_start:
{
lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; 
v___x_868_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__1));
v___x_869_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1___closed__0));
v___x_870_ = l_Lean_addBuiltinDocString(v___x_868_, v___x_869_);
return v___x_870_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_871_;
v_res_871_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1();
stack->m_obj
 = v_res_871_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1___boxed(lean_object* v_a_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1();
return v_res_873_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__3(void){
_start:
{
lean_object* v___x_882_; lean_object* v___x_883_; 
v___x_882_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__2));
v___x_883_ = l_Lean_Parser_symbol(v___x_882_);
return v___x_883_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__4(void){
_start:
{
lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_884_ = l_Lean_Parser_ident;
v___x_885_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__3, &l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__3);
v___x_886_ = l_Lean_Parser_andthen(v___x_885_, v___x_884_);
return v___x_886_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__5(void){
_start:
{
uint8_t v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_887_ = 0;
v___x_888_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__4, &l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__4);
v___x_889_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__1));
v___x_890_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__0));
v___x_891_ = l_Lean_Parser_nodeWithAntiquot(v___x_890_, v___x_889_, v___x_888_, v___x_887_);
return v___x_891_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_flag__off___lam__0(lean_object* v_c_892_, lean_object* v_s_893_){
_start:
{
lean_object* v___x_894_; lean_object* v_fn_895_; lean_object* v___x_896_; 
v___x_894_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__5, &l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__5_once, _init_l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__5);
v_fn_895_ = lean_ctor_get(v___x_894_, 1);
lean_inc_ref(v_fn_895_);
v___x_896_ = lean_apply_2(v_fn_895_, v_c_892_, v_s_893_);
return v___x_896_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1(){
_start:
{
lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; 
v___x_904_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__1));
v___x_905_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1___closed__0));
v___x_906_ = l_Lean_addBuiltinDocString(v___x_904_, v___x_905_);
return v___x_906_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_907_;
v_res_907_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1();
stack->m_obj
 = v_res_907_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1___boxed(lean_object* v_a_908_){
_start:
{
lean_object* v_res_909_; 
v_res_909_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1();
return v_res_909_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___lam__0___closed__2(void){
_start:
{
uint8_t v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_916_ = 1;
v___x_917_ = ((lean_object*)(l_Lean_Doc_Parser_arg___lam__0___closed__1));
v___x_918_ = ((lean_object*)(l_Lean_Doc_Parser_arg___lam__0___closed__0));
v___x_919_ = l_Lean_Parser_mkAntiquot(v___x_918_, v___x_917_, v___x_916_, v___x_916_);
return v___x_919_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; 
v___x_920_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named__no__paren));
v___x_921_ = l_Lean_Parser_atomic(v___x_920_);
return v___x_921_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; 
v___x_922_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_anon));
v___x_923_ = lean_obj_once(&l_Lean_Doc_Parser_arg___lam__0___closed__3, &l_Lean_Doc_Parser_arg___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_arg___lam__0___closed__3);
v___x_924_ = l_Lean_Parser_orelse(v___x_923_, v___x_922_);
return v___x_924_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; 
v___x_925_ = lean_obj_once(&l_Lean_Doc_Parser_arg___lam__0___closed__4, &l_Lean_Doc_Parser_arg___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_arg___lam__0___closed__4);
v___x_926_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__off));
v___x_927_ = l_Lean_Parser_orelse(v___x_926_, v___x_925_);
return v___x_927_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = lean_obj_once(&l_Lean_Doc_Parser_arg___lam__0___closed__5, &l_Lean_Doc_Parser_arg___lam__0___closed__5_once, _init_l_Lean_Doc_Parser_arg___lam__0___closed__5);
v___x_929_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__on));
v___x_930_ = l_Lean_Parser_orelse(v___x_929_, v___x_928_);
return v___x_930_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; 
v___x_931_ = lean_obj_once(&l_Lean_Doc_Parser_arg___lam__0___closed__6, &l_Lean_Doc_Parser_arg___lam__0___closed__6_once, _init_l_Lean_Doc_Parser_arg___lam__0___closed__6);
v___x_932_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named));
v___x_933_ = l_Lean_Parser_orelse(v___x_932_, v___x_931_);
return v___x_933_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; 
v___x_934_ = lean_obj_once(&l_Lean_Doc_Parser_arg___lam__0___closed__7, &l_Lean_Doc_Parser_arg___lam__0___closed__7_once, _init_l_Lean_Doc_Parser_arg___lam__0___closed__7);
v___x_935_ = lean_obj_once(&l_Lean_Doc_Parser_arg___lam__0___closed__2, &l_Lean_Doc_Parser_arg___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_arg___lam__0___closed__2);
v___x_936_ = l_Lean_Parser_withAntiquot(v___x_935_, v___x_934_);
return v___x_936_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_arg___lam__0(lean_object* v_c_937_, lean_object* v_s_938_){
_start:
{
lean_object* v___x_939_; lean_object* v_fn_940_; lean_object* v___x_941_; 
v___x_939_ = lean_obj_once(&l_Lean_Doc_Parser_arg___lam__0___closed__8, &l_Lean_Doc_Parser_arg___lam__0___closed__8_once, _init_l_Lean_Doc_Parser_arg___lam__0___closed__8);
v_fn_940_ = lean_ctor_get(v___x_939_, 1);
lean_inc_ref(v_fn_940_);
v___x_941_ = lean_apply_2(v_fn_940_, v_c_937_, v_s_938_);
return v___x_941_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__3(void){
_start:
{
lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_955_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__7, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__7_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__7);
v___x_956_ = ((lean_object*)(l_Lean_Doc_Parser_versoLinkUrl));
v___x_957_ = l_Lean_Parser_andthen(v___x_956_, v___x_955_);
return v___x_957_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__4(void){
_start:
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
v___x_958_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__3, &l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__3);
v___x_959_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__3, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__3);
v___x_960_ = l_Lean_Parser_andthen(v___x_959_, v___x_958_);
return v___x_960_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__5(void){
_start:
{
uint8_t v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; 
v___x_961_ = 0;
v___x_962_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__4, &l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__4);
v___x_963_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__2));
v___x_964_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__0));
v___x_965_ = l_Lean_Parser_nodeWithAntiquot(v___x_964_, v___x_963_, v___x_962_, v___x_961_);
return v___x_965_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_LinkTarget_url___lam__0(lean_object* v_c_966_, lean_object* v_s_967_){
_start:
{
lean_object* v___x_968_; lean_object* v_fn_969_; lean_object* v___x_970_; 
v___x_968_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__5, &l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__5_once, _init_l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__5);
v_fn_969_ = lean_ctor_get(v___x_968_, 1);
lean_inc_ref(v_fn_969_);
v___x_970_ = lean_apply_2(v_fn_969_, v_c_966_, v_s_967_);
return v___x_970_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1(){
_start:
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__2));
v___x_979_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1___closed__0));
v___x_980_ = l_Lean_addBuiltinDocString(v___x_978_, v___x_979_);
return v___x_980_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_981_;
v_res_981_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1();
stack->m_obj
 = v_res_981_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1___boxed(lean_object* v_a_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1();
return v_res_983_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__3(void){
_start:
{
lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_992_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__2));
v___x_993_ = l_Lean_Parser_symbol(v___x_992_);
return v___x_993_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__5(void){
_start:
{
lean_object* v___x_995_; lean_object* v___x_996_; 
v___x_995_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__4));
v___x_996_ = l_Lean_Parser_symbol(v___x_995_);
return v___x_996_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__6(void){
_start:
{
lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v___x_997_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__5, &l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__5_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__5);
v___x_998_ = ((lean_object*)(l_Lean_Doc_Parser_versoRef));
v___x_999_ = l_Lean_Parser_andthen(v___x_998_, v___x_997_);
return v___x_999_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__7(void){
_start:
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__6, &l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__6_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__6);
v___x_1001_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__3, &l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__3);
v___x_1002_ = l_Lean_Parser_andthen(v___x_1001_, v___x_1000_);
return v___x_1002_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__8(void){
_start:
{
uint8_t v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; 
v___x_1003_ = 0;
v___x_1004_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__7, &l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__7_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__7);
v___x_1005_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__1));
v___x_1006_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__0));
v___x_1007_ = l_Lean_Parser_nodeWithAntiquot(v___x_1006_, v___x_1005_, v___x_1004_, v___x_1003_);
return v___x_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_LinkTarget_ref___lam__0(lean_object* v_c_1008_, lean_object* v_s_1009_){
_start:
{
lean_object* v___x_1010_; lean_object* v_fn_1011_; lean_object* v___x_1012_; 
v___x_1010_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__8, &l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__8_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__8);
v_fn_1011_ = lean_ctor_get(v___x_1010_, 1);
lean_inc_ref(v_fn_1011_);
v___x_1012_ = lean_apply_2(v_fn_1011_, v_c_1008_, v_s_1009_);
return v___x_1012_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1(){
_start:
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1020_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__1));
v___x_1021_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1___closed__0));
v___x_1022_ = l_Lean_addBuiltinDocString(v___x_1020_, v___x_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1023_;
v_res_1023_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1();
stack->m_obj
 = v_res_1023_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1___boxed(lean_object* v_a_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1();
return v_res_1025_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_linkTarget___lam__0___closed__2(void){
_start:
{
uint8_t v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; 
v___x_1032_ = 1;
v___x_1033_ = ((lean_object*)(l_Lean_Doc_Parser_linkTarget___lam__0___closed__1));
v___x_1034_ = ((lean_object*)(l_Lean_Doc_Parser_linkTarget___lam__0___closed__0));
v___x_1035_ = l_Lean_Parser_mkAntiquot(v___x_1034_, v___x_1033_, v___x_1032_, v___x_1032_);
return v___x_1035_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_linkTarget___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; 
v___x_1036_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref));
v___x_1037_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_url));
v___x_1038_ = l_Lean_Parser_orelse(v___x_1037_, v___x_1036_);
return v___x_1038_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_linkTarget___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; 
v___x_1039_ = lean_obj_once(&l_Lean_Doc_Parser_linkTarget___lam__0___closed__3, &l_Lean_Doc_Parser_linkTarget___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_linkTarget___lam__0___closed__3);
v___x_1040_ = lean_obj_once(&l_Lean_Doc_Parser_linkTarget___lam__0___closed__2, &l_Lean_Doc_Parser_linkTarget___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_linkTarget___lam__0___closed__2);
v___x_1041_ = l_Lean_Parser_withAntiquot(v___x_1040_, v___x_1039_);
return v___x_1041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_linkTarget___lam__0(lean_object* v_c_1042_, lean_object* v_s_1043_){
_start:
{
lean_object* v___x_1044_; lean_object* v_fn_1045_; lean_object* v___x_1046_; 
v___x_1044_ = lean_obj_once(&l_Lean_Doc_Parser_linkTarget___lam__0___closed__4, &l_Lean_Doc_Parser_linkTarget___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_linkTarget___lam__0___closed__4);
v_fn_1045_ = lean_ctor_get(v___x_1044_, 1);
lean_inc_ref(v_fn_1045_);
v___x_1046_ = lean_apply_2(v_fn_1045_, v_c_1042_, v_s_1043_);
return v___x_1046_;
}
}
uint8_t l_instBEqOption_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(lean_object* v_x_1052_, lean_object* v_x_1053_){
_start:
{
if (lean_obj_tag(v_x_1052_) == 0)
{
if (lean_obj_tag(v_x_1053_) == 0)
{
uint8_t v___x_1054_; 
v___x_1054_ = 1;
return v___x_1054_;
}
else
{
uint8_t v___x_1055_; 
v___x_1055_ = 0;
return v___x_1055_;
}
}
else
{
if (lean_obj_tag(v_x_1053_) == 0)
{
uint8_t v___x_1056_; 
v___x_1056_ = 0;
return v___x_1056_;
}
else
{
lean_object* v_val_1057_; lean_object* v_val_1058_; uint8_t v___x_1059_; 
v_val_1057_ = lean_ctor_get(v_x_1052_, 0);
v_val_1058_ = lean_ctor_get(v_x_1053_, 0);
v___x_1059_ = l_Lean_Parser_instBEqError_beq(v_val_1057_, v_val_1058_);
return v___x_1059_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_1052_ = stack[0].m_obj;
lean_object* v_x_1053_ = stack[1].m_obj;
uint8_t v_res_1060_;
v_res_1060_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_x_1052_, v_x_1053_);
stack->m_num = v_res_1060_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1___boxed(lean_object* v_x_1061_, lean_object* v_x_1062_){
_start:
{
uint8_t v_res_1063_; lean_object* v_r_1064_; 
v_res_1063_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_x_1061_, v_x_1062_);
lean_dec(v_x_1062_);
lean_dec(v_x_1061_);
v_r_1064_ = lean_box(v_res_1063_);
return v_r_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0(lean_object* v_x_1065_, lean_object* v_st_1066_){
_start:
{
lean_inc_ref(v_st_1066_);
return v_st_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0___boxed(lean_object* v_x_1067_, lean_object* v_st_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0(v_x_1067_, v_st_1068_);
lean_dec_ref(v_st_1068_);
lean_dec_ref(v_x_1067_);
return v_res_1069_;
}
}
uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__0(uint32_t v___x_1070_, uint32_t v_x_1071_){
_start:
{
uint8_t v___x_1072_; 
v___x_1072_ = lean_uint32_dec_eq(v_x_1071_, v___x_1070_);
return v___x_1072_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v___x_1070_ = stack[0].m_num;
uint32_t v_x_1071_ = stack[1].m_num;
uint8_t v_res_1073_;
v_res_1073_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__0(v___x_1070_, v_x_1071_);
stack->m_num = v_res_1073_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__0___boxed(lean_object* v___x_1074_, lean_object* v_x_1075_){
_start:
{
uint32_t v___x_589__boxed_1076_; uint32_t v_x_590__boxed_1077_; uint8_t v_res_1078_; lean_object* v_r_1079_; 
v___x_589__boxed_1076_ = lean_unbox_uint32(v___x_1074_);
lean_dec(v___x_1074_);
v_x_590__boxed_1077_ = lean_unbox_uint32(v_x_1075_);
lean_dec(v_x_1075_);
v_res_1078_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__0(v___x_589__boxed_1076_, v_x_590__boxed_1077_);
v_r_1079_ = lean_box(v_res_1078_);
return v_r_1079_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__2(lean_object* v_b_1080_, lean_object* v___f_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
lean_object* v___x_1084_; 
v___x_1084_ = l_Lean_Parser_andthenFn(v_b_1080_, v___f_1081_, v___y_1082_, v___y_1083_);
return v___x_1084_;
}
}
lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__1(uint32_t v___x_1085_, lean_object* v___f_1086_, lean_object* v___y_1087_, lean_object* v___y_1088_){
_start:
{
lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; 
v___x_1089_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_1090_ = lean_string_push(v___x_1089_, v___x_1085_);
v___x_1091_ = l_Lean_Parser_satisfyFn(v___f_1086_, v___x_1090_, v___y_1087_, v___y_1088_);
return v___x_1091_;
}
}
LEAN_EXPORT void l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint32_t v___x_1085_ = stack[0].m_num;
lean_object* v___f_1086_ = stack[1].m_obj;
lean_object* v___y_1087_ = stack[2].m_obj;
lean_object* v___y_1088_ = stack[3].m_obj;
lean_object* v_res_1092_;
v_res_1092_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__1(v___x_1085_, v___f_1086_, v___y_1087_, v___y_1088_);
stack->m_obj
 = v_res_1092_;
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__1___boxed(lean_object* v___x_1093_, lean_object* v___f_1094_, lean_object* v___y_1095_, lean_object* v___y_1096_){
_start:
{
uint32_t v___x_615__boxed_1097_; lean_object* v_res_1098_; 
v___x_615__boxed_1097_ = lean_unbox_uint32(v___x_1093_);
lean_dec(v___x_1093_);
v_res_1098_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__1(v___x_615__boxed_1097_, v___f_1094_, v___y_1095_, v___y_1096_);
lean_dec_ref(v___y_1095_);
return v_res_1098_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg(lean_object* v___x_1099_, lean_object* v_s_1100_, lean_object* v_a_1101_, lean_object* v_b_1102_, lean_object* v___y_1103_, lean_object* v___y_1104_){
_start:
{
uint8_t v_decide_1105_; 
v_decide_1105_ = lean_nat_dec_eq(v_a_1101_, v___x_1099_);
if (v_decide_1105_ == 0)
{
uint32_t v___x_1106_; lean_object* v___x_1107_; lean_object* v___f_1108_; lean_object* v___x_1109_; lean_object* v___f_1110_; lean_object* v___f_1111_; lean_object* v___x_1112_; 
v___x_1106_ = lean_string_utf8_get_fast(v_s_1100_, v_a_1101_);
v___x_1107_ = lean_box_uint32(v___x_1106_);
v___f_1108_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1108_, 0, v___x_1107_);
v___x_1109_ = lean_box_uint32(v___x_1106_);
v___f_1110_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1110_, 0, v___x_1109_);
lean_closure_set(v___f_1110_, 1, v___f_1108_);
v___f_1111_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__2), 4, 2);
lean_closure_set(v___f_1111_, 0, v_b_1102_);
lean_closure_set(v___f_1111_, 1, v___f_1110_);
v___x_1112_ = lean_string_utf8_next_fast(v_s_1100_, v_a_1101_);
lean_dec(v_a_1101_);
v_a_1101_ = v___x_1112_;
v_b_1102_ = v___f_1111_;
goto _start;
}
else
{
lean_object* v___x_1114_; 
lean_dec(v_a_1101_);
v___x_1114_ = lean_apply_2(v_b_1102_, v___y_1103_, v___y_1104_);
return v___x_1114_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___boxed(lean_object* v___x_1115_, lean_object* v_s_1116_, lean_object* v_a_1117_, lean_object* v_b_1118_, lean_object* v___y_1119_, lean_object* v___y_1120_){
_start:
{
lean_object* v_res_1121_; 
v_res_1121_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg(v___x_1115_, v_s_1116_, v_a_1117_, v_b_1118_, v___y_1119_, v___y_1120_);
lean_dec_ref(v_s_1116_);
lean_dec(v___x_1115_);
return v_res_1121_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1(lean_object* v_s_1123_, lean_object* v___f_1124_, lean_object* v_c_1125_, lean_object* v_st_1126_){
_start:
{
lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v_st_x27_1129_; lean_object* v_errorMsg_1130_; lean_object* v___x_1131_; uint8_t v___x_1132_; 
v___x_1127_ = lean_string_utf8_byte_size(v_s_1123_);
v___x_1128_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_st_1126_);
v_st_x27_1129_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg(v___x_1127_, v_s_1123_, v___x_1128_, v___f_1124_, v_c_1125_, v_st_1126_);
v_errorMsg_1130_ = lean_ctor_get(v_st_x27_1129_, 4);
v___x_1131_ = lean_box(0);
v___x_1132_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_1130_, v___x_1131_);
if (v___x_1132_ == 0)
{
lean_object* v_pos_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v_pos_1133_ = lean_ctor_get(v_st_1126_, 2);
lean_inc(v_pos_1133_);
lean_dec_ref(v_st_1126_);
v___x_1134_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0));
v___x_1135_ = lean_string_append(v___x_1134_, v_s_1123_);
v___x_1136_ = lean_string_append(v___x_1135_, v___x_1134_);
v___x_1137_ = l_Lean_Parser_ParserState_mkErrorAt(v_st_x27_1129_, v___x_1136_, v_pos_1133_, v___x_1131_);
return v___x_1137_;
}
else
{
lean_dec_ref(v_st_1126_);
return v_st_x27_1129_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___boxed(lean_object* v_s_1138_, lean_object* v___f_1139_, lean_object* v_c_1140_, lean_object* v_st_1141_){
_start:
{
lean_object* v_res_1142_; 
v_res_1142_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1(v_s_1138_, v___f_1139_, v_c_1140_, v_st_1141_);
lean_dec_ref(v_s_1138_);
return v_res_1142_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(lean_object* v_s_1144_){
_start:
{
lean_object* v___f_1145_; lean_object* v___f_1146_; lean_object* v___x_1147_; uint8_t v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; 
v___f_1145_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__0));
v___f_1146_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1146_, 0, v_s_1144_);
lean_closure_set(v___f_1146_, 1, v___f_1145_);
v___x_1147_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_1148_ = 1;
v___x_1149_ = lean_box(v___x_1148_);
v___x_1150_ = lean_alloc_closure((void*)(l_Lean_Parser_rawFn___boxed), 4, 2);
lean_closure_set(v___x_1150_, 0, v___f_1146_);
lean_closure_set(v___x_1150_, 1, v___x_1149_);
v___x_1151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1147_);
lean_ctor_set(v___x_1151_, 1, v___x_1150_);
v___x_1152_ = l_Lean_Parser_tokenWithAntiquot(v___x_1151_);
return v___x_1152_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0(lean_object* v___x_1153_, lean_object* v___x_1154_, lean_object* v_s_1155_, lean_object* v_inst_1156_, lean_object* v_R_1157_, lean_object* v_a_1158_, lean_object* v_b_1159_, lean_object* v_c_1160_, lean_object* v___y_1161_, lean_object* v___y_1162_){
_start:
{
lean_object* v___x_1163_; 
v___x_1163_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg(v___x_1154_, v_s_1155_, v_a_1158_, v_b_1159_, v___y_1161_, v___y_1162_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___boxed(lean_object* v___x_1164_, lean_object* v___x_1165_, lean_object* v_s_1166_, lean_object* v_inst_1167_, lean_object* v_R_1168_, lean_object* v_a_1169_, lean_object* v_b_1170_, lean_object* v_c_1171_, lean_object* v___y_1172_, lean_object* v___y_1173_){
_start:
{
lean_object* v_res_1174_; 
v_res_1174_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0(v___x_1164_, v___x_1165_, v_s_1166_, v_inst_1167_, v_R_1168_, v_a_1169_, v_b_1170_, v_c_1171_, v___y_1172_, v___y_1173_);
lean_dec_ref(v_s_1166_);
lean_dec(v___x_1165_);
lean_dec_ref(v___x_1164_);
return v_res_1174_;
}
}
uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0(uint32_t v_ch_1175_, uint32_t v_x_1176_){
_start:
{
uint8_t v___x_1177_; 
v___x_1177_ = lean_uint32_dec_eq(v_x_1176_, v_ch_1175_);
return v___x_1177_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_ch_1175_ = stack[0].m_num;
uint32_t v_x_1176_ = stack[1].m_num;
uint8_t v_res_1178_;
v_res_1178_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0(v_ch_1175_, v_x_1176_);
stack->m_num = v_res_1178_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0___boxed(lean_object* v_ch_1179_, lean_object* v_x_1180_){
_start:
{
uint32_t v_ch_boxed_1181_; uint32_t v_x_149__boxed_1182_; uint8_t v_res_1183_; lean_object* v_r_1184_; 
v_ch_boxed_1181_ = lean_unbox_uint32(v_ch_1179_);
lean_dec(v_ch_1179_);
v_x_149__boxed_1182_ = lean_unbox_uint32(v_x_1180_);
lean_dec(v_x_1180_);
v_res_1183_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0(v_ch_boxed_1181_, v_x_149__boxed_1182_);
v_r_1184_ = lean_box(v_res_1183_);
return v_r_1184_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1(uint32_t v_ch_1186_, lean_object* v___f_1187_, lean_object* v_c_1188_, lean_object* v_st_1189_){
_start:
{
lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v_st_x27_1195_; lean_object* v_errorMsg_1196_; lean_object* v___x_1197_; uint8_t v___x_1198_; 
v___x_1190_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0));
v___x_1191_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_1192_ = lean_string_push(v___x_1191_, v_ch_1186_);
v___x_1193_ = lean_string_append(v___x_1190_, v___x_1192_);
v___x_1194_ = lean_string_append(v___x_1193_, v___x_1190_);
lean_inc_ref(v_st_1189_);
v_st_x27_1195_ = l_Lean_Parser_takeWhile1Fn(v___f_1187_, v___x_1194_, v_c_1188_, v_st_1189_);
v_errorMsg_1196_ = lean_ctor_get(v_st_x27_1195_, 4);
v___x_1197_ = lean_box(0);
v___x_1198_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_1196_, v___x_1197_);
if (v___x_1198_ == 0)
{
lean_object* v_pos_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v_pos_1199_ = lean_ctor_get(v_st_1189_, 2);
lean_inc(v_pos_1199_);
lean_dec_ref(v_st_1189_);
v___x_1200_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___closed__0));
v___x_1201_ = lean_string_append(v___x_1200_, v___x_1192_);
lean_dec_ref(v___x_1192_);
v___x_1202_ = lean_string_append(v___x_1201_, v___x_1190_);
v___x_1203_ = l_Lean_Parser_ParserState_mkErrorAt(v_st_x27_1195_, v___x_1202_, v_pos_1199_, v___x_1197_);
return v___x_1203_;
}
else
{
lean_dec_ref(v___x_1192_);
lean_dec_ref(v_st_1189_);
return v_st_x27_1195_;
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1_0interp(lean_interpreter_value* stack)
{
uint32_t v_ch_1186_ = stack[0].m_num;
lean_object* v___f_1187_ = stack[1].m_obj;
lean_object* v_c_1188_ = stack[2].m_obj;
lean_object* v_st_1189_ = stack[3].m_obj;
lean_object* v_res_1204_;
v_res_1204_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1(v_ch_1186_, v___f_1187_, v_c_1188_, v_st_1189_);
stack->m_obj
 = v_res_1204_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___boxed(lean_object* v_ch_1205_, lean_object* v___f_1206_, lean_object* v_c_1207_, lean_object* v_st_1208_){
_start:
{
uint32_t v_ch_boxed_1209_; lean_object* v_res_1210_; 
v_ch_boxed_1209_ = lean_unbox_uint32(v_ch_1205_);
lean_dec(v_ch_1205_);
v_res_1210_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1(v_ch_boxed_1209_, v___f_1206_, v_c_1207_, v_st_1208_);
return v_res_1210_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(uint32_t v_ch_1211_){
_start:
{
lean_object* v___x_1212_; lean_object* v___f_1213_; lean_object* v___x_1214_; lean_object* v___f_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1212_ = lean_box_uint32(v_ch_1211_);
v___f_1213_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1213_, 0, v___x_1212_);
v___x_1214_ = lean_box_uint32(v_ch_1211_);
v___f_1215_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1215_, 0, v___x_1214_);
lean_closure_set(v___f_1215_, 1, v___f_1213_);
v___x_1216_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_1217_ = 1;
v___x_1218_ = lean_box(v___x_1217_);
v___x_1219_ = lean_alloc_closure((void*)(l_Lean_Parser_rawFn___boxed), 4, 2);
lean_closure_set(v___x_1219_, 0, v___f_1215_);
lean_closure_set(v___x_1219_, 1, v___x_1218_);
v___x_1220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1220_, 0, v___x_1216_);
lean_ctor_set(v___x_1220_, 1, v___x_1219_);
v___x_1221_ = l_Lean_Parser_tokenWithAntiquot(v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun_0interp(lean_interpreter_value* stack)
{
uint32_t v_ch_1211_ = stack[0].m_num;
lean_object* v_res_1222_;
v_res_1222_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v_ch_1211_);
stack->m_obj
 = v_res_1222_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___boxed(lean_object* v_ch_1223_){
_start:
{
uint32_t v_ch_boxed_1224_; lean_object* v_res_1225_; 
v_ch_boxed_1224_ = lean_unbox_uint32(v_ch_1223_);
lean_dec(v_ch_1223_);
v_res_1225_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v_ch_boxed_1224_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0(lean_object* v_c_1227_, lean_object* v_s_1228_){
_start:
{
lean_object* v_toInputContext_1229_; lean_object* v_pos_1230_; uint8_t v___x_1231_; 
v_toInputContext_1229_ = lean_ctor_get(v_c_1227_, 0);
v_pos_1230_ = lean_ctor_get(v_s_1228_, 2);
v___x_1231_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1229_, v_pos_1230_);
if (v___x_1231_ == 0)
{
lean_object* v_inputString_1232_; uint32_t v_ch_1233_; uint32_t v___x_1234_; uint8_t v___x_1235_; 
lean_inc(v_pos_1230_);
v_inputString_1232_ = lean_ctor_get(v_toInputContext_1229_, 0);
v_ch_1233_ = lean_string_utf8_get_fast(v_inputString_1232_, v_pos_1230_);
v___x_1234_ = 42;
v___x_1235_ = lean_uint32_dec_eq(v_ch_1233_, v___x_1234_);
if (v___x_1235_ == 0)
{
uint32_t v___x_1236_; uint8_t v___x_1237_; 
v___x_1236_ = 45;
v___x_1237_ = lean_uint32_dec_eq(v_ch_1233_, v___x_1236_);
if (v___x_1237_ == 0)
{
uint32_t v___x_1238_; uint8_t v___x_1239_; 
v___x_1238_ = 43;
v___x_1239_ = lean_uint32_dec_eq(v_ch_1233_, v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0___closed__0));
v___x_1241_ = lean_box(0);
v___x_1242_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_1228_, v___x_1240_, v_pos_1230_, v___x_1241_);
return v___x_1242_;
}
else
{
lean_object* v___x_1243_; 
v___x_1243_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1228_, v_c_1227_, v_pos_1230_);
lean_dec(v_pos_1230_);
return v___x_1243_;
}
}
else
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1228_, v_c_1227_, v_pos_1230_);
lean_dec(v_pos_1230_);
return v___x_1244_;
}
}
else
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1228_, v_c_1227_, v_pos_1230_);
lean_dec(v_pos_1230_);
return v___x_1245_;
}
}
else
{
lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1246_ = lean_box(0);
v___x_1247_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1228_, v___x_1246_);
return v___x_1247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0___boxed(lean_object* v_c_1248_, lean_object* v_s_1249_){
_start:
{
lean_object* v_res_1250_; 
v_res_1250_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0(v_c_1248_, v_s_1249_);
lean_dec_ref(v_c_1248_);
return v_res_1250_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__3(lean_object* v___f_1251_, lean_object* v___f_1252_, lean_object* v___f_1253_, lean_object* v_c_1254_, lean_object* v_s_1255_){
_start:
{
lean_object* v___x_1256_; lean_object* v___x_1257_; uint8_t v___x_1258_; lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v_fn_1263_; lean_object* v___x_1264_; 
v___x_1256_ = lean_box(1);
v___x_1257_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1257_, 0, v___f_1251_);
lean_ctor_set(v___x_1257_, 1, v___f_1252_);
lean_ctor_set(v___x_1257_, 2, v___x_1256_);
v___x_1258_ = 1;
v___x_1259_ = lean_box(v___x_1258_);
v___x_1260_ = lean_alloc_closure((void*)(l_Lean_Parser_rawFn___boxed), 4, 2);
lean_closure_set(v___x_1260_, 0, v___f_1253_);
lean_closure_set(v___x_1260_, 1, v___x_1259_);
v___x_1261_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1261_, 0, v___x_1257_);
lean_ctor_set(v___x_1261_, 1, v___x_1260_);
v___x_1262_ = l_Lean_Parser_tokenWithAntiquot(v___x_1261_);
v_fn_1263_ = lean_ctor_get(v___x_1262_, 1);
lean_inc_ref(v_fn_1263_);
lean_dec_ref(v___x_1262_);
v___x_1264_ = lean_apply_2(v_fn_1263_, v_c_1254_, v_s_1255_);
return v___x_1264_;
}
}
uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0(uint32_t v_x_1274_){
_start:
{
uint32_t v___x_1275_; uint8_t v___x_1276_; 
v___x_1275_ = 48;
v___x_1276_ = lean_uint32_dec_le(v___x_1275_, v_x_1274_);
if (v___x_1276_ == 0)
{
return v___x_1276_;
}
else
{
uint32_t v___x_1277_; uint8_t v___x_1278_; 
v___x_1277_ = 57;
v___x_1278_ = lean_uint32_dec_le(v_x_1274_, v___x_1277_);
return v___x_1278_;
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_x_1274_ = stack[0].m_num;
uint8_t v_res_1279_;
v_res_1279_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0(v_x_1274_);
stack->m_num = v_res_1279_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0___boxed(lean_object* v_x_1280_){
_start:
{
uint32_t v_x_330__boxed_1281_; uint8_t v_res_1282_; lean_object* v_r_1283_; 
v_x_330__boxed_1281_ = lean_unbox_uint32(v_x_1280_);
lean_dec(v_x_1280_);
v_res_1282_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0(v_x_330__boxed_1281_);
v_r_1283_ = lean_box(v_res_1282_);
return v_r_1283_;
}
}
uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1(uint32_t v_c_1284_){
_start:
{
uint32_t v___x_1285_; uint8_t v___x_1286_; 
v___x_1285_ = 46;
v___x_1286_ = lean_uint32_dec_eq(v_c_1284_, v___x_1285_);
if (v___x_1286_ == 0)
{
uint32_t v___x_1287_; uint8_t v___x_1288_; 
v___x_1287_ = 41;
v___x_1288_ = lean_uint32_dec_eq(v_c_1284_, v___x_1287_);
return v___x_1288_;
}
else
{
return v___x_1286_;
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_1284_ = stack[0].m_num;
uint8_t v_res_1289_;
v_res_1289_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1(v_c_1284_);
stack->m_num = v_res_1289_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1___boxed(lean_object* v_c_1290_){
_start:
{
uint32_t v_c_boxed_1291_; uint8_t v_res_1292_; lean_object* v_r_1293_; 
v_c_boxed_1291_ = lean_unbox_uint32(v_c_1290_);
lean_dec(v_c_1290_);
v_res_1292_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1(v_c_boxed_1291_);
v_r_1293_ = lean_box(v_res_1292_);
return v_r_1293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2(lean_object* v___f_1295_, lean_object* v___y_1296_, lean_object* v___y_1297_){
_start:
{
lean_object* v___x_1298_; lean_object* v___x_1299_; 
v___x_1298_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2___closed__0));
v___x_1299_ = l_Lean_Parser_satisfyFn(v___f_1295_, v___x_1298_, v___y_1296_, v___y_1297_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2___boxed(lean_object* v___f_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_){
_start:
{
lean_object* v_res_1303_; 
v_res_1303_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2(v___f_1300_, v___y_1301_, v___y_1302_);
lean_dec_ref(v___y_1301_);
return v_res_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3(lean_object* v___f_1306_, lean_object* v___f_1307_, lean_object* v_c_1308_, lean_object* v_s_1309_){
_start:
{
lean_object* v___x_1310_; lean_object* v___x_1311_; lean_object* v_s_x27_1312_; lean_object* v_errorMsg_1313_; lean_object* v___x_1314_; uint8_t v___x_1315_; 
v___x_1310_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3___closed__0));
v___x_1311_ = lean_alloc_closure((void*)(l_Lean_Parser_takeWhile1Fn), 4, 2);
lean_closure_set(v___x_1311_, 0, v___f_1306_);
lean_closure_set(v___x_1311_, 1, v___x_1310_);
lean_inc_ref(v_s_1309_);
v_s_x27_1312_ = l_Lean_Parser_andthenFn(v___x_1311_, v___f_1307_, v_c_1308_, v_s_1309_);
v_errorMsg_1313_ = lean_ctor_get(v_s_x27_1312_, 4);
v___x_1314_ = lean_box(0);
v___x_1315_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_1313_, v___x_1314_);
if (v___x_1315_ == 0)
{
lean_object* v_pos_1316_; lean_object* v___x_1317_; lean_object* v___x_1318_; 
v_pos_1316_ = lean_ctor_get(v_s_1309_, 2);
lean_inc(v_pos_1316_);
lean_dec_ref(v_s_1309_);
v___x_1317_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3___closed__1));
v___x_1318_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_x27_1312_, v___x_1317_, v_pos_1316_, v___x_1314_);
return v___x_1318_;
}
else
{
lean_dec_ref(v_s_1309_);
return v_s_x27_1312_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__0(lean_object* v_c_1335_){
_start:
{
lean_object* v_toInputContext_1336_; lean_object* v_toParserModuleContext_1337_; lean_object* v_toCacheableParserContext_1338_; lean_object* v_tokens_1339_; lean_object* v___x_1341_; uint8_t v_isShared_1342_; uint8_t v_isSharedCheck_1348_; 
v_toInputContext_1336_ = lean_ctor_get(v_c_1335_, 0);
v_toParserModuleContext_1337_ = lean_ctor_get(v_c_1335_, 1);
v_toCacheableParserContext_1338_ = lean_ctor_get(v_c_1335_, 2);
v_tokens_1339_ = lean_ctor_get(v_c_1335_, 3);
v_isSharedCheck_1348_ = !lean_is_exclusive(v_c_1335_);
if (v_isSharedCheck_1348_ == 0)
{
v___x_1341_ = v_c_1335_;
v_isShared_1342_ = v_isSharedCheck_1348_;
goto v_resetjp_1340_;
}
else
{
lean_inc(v_tokens_1339_);
lean_inc(v_toCacheableParserContext_1338_);
lean_inc(v_toParserModuleContext_1337_);
lean_inc(v_toInputContext_1336_);
lean_dec(v_c_1335_);
v___x_1341_ = lean_box(0);
v_isShared_1342_ = v_isSharedCheck_1348_;
goto v_resetjp_1340_;
}
v_resetjp_1340_:
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1346_; 
v___x_1343_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__0___closed__0));
v___x_1344_ = l_Lean_Data_Trie_insert___redArg(v_tokens_1339_, v___x_1343_, v___x_1343_);
if (v_isShared_1342_ == 0)
{
lean_ctor_set(v___x_1341_, 3, v___x_1344_);
v___x_1346_ = v___x_1341_;
goto v_reusejp_1345_;
}
else
{
lean_object* v_reuseFailAlloc_1347_; 
v_reuseFailAlloc_1347_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1347_, 0, v_toInputContext_1336_);
lean_ctor_set(v_reuseFailAlloc_1347_, 1, v_toParserModuleContext_1337_);
lean_ctor_set(v_reuseFailAlloc_1347_, 2, v_toCacheableParserContext_1338_);
lean_ctor_set(v_reuseFailAlloc_1347_, 3, v___x_1344_);
v___x_1346_ = v_reuseFailAlloc_1347_;
goto v_reusejp_1345_;
}
v_reusejp_1345_:
{
return v___x_1346_;
}
}
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__4(void){
_start:
{
uint8_t v___x_1357_; uint8_t v___x_1358_; lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
v___x_1357_ = 0;
v___x_1358_ = 1;
v___x_1359_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__3));
v___x_1360_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__0));
v___x_1361_ = l_Lean_Parser_mkAntiquot(v___x_1360_, v___x_1359_, v___x_1358_, v___x_1357_);
return v___x_1361_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__5));
v___x_1364_ = l_Lean_Parser_symbol(v___x_1363_);
return v___x_1364_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__10(void){
_start:
{
lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1369_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__9));
v___x_1370_ = l_Lean_Parser_symbol(v___x_1369_);
return v___x_1370_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__11(void){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v_p_1374_; 
v___x_1371_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__10, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__10_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__10);
v___x_1372_ = l_Lean_Parser_Term_structInstField;
v___x_1373_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__8));
v_p_1374_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1373_, v___x_1372_, v___x_1371_);
return v_p_1374_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__13(void){
_start:
{
lean_object* v___x_1376_; lean_object* v___x_1377_; 
v___x_1376_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__12));
v___x_1377_ = l_Lean_Parser_checkColGe(v___x_1376_);
return v___x_1377_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__14(void){
_start:
{
lean_object* v_p_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; 
v_p_1378_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__11, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__11_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__11);
v___x_1379_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__13, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__13_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__13);
v___x_1380_ = l_Lean_Parser_andthen(v___x_1379_, v_p_1378_);
return v___x_1380_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__15(void){
_start:
{
lean_object* v___x_1381_; lean_object* v___x_1382_; 
v___x_1381_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__12));
v___x_1382_ = l_Lean_Parser_checkColEq(v___x_1381_);
return v___x_1382_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__17(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__16));
v___x_1385_ = l_Lean_Parser_checkLinebreakBefore(v___x_1384_);
return v___x_1385_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__18(void){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1386_ = l_Lean_Parser_pushNone;
v___x_1387_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__17, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__17_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__17);
v___x_1388_ = l_Lean_Parser_andthen(v___x_1387_, v___x_1386_);
return v___x_1388_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__19(void){
_start:
{
lean_object* v___x_1389_; lean_object* v___x_1390_; lean_object* v___x_1391_; 
v___x_1389_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__18, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__18_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__18);
v___x_1390_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__15, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__15_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__15);
v___x_1391_ = l_Lean_Parser_andthen(v___x_1390_, v___x_1389_);
return v___x_1391_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__20(void){
_start:
{
lean_object* v___x_1392_; lean_object* v___x_1393_; lean_object* v___x_1394_; 
v___x_1392_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__19, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__19_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__19);
v___x_1393_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__6);
v___x_1394_ = l_Lean_Parser_orelse(v___x_1393_, v___x_1392_);
return v___x_1394_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__21(void){
_start:
{
uint8_t v___x_1395_; lean_object* v___x_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; 
v___x_1395_ = 1;
v___x_1396_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__20, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__20_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__20);
v___x_1397_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__5));
v___x_1398_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__14, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__14_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__14);
v___x_1399_ = l_Lean_Parser_sepBy(v___x_1398_, v___x_1397_, v___x_1396_, v___x_1395_);
return v___x_1399_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__22(void){
_start:
{
lean_object* v___x_1400_; lean_object* v___x_1401_; 
v___x_1400_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__21, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__21_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__21);
v___x_1401_ = l_Lean_Parser_withPosition(v___x_1400_);
return v___x_1401_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__23(void){
_start:
{
lean_object* v___x_1402_; lean_object* v___x_1403_; 
v___x_1402_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__22, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__22_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__22);
v___x_1403_ = l_Lean_Parser_Term_structInstFields(v___x_1402_);
return v___x_1403_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__24(void){
_start:
{
lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1404_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__23, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__23_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__23);
v___x_1405_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__4);
v___x_1406_ = l_Lean_Parser_withAntiquot(v___x_1405_, v___x_1404_);
return v___x_1406_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1(lean_object* v___f_1407_, lean_object* v_c_1408_, lean_object* v_s_1409_){
_start:
{
lean_object* v___x_1410_; lean_object* v_fn_1411_; lean_object* v___x_1412_; 
v___x_1410_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__24, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__24_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__24);
v_fn_1411_ = lean_ctor_get(v___x_1410_, 1);
lean_inc_ref(v_fn_1411_);
v___x_1412_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_1407_, v_fn_1411_, v_c_1408_, v_s_1409_);
return v___x_1412_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_headerMarker___lam__0___closed__2(void){
_start:
{
uint32_t v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = 35;
v___x_1427_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_1426_);
return v___x_1427_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_headerMarker___lam__0___closed__3(void){
_start:
{
uint8_t v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1428_ = 0;
v___x_1429_ = lean_obj_once(&l_Lean_Doc_Parser_headerMarker___lam__0___closed__2, &l_Lean_Doc_Parser_headerMarker___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_headerMarker___lam__0___closed__2);
v___x_1430_ = ((lean_object*)(l_Lean_Doc_Parser_headerMarker___lam__0___closed__1));
v___x_1431_ = ((lean_object*)(l_Lean_Doc_Parser_headerMarker___lam__0___closed__0));
v___x_1432_ = l_Lean_Parser_nodeWithAntiquot(v___x_1431_, v___x_1430_, v___x_1429_, v___x_1428_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_headerMarker___lam__0(lean_object* v_c_1433_, lean_object* v_s_1434_){
_start:
{
lean_object* v___x_1435_; lean_object* v_fn_1436_; lean_object* v___x_1437_; 
v___x_1435_ = lean_obj_once(&l_Lean_Doc_Parser_headerMarker___lam__0___closed__3, &l_Lean_Doc_Parser_headerMarker___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_headerMarker___lam__0___closed__3);
v_fn_1436_ = lean_ctor_get(v___x_1435_, 1);
lean_inc_ref(v_fn_1436_);
v___x_1437_ = lean_apply_2(v_fn_1436_, v_c_1433_, v_s_1434_);
return v___x_1437_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_listMarker___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1449_; lean_object* v___x_1450_; 
v___x_1449_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom));
v___x_1450_ = l_Lean_Parser_atomic(v___x_1449_);
return v___x_1450_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_listMarker___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; 
v___x_1451_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom));
v___x_1452_ = lean_obj_once(&l_Lean_Doc_Parser_listMarker___lam__0___closed__2, &l_Lean_Doc_Parser_listMarker___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_listMarker___lam__0___closed__2);
v___x_1453_ = l_Lean_Parser_orelse(v___x_1452_, v___x_1451_);
return v___x_1453_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_listMarker___lam__0___closed__4(void){
_start:
{
uint8_t v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1454_ = 0;
v___x_1455_ = lean_obj_once(&l_Lean_Doc_Parser_listMarker___lam__0___closed__3, &l_Lean_Doc_Parser_listMarker___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_listMarker___lam__0___closed__3);
v___x_1456_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___lam__0___closed__1));
v___x_1457_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___lam__0___closed__0));
v___x_1458_ = l_Lean_Parser_nodeWithAntiquot(v___x_1457_, v___x_1456_, v___x_1455_, v___x_1454_);
return v___x_1458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_listMarker___lam__0(lean_object* v_c_1459_, lean_object* v_s_1460_){
_start:
{
lean_object* v___x_1461_; lean_object* v_fn_1462_; lean_object* v___x_1463_; 
v___x_1461_ = lean_obj_once(&l_Lean_Doc_Parser_listMarker___lam__0___closed__4, &l_Lean_Doc_Parser_listMarker___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_listMarker___lam__0___closed__4);
v_fn_1462_ = lean_ctor_get(v___x_1461_, 1);
lean_inc_ref(v_fn_1462_);
v___x_1463_ = lean_apply_2(v_fn_1462_, v_c_1459_, v_s_1460_);
return v___x_1463_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___lam__0___closed__0(void){
_start:
{
uint8_t v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1469_ = 0;
v___x_1470_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom));
v___x_1471_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___lam__0___closed__1));
v___x_1472_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___lam__0___closed__0));
v___x_1473_ = l_Lean_Parser_nodeWithAntiquot(v___x_1472_, v___x_1471_, v___x_1470_, v___x_1469_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___lam__0(lean_object* v_c_1474_, lean_object* v_s_1475_){
_start:
{
lean_object* v___x_1476_; lean_object* v_fn_1477_; lean_object* v___x_1478_; 
v___x_1476_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___lam__0___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___lam__0___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___lam__0___closed__0);
v_fn_1477_ = lean_ctor_get(v___x_1476_, 1);
lean_inc_ref(v_fn_1477_);
v___x_1478_ = lean_apply_2(v_fn_1477_, v_c_1474_, v_s_1475_);
return v___x_1478_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___lam__0___closed__0(void){
_start:
{
uint8_t v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; 
v___x_1484_ = 0;
v___x_1485_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom));
v___x_1486_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___lam__0___closed__1));
v___x_1487_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___lam__0___closed__0));
v___x_1488_ = l_Lean_Parser_nodeWithAntiquot(v___x_1487_, v___x_1486_, v___x_1485_, v___x_1484_);
return v___x_1488_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___lam__0(lean_object* v_c_1489_, lean_object* v_s_1490_){
_start:
{
lean_object* v___x_1491_; lean_object* v_fn_1492_; lean_object* v___x_1493_; 
v___x_1491_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___lam__0___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___lam__0___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___lam__0___closed__0);
v_fn_1492_ = lean_ctor_get(v___x_1491_, 1);
lean_inc_ref(v_fn_1492_);
v___x_1493_ = lean_apply_2(v_fn_1492_, v_c_1489_, v_s_1490_);
return v___x_1493_;
}
}
uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0(uint32_t v_x_1499_){
_start:
{
uint32_t v___x_1500_; uint8_t v___x_1501_; 
v___x_1500_ = 58;
v___x_1501_ = lean_uint32_dec_eq(v_x_1499_, v___x_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_x_1499_ = stack[0].m_num;
uint8_t v_res_1502_;
v_res_1502_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0(v_x_1499_);
stack->m_num = v_res_1502_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0___boxed(lean_object* v_x_1503_){
_start:
{
uint32_t v_x_136__boxed_1504_; uint8_t v_res_1505_; lean_object* v_r_1506_; 
v_x_136__boxed_1504_ = lean_unbox_uint32(v_x_1503_);
lean_dec(v_x_1503_);
v_res_1505_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0(v_x_136__boxed_1504_);
v_r_1506_ = lean_box(v_res_1505_);
return v_r_1506_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1508_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__0));
v___x_1509_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_1508_);
return v___x_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3(lean_object* v___f_1511_, lean_object* v___f_1512_, lean_object* v___f_1513_, lean_object* v_c_1514_, lean_object* v_s_1515_){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v_fn_1525_; lean_object* v___x_1526_; 
v___x_1516_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__1);
v___x_1517_ = lean_box(1);
v___x_1518_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1518_, 0, v___f_1511_);
lean_ctor_set(v___x_1518_, 1, v___f_1512_);
lean_ctor_set(v___x_1518_, 2, v___x_1517_);
v___x_1519_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__2));
v___x_1520_ = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(v___x_1520_, 0, v___f_1513_);
lean_closure_set(v___x_1520_, 1, v___x_1519_);
v___x_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1521_, 0, v___x_1518_);
lean_ctor_set(v___x_1521_, 1, v___x_1520_);
v___x_1522_ = l_Lean_Parser_notFollowedBy(v___x_1521_, v___x_1519_);
v___x_1523_ = l_Lean_Parser_andthen(v___x_1516_, v___x_1522_);
v___x_1524_ = l_Lean_Parser_atomic(v___x_1523_);
v_fn_1525_ = lean_ctor_get(v___x_1524_, 1);
lean_inc_ref(v_fn_1525_);
lean_dec_ref(v___x_1524_);
v___x_1526_ = lean_apply_2(v_fn_1525_, v_c_1514_, v_s_1515_);
return v___x_1526_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__2(void){
_start:
{
uint32_t v___x_1542_; lean_object* v___x_1543_; 
v___x_1542_ = 95;
v___x_1543_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_1542_);
return v___x_1543_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__3(void){
_start:
{
uint8_t v___x_1544_; lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; 
v___x_1544_ = 0;
v___x_1545_ = lean_obj_once(&l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__2, &l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__2);
v___x_1546_ = ((lean_object*)(l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__1));
v___x_1547_ = ((lean_object*)(l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__0));
v___x_1548_ = l_Lean_Parser_nodeWithAntiquot(v___x_1547_, v___x_1546_, v___x_1545_, v___x_1544_);
return v___x_1548_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_emphDelimiter___lam__0(lean_object* v_c_1549_, lean_object* v_s_1550_){
_start:
{
lean_object* v___x_1551_; lean_object* v_fn_1552_; lean_object* v___x_1553_; 
v___x_1551_ = lean_obj_once(&l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__3, &l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__3);
v_fn_1552_ = lean_ctor_get(v___x_1551_, 1);
lean_inc_ref(v_fn_1552_);
v___x_1553_ = lean_apply_2(v_fn_1552_, v_c_1549_, v_s_1550_);
return v___x_1553_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__2(void){
_start:
{
uint32_t v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = 42;
v___x_1566_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_1565_);
return v___x_1566_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__3(void){
_start:
{
uint8_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1567_ = 0;
v___x_1568_ = lean_obj_once(&l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__2, &l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__2);
v___x_1569_ = ((lean_object*)(l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__1));
v___x_1570_ = ((lean_object*)(l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__0));
v___x_1571_ = l_Lean_Parser_nodeWithAntiquot(v___x_1570_, v___x_1569_, v___x_1568_, v___x_1567_);
return v___x_1571_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_boldDelimiter___lam__0(lean_object* v_c_1572_, lean_object* v_s_1573_){
_start:
{
lean_object* v___x_1574_; lean_object* v_fn_1575_; lean_object* v___x_1576_; 
v___x_1574_ = lean_obj_once(&l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__3, &l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__3);
v_fn_1575_ = lean_ctor_get(v___x_1574_, 1);
lean_inc_ref(v_fn_1575_);
v___x_1576_ = lean_apply_2(v_fn_1575_, v_c_1572_, v_s_1573_);
return v___x_1576_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2(void){
_start:
{
uint32_t v___x_1588_; lean_object* v___x_1589_; 
v___x_1588_ = 96;
v___x_1589_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_1588_);
return v___x_1589_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__3(void){
_start:
{
uint8_t v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1590_ = 0;
v___x_1591_ = lean_obj_once(&l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2, &l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2);
v___x_1592_ = ((lean_object*)(l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__1));
v___x_1593_ = ((lean_object*)(l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__0));
v___x_1594_ = l_Lean_Parser_nodeWithAntiquot(v___x_1593_, v___x_1592_, v___x_1591_, v___x_1590_);
return v___x_1594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_codeDelimiter___lam__0(lean_object* v_c_1595_, lean_object* v_s_1596_){
_start:
{
lean_object* v___x_1597_; lean_object* v_fn_1598_; lean_object* v___x_1599_; 
v___x_1597_ = lean_obj_once(&l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__3, &l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__3);
v_fn_1598_ = lean_ctor_get(v___x_1597_, 1);
lean_inc_ref(v_fn_1598_);
v___x_1599_ = lean_apply_2(v_fn_1598_, v_c_1595_, v_s_1596_);
return v___x_1599_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__2(void){
_start:
{
uint8_t v___x_1611_; lean_object* v___x_1612_; lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1611_ = 0;
v___x_1612_ = lean_obj_once(&l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2, &l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2);
v___x_1613_ = ((lean_object*)(l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__1));
v___x_1614_ = ((lean_object*)(l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__0));
v___x_1615_ = l_Lean_Parser_nodeWithAntiquot(v___x_1614_, v___x_1613_, v___x_1612_, v___x_1611_);
return v___x_1615_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_codeBlockFence___lam__0(lean_object* v_c_1616_, lean_object* v_s_1617_){
_start:
{
lean_object* v___x_1618_; lean_object* v_fn_1619_; lean_object* v___x_1620_; 
v___x_1618_ = lean_obj_once(&l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__2, &l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__2);
v_fn_1619_ = lean_ctor_get(v___x_1618_, 1);
lean_inc_ref(v_fn_1619_);
v___x_1620_ = lean_apply_2(v_fn_1619_, v_c_1616_, v_s_1617_);
return v___x_1620_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1633_ = ((lean_object*)(l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__2));
v___x_1634_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_1633_);
return v___x_1634_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__4(void){
_start:
{
uint8_t v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1635_ = 0;
v___x_1636_ = lean_obj_once(&l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__3, &l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__3);
v___x_1637_ = ((lean_object*)(l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__1));
v___x_1638_ = ((lean_object*)(l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__0));
v___x_1639_ = l_Lean_Parser_nodeWithAntiquot(v___x_1638_, v___x_1637_, v___x_1636_, v___x_1635_);
return v___x_1639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_inlineMathMarker___lam__0(lean_object* v_c_1640_, lean_object* v_s_1641_){
_start:
{
lean_object* v___x_1642_; lean_object* v_fn_1643_; lean_object* v___x_1644_; 
v___x_1642_ = lean_obj_once(&l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__4, &l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__4);
v_fn_1643_ = lean_ctor_get(v___x_1642_, 1);
lean_inc_ref(v_fn_1643_);
v___x_1644_ = lean_apply_2(v_fn_1643_, v_c_1640_, v_s_1641_);
return v___x_1644_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1657_ = ((lean_object*)(l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__2));
v___x_1658_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_1657_);
return v___x_1658_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__4(void){
_start:
{
uint8_t v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1659_ = 0;
v___x_1660_ = lean_obj_once(&l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__3, &l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__3);
v___x_1661_ = ((lean_object*)(l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__1));
v___x_1662_ = ((lean_object*)(l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__0));
v___x_1663_ = l_Lean_Parser_nodeWithAntiquot(v___x_1662_, v___x_1661_, v___x_1660_, v___x_1659_);
return v___x_1663_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_displayMathMarker___lam__0(lean_object* v_c_1664_, lean_object* v_s_1665_){
_start:
{
lean_object* v___x_1666_; lean_object* v_fn_1667_; lean_object* v___x_1668_; 
v___x_1666_ = lean_obj_once(&l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__4, &l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__4);
v_fn_1667_ = lean_ctor_get(v___x_1666_, 1);
lean_inc_ref(v_fn_1667_);
v___x_1668_ = lean_apply_2(v_fn_1667_, v_c_1664_, v_s_1665_);
return v___x_1668_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__2(void){
_start:
{
uint32_t v___x_1680_; lean_object* v___x_1681_; 
v___x_1680_ = 58;
v___x_1681_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_1680_);
return v___x_1681_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__3(void){
_start:
{
uint8_t v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1682_ = 0;
v___x_1683_ = lean_obj_once(&l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__2, &l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__2);
v___x_1684_ = ((lean_object*)(l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__1));
v___x_1685_ = ((lean_object*)(l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__0));
v___x_1686_ = l_Lean_Parser_nodeWithAntiquot(v___x_1685_, v___x_1684_, v___x_1683_, v___x_1682_);
return v___x_1686_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_directiveDelimiter___lam__0(lean_object* v_c_1687_, lean_object* v_s_1688_){
_start:
{
lean_object* v___x_1689_; lean_object* v_fn_1690_; lean_object* v___x_1691_; 
v___x_1689_ = lean_obj_once(&l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__3, &l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__3);
v_fn_1690_ = lean_ctor_get(v___x_1689_, 1);
lean_inc_ref(v_fn_1690_);
v___x_1691_ = lean_apply_2(v_fn_1690_, v_c_1687_, v_s_1688_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength(lean_object* v_x_1697_){
_start:
{
if (lean_obj_tag(v_x_1697_) == 1)
{
lean_object* v_args_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; uint8_t v___x_1701_; 
v_args_1698_ = lean_ctor_get(v_x_1697_, 2);
v___x_1699_ = lean_array_get_size(v_args_1698_);
v___x_1700_ = lean_unsigned_to_nat(1u);
v___x_1701_ = lean_nat_dec_eq(v___x_1699_, v___x_1700_);
if (v___x_1701_ == 0)
{
lean_object* v___x_1702_; 
v___x_1702_ = lean_box(0);
return v___x_1702_;
}
else
{
lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1703_ = lean_unsigned_to_nat(0u);
v___x_1704_ = lean_array_fget_borrowed(v_args_1698_, v___x_1703_);
if (lean_obj_tag(v___x_1704_) == 2)
{
lean_object* v_val_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v_val_1705_ = lean_ctor_get(v___x_1704_, 1);
v___x_1706_ = lean_string_length(v_val_1705_);
v___x_1707_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1707_, 0, v___x_1706_);
return v___x_1707_;
}
else
{
lean_object* v___x_1708_; 
v___x_1708_ = lean_box(0);
return v___x_1708_;
}
}
}
else
{
lean_object* v___x_1709_; 
v___x_1709_ = lean_box(0);
return v___x_1709_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength___boxed(lean_object* v_x_1710_){
_start:
{
lean_object* v_res_1711_; 
v_res_1711_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength(v_x_1710_);
lean_dec(v_x_1710_);
return v_res_1711_;
}
}
lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0(uint32_t v_ch_1712_, lean_object* v_x_1713_, lean_object* v_x_1714_){
_start:
{
lean_object* v_zero_1715_; uint8_t v_isZero_1716_; 
v_zero_1715_ = lean_unsigned_to_nat(0u);
v_isZero_1716_ = lean_nat_dec_eq(v_x_1713_, v_zero_1715_);
if (v_isZero_1716_ == 1)
{
lean_dec(v_x_1713_);
return v_x_1714_;
}
else
{
lean_object* v_one_1717_; lean_object* v_n_1718_; lean_object* v___x_1719_; 
v_one_1717_ = lean_unsigned_to_nat(1u);
v_n_1718_ = lean_nat_sub(v_x_1713_, v_one_1717_);
lean_dec(v_x_1713_);
v___x_1719_ = lean_string_push(v_x_1714_, v_ch_1712_);
v_x_1713_ = v_n_1718_;
v_x_1714_ = v___x_1719_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_ch_1712_ = stack[0].m_num;
lean_object* v_x_1713_ = stack[1].m_obj;
lean_object* v_x_1714_ = stack[2].m_obj;
lean_object* v_res_1721_;
v_res_1721_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0(v_ch_1712_, v_x_1713_, v_x_1714_);
stack->m_obj
 = v_res_1721_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0___boxed(lean_object* v_ch_1722_, lean_object* v_x_1723_, lean_object* v_x_1724_){
_start:
{
uint32_t v_ch_boxed_1725_; lean_object* v_res_1726_; 
v_ch_boxed_1725_ = lean_unbox_uint32(v_ch_1722_);
lean_dec(v_ch_1722_);
v_res_1726_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0(v_ch_boxed_1725_, v_x_1723_, v_x_1724_);
return v_res_1726_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths(lean_object* v_delim_1729_, uint32_t v_ch_1730_, lean_object* v_contents_1731_, lean_object* v_c_1732_, lean_object* v_s_1733_){
_start:
{
lean_object* v_fn_1734_; lean_object* v_s_1735_; lean_object* v_stxStack_1736_; lean_object* v_errorMsg_1737_; lean_object* v___x_1738_; uint8_t v___x_1739_; 
v_fn_1734_ = lean_ctor_get(v_delim_1729_, 1);
lean_inc_ref_n(v_fn_1734_, 2);
lean_dec_ref(v_delim_1729_);
lean_inc_ref(v_c_1732_);
v_s_1735_ = lean_apply_2(v_fn_1734_, v_c_1732_, v_s_1733_);
v_stxStack_1736_ = lean_ctor_get(v_s_1735_, 0);
lean_inc_ref(v_stxStack_1736_);
v_errorMsg_1737_ = lean_ctor_get(v_s_1735_, 4);
lean_inc(v_errorMsg_1737_);
v___x_1738_ = lean_box(0);
v___x_1739_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_1737_, v___x_1738_);
lean_dec(v_errorMsg_1737_);
if (v___x_1739_ == 0)
{
lean_dec_ref(v_stxStack_1736_);
lean_dec_ref(v_fn_1734_);
lean_dec_ref(v_c_1732_);
lean_dec_ref(v_contents_1731_);
return v_s_1735_;
}
else
{
lean_object* v_fn_1740_; lean_object* v_s_1741_; lean_object* v_pos_1742_; lean_object* v_errorMsg_1743_; uint8_t v___x_1744_; 
v_fn_1740_ = lean_ctor_get(v_contents_1731_, 1);
lean_inc_ref(v_fn_1740_);
lean_dec_ref(v_contents_1731_);
lean_inc_ref(v_c_1732_);
v_s_1741_ = lean_apply_2(v_fn_1740_, v_c_1732_, v_s_1735_);
v_pos_1742_ = lean_ctor_get(v_s_1741_, 2);
lean_inc(v_pos_1742_);
v_errorMsg_1743_ = lean_ctor_get(v_s_1741_, 4);
lean_inc(v_errorMsg_1743_);
v___x_1744_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_1743_, v___x_1738_);
lean_dec(v_errorMsg_1743_);
if (v___x_1744_ == 0)
{
lean_dec(v_pos_1742_);
lean_dec_ref(v_stxStack_1736_);
lean_dec_ref(v_fn_1734_);
lean_dec_ref(v_c_1732_);
return v_s_1741_;
}
else
{
lean_object* v_s_1745_; lean_object* v_stxStack_1746_; lean_object* v_errorMsg_1747_; uint8_t v___x_1748_; 
v_s_1745_ = lean_apply_2(v_fn_1734_, v_c_1732_, v_s_1741_);
v_stxStack_1746_ = lean_ctor_get(v_s_1745_, 0);
lean_inc_ref(v_stxStack_1746_);
v_errorMsg_1747_ = lean_ctor_get(v_s_1745_, 4);
lean_inc(v_errorMsg_1747_);
v___x_1748_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_1747_, v___x_1738_);
lean_dec(v_errorMsg_1747_);
if (v___x_1748_ == 0)
{
lean_dec_ref(v_stxStack_1746_);
lean_dec(v_pos_1742_);
lean_dec_ref(v_stxStack_1736_);
return v_s_1745_;
}
else
{
lean_object* v_opener_1749_; lean_object* v___x_1750_; 
v_opener_1749_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1736_);
lean_dec_ref(v_stxStack_1736_);
v___x_1750_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength(v_opener_1749_);
lean_dec(v_opener_1749_);
if (lean_obj_tag(v___x_1750_) == 1)
{
lean_object* v_val_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v_val_1751_ = lean_ctor_get(v___x_1750_, 0);
lean_inc(v_val_1751_);
lean_dec_ref_known(v___x_1750_, 1);
v___x_1752_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1746_);
lean_dec_ref(v_stxStack_1746_);
v___x_1753_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength(v___x_1752_);
lean_dec(v___x_1752_);
if (lean_obj_tag(v___x_1753_) == 1)
{
lean_object* v_val_1754_; uint8_t v___x_1755_; 
v_val_1754_ = lean_ctor_get(v___x_1753_, 0);
lean_inc(v_val_1754_);
lean_dec_ref_known(v___x_1753_, 1);
v___x_1755_ = lean_nat_dec_eq(v_val_1751_, v_val_1754_);
lean_dec(v_val_1754_);
if (v___x_1755_ == 0)
{
lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; 
v___x_1756_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0));
v___x_1757_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_1758_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0(v_ch_1730_, v_val_1751_, v___x_1757_);
v___x_1759_ = lean_string_append(v___x_1756_, v___x_1758_);
v___x_1760_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___closed__0));
v___x_1761_ = lean_string_append(v___x_1759_, v___x_1760_);
v___x_1762_ = lean_string_append(v___x_1761_, v___x_1758_);
lean_dec_ref(v___x_1758_);
v___x_1763_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___closed__1));
v___x_1764_ = lean_string_append(v___x_1762_, v___x_1763_);
v___x_1765_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_1745_, v___x_1764_, v_pos_1742_, v___x_1738_);
return v___x_1765_;
}
else
{
lean_dec(v_val_1751_);
lean_dec(v_pos_1742_);
return v_s_1745_;
}
}
else
{
lean_dec(v___x_1753_);
lean_dec(v_val_1751_);
lean_dec(v_pos_1742_);
return v_s_1745_;
}
}
else
{
lean_dec(v___x_1750_);
lean_dec_ref(v_stxStack_1746_);
lean_dec(v_pos_1742_);
return v_s_1745_;
}
}
}
}
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_0interp(lean_interpreter_value* stack)
{
lean_object* v_delim_1729_ = stack[0].m_obj;
uint32_t v_ch_1730_ = stack[1].m_num;
lean_object* v_contents_1731_ = stack[2].m_obj;
lean_object* v_c_1732_ = stack[3].m_obj;
lean_object* v_s_1733_ = stack[4].m_obj;
lean_object* v_res_1766_;
v_res_1766_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths(v_delim_1729_, v_ch_1730_, v_contents_1731_, v_c_1732_, v_s_1733_);
stack->m_obj
 = v_res_1766_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___boxed(lean_object* v_delim_1767_, lean_object* v_ch_1768_, lean_object* v_contents_1769_, lean_object* v_c_1770_, lean_object* v_s_1771_){
_start:
{
uint32_t v_ch_boxed_1772_; lean_object* v_res_1773_; 
v_ch_boxed_1772_ = lean_unbox_uint32(v_ch_1768_);
lean_dec(v_ch_1768_);
v_res_1773_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths(v_delim_1767_, v_ch_boxed_1772_, v_contents_1769_, v_c_1770_, v_s_1771_);
return v_res_1773_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_1782_; lean_object* v___x_1783_; 
v___x_1782_ = 96;
v___x_1783_ = lean_box_uint32(v___x_1782_);
return v___x_1783_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; 
v___x_1784_ = ((lean_object*)(l_Lean_Doc_Parser_versoCode));
v___x_1785_ = ((lean_object*)(l_Lean_Doc_Parser_codeDelimiter));
v___x_1786_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__3___boxed__const__1;
v___x_1787_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___boxed), 5, 3);
lean_closure_set(v___x_1787_, 0, v___x_1785_);
lean_closure_set(v___x_1787_, 1, v___x_1786_);
lean_closure_set(v___x_1787_, 2, v___x_1784_);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2(lean_object* v___f_1788_, lean_object* v___f_1789_, lean_object* v_c_1790_, lean_object* v_s_1791_){
_start:
{
lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; uint8_t v___x_1798_; lean_object* v___x_1799_; lean_object* v_fn_1800_; lean_object* v___x_1801_; 
v___x_1792_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__0));
v___x_1793_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2));
v___x_1794_ = lean_box(1);
v___x_1795_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1795_, 0, v___f_1788_);
lean_ctor_set(v___x_1795_, 1, v___f_1789_);
lean_ctor_set(v___x_1795_, 2, v___x_1794_);
v___x_1796_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__3);
v___x_1797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1797_, 0, v___x_1795_);
lean_ctor_set(v___x_1797_, 1, v___x_1796_);
v___x_1798_ = 0;
v___x_1799_ = l_Lean_Parser_nodeWithAntiquot(v___x_1792_, v___x_1793_, v___x_1797_, v___x_1798_);
v_fn_1800_ = lean_ctor_get(v___x_1799_, 1);
lean_inc_ref(v_fn_1800_);
lean_dec_ref(v___x_1799_);
v___x_1801_ = lean_apply_2(v_fn_1800_, v_c_1790_, v_s_1791_);
return v___x_1801_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2(void){
_start:
{
uint32_t v___x_1816_; lean_object* v___x_1817_; 
v___x_1816_ = 10;
v___x_1817_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_1816_);
return v___x_1817_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__3(void){
_start:
{
uint8_t v___x_1818_; lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; 
v___x_1818_ = 0;
v___x_1819_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2);
v___x_1820_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1));
v___x_1821_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0));
v___x_1822_ = l_Lean_Parser_nodeWithAntiquot(v___x_1821_, v___x_1820_, v___x_1819_, v___x_1818_);
return v___x_1822_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot(lean_object* v_a_1823_, lean_object* v_a_1824_){
_start:
{
lean_object* v___x_1825_; lean_object* v_fn_1826_; lean_object* v___x_1827_; 
v___x_1825_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__3);
v_fn_1826_ = lean_ctor_get(v___x_1825_, 1);
lean_inc_ref(v_fn_1826_);
v___x_1827_ = lean_apply_2(v_fn_1826_, v_a_1823_, v_a_1824_);
return v___x_1827_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3(void){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1836_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__2));
v___x_1837_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_1836_);
return v___x_1837_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4(void){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1838_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__4));
v___x_1839_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_1838_);
return v___x_1839_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = ((lean_object*)(l_Lean_Doc_Parser_linkTarget));
v___x_1841_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4);
v___x_1842_ = l_Lean_Parser_andthen(v___x_1841_, v___x_1840_);
return v___x_1842_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5);
v___x_1844_ = ((lean_object*)(l_Lean_Doc_Parser_versoImageAlt));
v___x_1845_ = l_Lean_Parser_andthen(v___x_1844_, v___x_1843_);
return v___x_1845_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; 
v___x_1846_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6);
v___x_1847_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3);
v___x_1848_ = l_Lean_Parser_andthen(v___x_1847_, v___x_1846_);
return v___x_1848_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__8(void){
_start:
{
uint8_t v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1849_ = 0;
v___x_1850_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7);
v___x_1851_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1));
v___x_1852_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0));
v___x_1853_ = l_Lean_Parser_nodeWithAntiquot(v___x_1852_, v___x_1851_, v___x_1850_, v___x_1849_);
return v___x_1853_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot(lean_object* v_a_1854_, lean_object* v_a_1855_){
_start:
{
lean_object* v___x_1856_; lean_object* v_fn_1857_; lean_object* v___x_1858_; 
v___x_1856_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__8, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__8_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__8);
v_fn_1857_ = lean_ctor_get(v___x_1856_, 1);
lean_inc_ref(v_fn_1857_);
v___x_1858_ = lean_apply_2(v_fn_1857_, v_a_1854_, v_a_1855_);
return v___x_1858_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__2));
v___x_1868_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_1867_);
return v___x_1868_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4(void){
_start:
{
lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; 
v___x_1869_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4);
v___x_1870_ = ((lean_object*)(l_Lean_Doc_Parser_versoRef));
v___x_1871_ = l_Lean_Parser_andthen(v___x_1870_, v___x_1869_);
return v___x_1871_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__5(void){
_start:
{
lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; 
v___x_1872_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4);
v___x_1873_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3);
v___x_1874_ = l_Lean_Parser_andthen(v___x_1873_, v___x_1872_);
return v___x_1874_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__6(void){
_start:
{
uint8_t v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1875_ = 0;
v___x_1876_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__5);
v___x_1877_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1));
v___x_1878_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0));
v___x_1879_ = l_Lean_Parser_nodeWithAntiquot(v___x_1878_, v___x_1877_, v___x_1876_, v___x_1875_);
return v___x_1879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot(lean_object* v_a_1880_, lean_object* v_a_1881_){
_start:
{
lean_object* v___x_1882_; lean_object* v_fn_1883_; lean_object* v___x_1884_; 
v___x_1882_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__6);
v_fn_1883_ = lean_ctor_get(v___x_1882_, 1);
lean_inc_ref(v_fn_1883_);
v___x_1884_ = lean_apply_2(v_fn_1883_, v_a_1880_, v_a_1881_);
return v___x_1884_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode));
v___x_1893_ = ((lean_object*)(l_Lean_Doc_Parser_inlineMathMarker));
v___x_1894_ = l_Lean_Parser_andthen(v___x_1893_, v___x_1892_);
return v___x_1894_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__3(void){
_start:
{
uint8_t v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; lean_object* v___x_1899_; 
v___x_1895_ = 0;
v___x_1896_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2);
v___x_1897_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1));
v___x_1898_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0));
v___x_1899_ = l_Lean_Parser_nodeWithAntiquot(v___x_1898_, v___x_1897_, v___x_1896_, v___x_1895_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot(lean_object* v_a_1900_, lean_object* v_a_1901_){
_start:
{
lean_object* v___x_1902_; lean_object* v_fn_1903_; lean_object* v___x_1904_; 
v___x_1902_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__3);
v_fn_1903_ = lean_ctor_get(v___x_1902_, 1);
lean_inc_ref(v_fn_1903_);
v___x_1904_ = lean_apply_2(v_fn_1903_, v_a_1900_, v_a_1901_);
return v___x_1904_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2(void){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1912_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode));
v___x_1913_ = ((lean_object*)(l_Lean_Doc_Parser_displayMathMarker));
v___x_1914_ = l_Lean_Parser_andthen(v___x_1913_, v___x_1912_);
return v___x_1914_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__3(void){
_start:
{
uint8_t v___x_1915_; lean_object* v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1915_ = 0;
v___x_1916_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2);
v___x_1917_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1));
v___x_1918_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0));
v___x_1919_ = l_Lean_Parser_nodeWithAntiquot(v___x_1918_, v___x_1917_, v___x_1916_, v___x_1915_);
return v___x_1919_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot(lean_object* v_a_1920_, lean_object* v_a_1921_){
_start:
{
lean_object* v___x_1922_; lean_object* v_fn_1923_; lean_object* v___x_1924_; 
v___x_1922_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__3);
v_fn_1923_ = lean_ctor_get(v___x_1922_, 1);
lean_inc_ref(v_fn_1923_);
v___x_1924_ = lean_apply_2(v_fn_1923_, v_a_1920_, v_a_1921_);
return v___x_1924_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0(void){
_start:
{
lean_object* v___x_1925_; lean_object* v___x_1926_; lean_object* v___x_1927_; 
v___x_1925_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot), 2, 0);
v___x_1926_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_1927_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1927_, 0, v___x_1926_);
lean_ctor_set(v___x_1927_, 1, v___x_1925_);
return v___x_1927_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0);
v___x_1929_ = l_Lean_Parser_atomic(v___x_1928_);
return v___x_1929_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2(void){
_start:
{
lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1930_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot), 2, 0);
v___x_1931_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_1932_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1932_, 0, v___x_1931_);
lean_ctor_set(v___x_1932_, 1, v___x_1930_);
return v___x_1932_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1933_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2);
v___x_1934_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1);
v___x_1935_ = l_Lean_Parser_orelse(v___x_1934_, v___x_1933_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot(lean_object* v_a_1936_, lean_object* v_a_1937_){
_start:
{
lean_object* v___x_1938_; lean_object* v_fn_1939_; lean_object* v___x_1940_; 
v___x_1938_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3);
v_fn_1939_ = lean_ctor_get(v___x_1938_, 1);
lean_inc_ref(v_fn_1939_);
v___x_1940_ = lean_apply_2(v_fn_1939_, v_a_1936_, v_a_1937_);
return v___x_1940_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__2(void){
_start:
{
uint8_t v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; 
v___x_1948_ = 0;
v___x_1949_ = ((lean_object*)(l_Lean_Doc_Parser_versoText));
v___x_1950_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1));
v___x_1951_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0));
v___x_1952_ = l_Lean_Parser_nodeWithAntiquot(v___x_1951_, v___x_1950_, v___x_1949_, v___x_1948_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot(lean_object* v_a_1953_, lean_object* v_a_1954_){
_start:
{
lean_object* v___x_1955_; lean_object* v_fn_1956_; lean_object* v___x_1957_; 
v___x_1955_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__2);
v_fn_1956_ = lean_ctor_get(v___x_1955_, 1);
lean_inc_ref(v_fn_1956_);
v___x_1957_ = lean_apply_2(v_fn_1956_, v_a_1953_, v_a_1954_);
return v___x_1957_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0(lean_object* v___y_1958_){
_start:
{
lean_inc(v___y_1958_);
return v___y_1958_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0___boxed(lean_object* v___y_1959_){
_start:
{
lean_object* v_res_1960_; 
v_res_1960_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0(v___y_1959_);
lean_dec(v___y_1959_);
return v_res_1960_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1(lean_object* v___y_1961_){
_start:
{
lean_inc_ref(v___y_1961_);
return v___y_1961_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1___boxed(lean_object* v___y_1962_){
_start:
{
lean_object* v_res_1963_; 
v_res_1963_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1(v___y_1962_);
lean_dec_ref(v___y_1962_);
return v_res_1963_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___boxed__const__1(void){
_start:
{
uint32_t v___x_1977_; lean_object* v___x_1978_; 
v___x_1977_ = 42;
v___x_1978_ = lean_box_uint32(v___x_1977_);
return v___x_1978_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0(void){
_start:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; 
v___x_1979_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot), 2, 0);
v___x_1980_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_1981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1981_, 0, v___x_1980_);
lean_ctor_set(v___x_1981_, 1, v___x_1979_);
return v___x_1981_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___boxed__const__1(void){
_start:
{
uint32_t v___x_1989_; lean_object* v___x_1990_; 
v___x_1989_ = 95;
v___x_1990_ = lean_box_uint32(v___x_1989_);
return v___x_1990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot(lean_object* v_a_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; lean_object* v___x_2003_; uint8_t v___x_2004_; lean_object* v___x_2005_; lean_object* v_fn_2006_; lean_object* v___x_2007_; 
v___x_1993_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0));
v___x_1994_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__1));
v___x_1995_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_1996_ = ((lean_object*)(l_Lean_Doc_Parser_emphDelimiter));
v___x_1997_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot), 2, 0);
v___x_1998_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1998_, 0, v___x_1995_);
lean_ctor_set(v___x_1998_, 1, v___x_1997_);
v___x_1999_ = l_Lean_Parser_atomic(v___x_1998_);
v___x_2000_ = l_Lean_Parser_many(v___x_1999_);
v___x_2001_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___boxed__const__1;
v___x_2002_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___boxed), 5, 3);
lean_closure_set(v___x_2002_, 0, v___x_1996_);
lean_closure_set(v___x_2002_, 1, v___x_2001_);
lean_closure_set(v___x_2002_, 2, v___x_2000_);
v___x_2003_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2003_, 0, v___x_1995_);
lean_ctor_set(v___x_2003_, 1, v___x_2002_);
v___x_2004_ = 0;
v___x_2005_ = l_Lean_Parser_nodeWithAntiquot(v___x_1993_, v___x_1994_, v___x_2003_, v___x_2004_);
v_fn_2006_ = lean_ctor_get(v___x_2005_, 1);
lean_inc_ref(v_fn_2006_);
lean_dec_ref(v___x_2005_);
v___x_2007_ = lean_apply_2(v_fn_2006_, v_a_1991_, v_a_1992_);
return v___x_2007_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1(void){
_start:
{
lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; 
v___x_2008_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot), 2, 0);
v___x_2009_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2010_, 0, v___x_2009_);
lean_ctor_set(v___x_2010_, 1, v___x_2008_);
return v___x_2010_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2(void){
_start:
{
lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; 
v___x_2011_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot), 2, 0);
v___x_2012_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2013_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2013_, 0, v___x_2012_);
lean_ctor_set(v___x_2013_, 1, v___x_2011_);
return v___x_2013_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__2(void){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; 
v___x_2021_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__2));
v___x_2022_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot(lean_object* v_a_2023_, lean_object* v_a_2024_){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2035_; uint8_t v___x_2036_; lean_object* v___x_2037_; lean_object* v_fn_2038_; lean_object* v___x_2039_; 
v___x_2025_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0));
v___x_2026_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1));
v___x_2027_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__2);
v___x_2028_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2029_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot), 2, 0);
v___x_2030_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2030_, 0, v___x_2028_);
lean_ctor_set(v___x_2030_, 1, v___x_2029_);
v___x_2031_ = l_Lean_Parser_atomic(v___x_2030_);
v___x_2032_ = l_Lean_Parser_many(v___x_2031_);
v___x_2033_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5);
v___x_2034_ = l_Lean_Parser_andthen(v___x_2032_, v___x_2033_);
v___x_2035_ = l_Lean_Parser_andthen(v___x_2027_, v___x_2034_);
v___x_2036_ = 0;
v___x_2037_ = l_Lean_Parser_nodeWithAntiquot(v___x_2025_, v___x_2026_, v___x_2035_, v___x_2036_);
v_fn_2038_ = lean_ctor_get(v___x_2037_, 1);
lean_inc_ref(v_fn_2038_);
lean_dec_ref(v___x_2037_);
v___x_2039_ = lean_apply_2(v_fn_2038_, v_a_2023_, v_a_2024_);
return v___x_2039_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3(void){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2040_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot), 2, 0);
v___x_2041_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
lean_ctor_set(v___x_2042_, 1, v___x_2040_);
return v___x_2042_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6(void){
_start:
{
uint8_t v___x_2049_; lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2049_ = 1;
v___x_2050_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5));
v___x_2051_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4));
v___x_2052_ = l_Lean_Parser_mkAntiquot(v___x_2051_, v___x_2050_, v___x_2049_, v___x_2049_);
return v___x_2052_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__7(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2053_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot), 2, 0);
v___x_2054_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2055_, 0, v___x_2054_);
lean_ctor_set(v___x_2055_, 1, v___x_2053_);
return v___x_2055_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3(void){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; 
v___x_2064_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2));
v___x_2065_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2064_);
return v___x_2065_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4(void){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2066_ = ((lean_object*)(l_Lean_Doc_Parser_arg));
v___x_2067_ = l_Lean_Parser_many(v___x_2066_);
return v___x_2067_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6(void){
_start:
{
lean_object* v___x_2069_; lean_object* v___x_2070_; 
v___x_2069_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__5));
v___x_2070_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2069_);
return v___x_2070_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__9(void){
_start:
{
lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; 
v___x_2074_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__2);
v___x_2075_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8));
v___x_2076_ = l_Lean_Parser_node(v___x_2075_, v___x_2074_);
return v___x_2076_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__10(void){
_start:
{
lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v___x_2077_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4);
v___x_2078_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8));
v___x_2079_ = l_Lean_Parser_node(v___x_2078_, v___x_2077_);
return v___x_2079_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__11(void){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; 
v___x_2080_ = l_Lean_Parser_skip;
v___x_2081_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8));
v___x_2082_ = l_Lean_Parser_node(v___x_2081_, v___x_2080_);
return v___x_2082_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot(lean_object* v_a_2083_, lean_object* v_a_2084_){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; uint8_t v___x_2109_; lean_object* v___x_2110_; lean_object* v_fn_2111_; lean_object* v___x_2112_; 
v___x_2085_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0));
v___x_2086_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1));
v___x_2087_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3);
v___x_2088_ = l_Lean_Parser_ident;
v___x_2089_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4);
v___x_2090_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6);
v___x_2091_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__9, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__9_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__9);
v___x_2092_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2093_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot), 2, 0);
v___x_2094_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2094_, 0, v___x_2092_);
lean_ctor_set(v___x_2094_, 1, v___x_2093_);
v___x_2095_ = l_Lean_Parser_atomic(v___x_2094_);
lean_inc_ref(v___x_2095_);
v___x_2096_ = l_Lean_Parser_many(v___x_2095_);
v___x_2097_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__10, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__10_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__10);
v___x_2098_ = l_Lean_Parser_andthen(v___x_2096_, v___x_2097_);
v___x_2099_ = l_Lean_Parser_andthen(v___x_2091_, v___x_2098_);
v___x_2100_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__11, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__11_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__11);
v___x_2101_ = l_Lean_Parser_many1(v___x_2095_);
v___x_2102_ = l_Lean_Parser_andthen(v___x_2101_, v___x_2100_);
v___x_2103_ = l_Lean_Parser_andthen(v___x_2100_, v___x_2102_);
v___x_2104_ = l_Lean_Parser_orelse(v___x_2099_, v___x_2103_);
v___x_2105_ = l_Lean_Parser_andthen(v___x_2090_, v___x_2104_);
v___x_2106_ = l_Lean_Parser_andthen(v___x_2089_, v___x_2105_);
v___x_2107_ = l_Lean_Parser_andthen(v___x_2088_, v___x_2106_);
v___x_2108_ = l_Lean_Parser_andthen(v___x_2087_, v___x_2107_);
v___x_2109_ = 0;
v___x_2110_ = l_Lean_Parser_nodeWithAntiquot(v___x_2085_, v___x_2086_, v___x_2108_, v___x_2109_);
v_fn_2111_ = lean_ctor_get(v___x_2110_, 1);
lean_inc_ref(v_fn_2111_);
lean_dec_ref(v___x_2110_);
v___x_2112_ = lean_apply_2(v_fn_2111_, v_a_2083_, v_a_2084_);
return v___x_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot(lean_object* v_c_2113_, lean_object* v_s_2114_){
_start:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2123_; lean_object* v___x_2124_; lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v_fn_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; lean_object* v___x_2138_; lean_object* v___x_2139_; lean_object* v_alts_2140_; lean_object* v_fn_2141_; uint8_t v___x_2142_; lean_object* v___x_2143_; 
v___x_2115_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2116_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0);
v___x_2117_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot), 2, 0);
v___x_2118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2118_, 0, v___x_2115_);
lean_ctor_set(v___x_2118_, 1, v___x_2117_);
v___x_2119_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot), 2, 0);
v___x_2120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2120_, 0, v___x_2115_);
lean_ctor_set(v___x_2120_, 1, v___x_2119_);
v___x_2121_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1);
v___x_2122_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2);
v___x_2123_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot), 2, 0);
v___x_2124_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2124_, 0, v___x_2115_);
lean_ctor_set(v___x_2124_, 1, v___x_2123_);
v___x_2125_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3);
v___x_2126_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6);
v_fn_2127_ = lean_ctor_get(v___x_2126_, 1);
v___x_2128_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__7, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__7_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__7);
v___x_2129_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode));
v___x_2130_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot), 2, 0);
v___x_2131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2131_, 0, v___x_2115_);
lean_ctor_set(v___x_2131_, 1, v___x_2130_);
v___x_2132_ = l_Lean_Parser_orelse(v___x_2128_, v___x_2131_);
v___x_2133_ = l_Lean_Parser_orelse(v___x_2125_, v___x_2132_);
v___x_2134_ = l_Lean_Parser_orelse(v___x_2124_, v___x_2133_);
v___x_2135_ = l_Lean_Parser_orelse(v___x_2122_, v___x_2134_);
v___x_2136_ = l_Lean_Parser_orelse(v___x_2121_, v___x_2135_);
v___x_2137_ = l_Lean_Parser_orelse(v___x_2129_, v___x_2136_);
v___x_2138_ = l_Lean_Parser_orelse(v___x_2120_, v___x_2137_);
v___x_2139_ = l_Lean_Parser_orelse(v___x_2118_, v___x_2138_);
v_alts_2140_ = l_Lean_Parser_orelse(v___x_2116_, v___x_2139_);
v_fn_2141_ = lean_ctor_get(v_alts_2140_, 1);
lean_inc_ref(v_fn_2141_);
lean_dec_ref(v_alts_2140_);
v___x_2142_ = 0;
lean_inc_ref(v_fn_2127_);
v___x_2143_ = l_Lean_Parser_withAntiquotFn(v_fn_2127_, v_fn_2141_, v___x_2142_, v_c_2113_, v_s_2114_);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot(lean_object* v_a_2144_, lean_object* v_a_2145_){
_start:
{
lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; uint8_t v___x_2157_; lean_object* v___x_2158_; lean_object* v_fn_2159_; lean_object* v___x_2160_; 
v___x_2146_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2));
v___x_2147_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_2148_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2149_ = ((lean_object*)(l_Lean_Doc_Parser_boldDelimiter));
v___x_2150_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot), 2, 0);
v___x_2151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2151_, 0, v___x_2148_);
lean_ctor_set(v___x_2151_, 1, v___x_2150_);
v___x_2152_ = l_Lean_Parser_atomic(v___x_2151_);
v___x_2153_ = l_Lean_Parser_many(v___x_2152_);
v___x_2154_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___boxed__const__1;
v___x_2155_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___boxed), 5, 3);
lean_closure_set(v___x_2155_, 0, v___x_2149_);
lean_closure_set(v___x_2155_, 1, v___x_2154_);
lean_closure_set(v___x_2155_, 2, v___x_2153_);
v___x_2156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2156_, 0, v___x_2148_);
lean_ctor_set(v___x_2156_, 1, v___x_2155_);
v___x_2157_ = 0;
v___x_2158_ = l_Lean_Parser_nodeWithAntiquot(v___x_2146_, v___x_2147_, v___x_2156_, v___x_2157_);
v_fn_2159_ = lean_ctor_get(v___x_2158_, 1);
lean_inc_ref(v_fn_2159_);
lean_dec_ref(v___x_2158_);
v___x_2160_ = lean_apply_2(v_fn_2159_, v_a_2144_, v_a_2145_);
return v___x_2160_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_text___closed__0(void){
_start:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2161_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot), 2, 0);
v___x_2162_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2163_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2163_, 0, v___x_2162_);
lean_ctor_set(v___x_2163_, 1, v___x_2161_);
return v___x_2163_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_text(void){
_start:
{
lean_object* v___x_2164_; 
v___x_2164_ = lean_obj_once(&l_Lean_Doc_Parser_Inline_text___closed__0, &l_Lean_Doc_Parser_Inline_text___closed__0_once, _init_l_Lean_Doc_Parser_Inline_text___closed__0);
return v___x_2164_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1(){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; 
v___x_2172_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__1));
v___x_2173_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1___closed__0));
v___x_2174_ = l_Lean_addBuiltinDocString(v___x_2172_, v___x_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2175_;
v_res_2175_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1();
stack->m_obj
 = v_res_2175_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1___boxed(lean_object* v_a_2176_){
_start:
{
lean_object* v_res_2177_; 
v_res_2177_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1();
return v_res_2177_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1(){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2185_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_2186_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1___closed__0));
v___x_2187_ = l_Lean_addBuiltinDocString(v___x_2185_, v___x_2186_);
return v___x_2187_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2188_;
v_res_2188_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1();
stack->m_obj
 = v_res_2188_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1___boxed(lean_object* v_a_2189_){
_start:
{
lean_object* v_res_2190_; 
v_res_2190_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1();
return v_res_2190_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1(){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2194_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2));
v___x_2195_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1___closed__0));
v___x_2196_ = l_Lean_addBuiltinDocString(v___x_2194_, v___x_2195_);
return v___x_2196_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2197_;
v_res_2197_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1();
stack->m_obj
 = v_res_2197_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1___boxed(lean_object* v_a_2198_){
_start:
{
lean_object* v_res_2199_; 
v_res_2199_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1();
return v_res_2199_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_inline__math(void){
_start:
{
lean_object* v___x_2200_; 
v___x_2200_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2);
return v___x_2200_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1(){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1));
v___x_2204_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1___closed__0));
v___x_2205_ = l_Lean_addBuiltinDocString(v___x_2203_, v___x_2204_);
return v___x_2205_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2206_;
v_res_2206_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1();
stack->m_obj
 = v_res_2206_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1___boxed(lean_object* v_a_2207_){
_start:
{
lean_object* v_res_2208_; 
v_res_2208_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1();
return v_res_2208_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_display__math(void){
_start:
{
lean_object* v___x_2209_; 
v___x_2209_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0);
return v___x_2209_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1(){
_start:
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
v___x_2212_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1));
v___x_2213_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1___closed__0));
v___x_2214_ = l_Lean_addBuiltinDocString(v___x_2212_, v___x_2213_);
return v___x_2214_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2215_;
v_res_2215_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1();
stack->m_obj
 = v_res_2215_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1___boxed(lean_object* v_a_2216_){
_start:
{
lean_object* v_res_2217_; 
v_res_2217_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1();
return v_res_2217_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1(){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2225_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1));
v___x_2226_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1___closed__0));
v___x_2227_ = l_Lean_addBuiltinDocString(v___x_2225_, v___x_2226_);
return v___x_2227_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2228_;
v_res_2228_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1();
stack->m_obj
 = v_res_2228_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1___boxed(lean_object* v_a_2229_){
_start:
{
lean_object* v_res_2230_; 
v_res_2230_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1();
return v_res_2230_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_image___closed__0(void){
_start:
{
lean_object* v___x_2231_; lean_object* v___x_2232_; lean_object* v___x_2233_; 
v___x_2231_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot), 2, 0);
v___x_2232_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2233_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2233_, 0, v___x_2232_);
lean_ctor_set(v___x_2233_, 1, v___x_2231_);
return v___x_2233_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_image(void){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = lean_obj_once(&l_Lean_Doc_Parser_Inline_image___closed__0, &l_Lean_Doc_Parser_Inline_image___closed__0_once, _init_l_Lean_Doc_Parser_Inline_image___closed__0);
return v___x_2234_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1(){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2237_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1));
v___x_2238_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1___closed__0));
v___x_2239_ = l_Lean_addBuiltinDocString(v___x_2237_, v___x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2240_;
v_res_2240_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1();
stack->m_obj
 = v_res_2240_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1___boxed(lean_object* v_a_2241_){
_start:
{
lean_object* v_res_2242_; 
v_res_2242_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1();
return v_res_2242_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_footnote___closed__0(void){
_start:
{
lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; 
v___x_2243_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot), 2, 0);
v___x_2244_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
lean_ctor_set(v___x_2245_, 1, v___x_2243_);
return v___x_2245_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_footnote(void){
_start:
{
lean_object* v___x_2246_; 
v___x_2246_ = lean_obj_once(&l_Lean_Doc_Parser_Inline_footnote___closed__0, &l_Lean_Doc_Parser_Inline_footnote___closed__0_once, _init_l_Lean_Doc_Parser_Inline_footnote___closed__0);
return v___x_2246_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1(){
_start:
{
lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v___x_2249_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1));
v___x_2250_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1___closed__0));
v___x_2251_ = l_Lean_addBuiltinDocString(v___x_2249_, v___x_2250_);
return v___x_2251_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2252_;
v_res_2252_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1();
stack->m_obj
 = v_res_2252_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1___boxed(lean_object* v_a_2253_){
_start:
{
lean_object* v_res_2254_; 
v_res_2254_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1();
return v_res_2254_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_linebreak___closed__0(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2255_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot), 2, 0);
v___x_2256_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
lean_ctor_set(v___x_2257_, 1, v___x_2255_);
return v___x_2257_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_linebreak(void){
_start:
{
lean_object* v___x_2258_; 
v___x_2258_ = lean_obj_once(&l_Lean_Doc_Parser_Inline_linebreak___closed__0, &l_Lean_Doc_Parser_Inline_linebreak___closed__0_once, _init_l_Lean_Doc_Parser_Inline_linebreak___closed__0);
return v___x_2258_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1(){
_start:
{
lean_object* v___x_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2266_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1));
v___x_2267_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1___closed__0));
v___x_2268_ = l_Lean_addBuiltinDocString(v___x_2266_, v___x_2267_);
return v___x_2268_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2269_;
v_res_2269_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1();
stack->m_obj
 = v_res_2269_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1___boxed(lean_object* v_a_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1();
return v_res_2271_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3(void){
_start:
{
lean_object* v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = ((lean_object*)(l_Lean_Doc_Parser_inline___closed__1));
v___x_2286_ = l_Lean_Parser_atomic(v___x_2285_);
return v___x_2286_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4(void){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; 
v___x_2287_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3);
v___x_2288_ = l_Lean_Parser_many1(v___x_2287_);
return v___x_2288_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__5(void){
_start:
{
uint8_t v___x_2289_; lean_object* v___x_2290_; lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2289_ = 0;
v___x_2290_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4);
v___x_2291_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2));
v___x_2292_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0));
v___x_2293_ = l_Lean_Parser_nodeWithAntiquot(v___x_2292_, v___x_2291_, v___x_2290_, v___x_2289_);
return v___x_2293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot(lean_object* v_a_2294_, lean_object* v_a_2295_){
_start:
{
lean_object* v___x_2296_; lean_object* v_fn_2297_; lean_object* v___x_2298_; 
v___x_2296_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__5);
v_fn_2297_ = lean_ctor_get(v___x_2296_, 1);
lean_inc_ref(v_fn_2297_);
v___x_2298_ = lean_apply_2(v_fn_2297_, v_a_2294_, v_a_2295_);
return v___x_2298_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2(void){
_start:
{
lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2306_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6);
v___x_2307_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4);
v___x_2308_ = l_Lean_Parser_andthen(v___x_2307_, v___x_2306_);
return v___x_2308_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3(void){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; lean_object* v___x_2311_; 
v___x_2309_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2);
v___x_2310_ = l_Lean_Parser_ident;
v___x_2311_ = l_Lean_Parser_andthen(v___x_2310_, v___x_2309_);
return v___x_2311_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4(void){
_start:
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2312_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3);
v___x_2313_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3);
v___x_2314_ = l_Lean_Parser_andthen(v___x_2313_, v___x_2312_);
return v___x_2314_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__5(void){
_start:
{
uint8_t v___x_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2319_; 
v___x_2315_ = 0;
v___x_2316_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4);
v___x_2317_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1));
v___x_2318_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0));
v___x_2319_ = l_Lean_Parser_nodeWithAntiquot(v___x_2318_, v___x_2317_, v___x_2316_, v___x_2315_);
return v___x_2319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot(lean_object* v_a_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v___x_2322_; lean_object* v_fn_2323_; lean_object* v___x_2324_; 
v___x_2322_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__5);
v_fn_2323_ = lean_ctor_get(v___x_2322_, 1);
lean_inc_ref(v_fn_2323_);
v___x_2324_ = lean_apply_2(v_fn_2323_, v_a_2320_, v_a_2321_);
return v___x_2324_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2(void){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__0___closed__0));
v___x_2333_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2332_);
return v___x_2333_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3(void){
_start:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; 
v___x_2334_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2);
v___x_2335_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit));
v___x_2336_ = l_Lean_Parser_andthen(v___x_2335_, v___x_2334_);
return v___x_2336_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4(void){
_start:
{
lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___x_2339_; 
v___x_2337_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3);
v___x_2338_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2);
v___x_2339_ = l_Lean_Parser_andthen(v___x_2338_, v___x_2337_);
return v___x_2339_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__5(void){
_start:
{
uint8_t v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
v___x_2340_ = 0;
v___x_2341_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4);
v___x_2342_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1));
v___x_2343_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0));
v___x_2344_ = l_Lean_Parser_nodeWithAntiquot(v___x_2343_, v___x_2342_, v___x_2341_, v___x_2340_);
return v___x_2344_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot(lean_object* v_a_2345_, lean_object* v_a_2346_){
_start:
{
lean_object* v___x_2347_; lean_object* v_fn_2348_; lean_object* v___x_2349_; 
v___x_2347_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__5);
v_fn_2348_ = lean_ctor_get(v___x_2347_, 1);
lean_inc_ref(v_fn_2348_);
v___x_2349_ = lean_apply_2(v_fn_2348_, v_a_2345_, v_a_2346_);
return v___x_2349_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3(void){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2358_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__2));
v___x_2359_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2358_);
return v___x_2359_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2360_ = ((lean_object*)(l_Lean_Doc_Parser_versoLinkRefUrl));
v___x_2361_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3);
v___x_2362_ = l_Lean_Parser_andthen(v___x_2361_, v___x_2360_);
return v___x_2362_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5(void){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2363_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4);
v___x_2364_ = ((lean_object*)(l_Lean_Doc_Parser_versoRef));
v___x_2365_ = l_Lean_Parser_andthen(v___x_2364_, v___x_2363_);
return v___x_2365_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__6(void){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2366_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5);
v___x_2367_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__2);
v___x_2368_ = l_Lean_Parser_andthen(v___x_2367_, v___x_2366_);
return v___x_2368_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__7(void){
_start:
{
uint8_t v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2369_ = 0;
v___x_2370_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__6);
v___x_2371_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1));
v___x_2372_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0));
v___x_2373_ = l_Lean_Parser_nodeWithAntiquot(v___x_2372_, v___x_2371_, v___x_2370_, v___x_2369_);
return v___x_2373_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot(lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v___x_2376_; lean_object* v_fn_2377_; lean_object* v___x_2378_; 
v___x_2376_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__7, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__7_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__7);
v_fn_2377_ = lean_ctor_get(v___x_2376_, 1);
lean_inc_ref(v_fn_2377_);
v___x_2378_ = lean_apply_2(v_fn_2377_, v_a_2374_, v_a_2375_);
return v___x_2378_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2(void){
_start:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2386_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3);
v___x_2387_ = l_Lean_Parser_many(v___x_2386_);
return v___x_2387_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3(void){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; 
v___x_2388_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2);
v___x_2389_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3);
v___x_2390_ = l_Lean_Parser_andthen(v___x_2389_, v___x_2388_);
return v___x_2390_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4(void){
_start:
{
lean_object* v___x_2391_; lean_object* v___x_2392_; lean_object* v___x_2393_; 
v___x_2391_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3);
v___x_2392_ = ((lean_object*)(l_Lean_Doc_Parser_versoRef));
v___x_2393_ = l_Lean_Parser_andthen(v___x_2392_, v___x_2391_);
return v___x_2393_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5(void){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; 
v___x_2394_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4);
v___x_2395_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3);
v___x_2396_ = l_Lean_Parser_andthen(v___x_2395_, v___x_2394_);
return v___x_2396_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__6(void){
_start:
{
uint8_t v___x_2397_; lean_object* v___x_2398_; lean_object* v___x_2399_; lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2397_ = 0;
v___x_2398_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5);
v___x_2399_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1));
v___x_2400_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0));
v___x_2401_ = l_Lean_Parser_nodeWithAntiquot(v___x_2400_, v___x_2399_, v___x_2398_, v___x_2397_);
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot(lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v___x_2404_; lean_object* v_fn_2405_; lean_object* v___x_2406_; 
v___x_2404_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__6);
v_fn_2405_ = lean_ctor_get(v___x_2404_, 1);
lean_inc_ref(v_fn_2405_);
v___x_2406_ = lean_apply_2(v_fn_2405_, v_a_2402_, v_a_2403_);
return v___x_2406_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2(void){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2414_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4);
v___x_2415_ = ((lean_object*)(l_Lean_Doc_Parser_headerMarker));
v___x_2416_ = l_Lean_Parser_andthen(v___x_2415_, v___x_2414_);
return v___x_2416_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__3(void){
_start:
{
uint8_t v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2417_ = 0;
v___x_2418_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2);
v___x_2419_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1));
v___x_2420_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0));
v___x_2421_ = l_Lean_Parser_nodeWithAntiquot(v___x_2420_, v___x_2419_, v___x_2418_, v___x_2417_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot(lean_object* v_a_2422_, lean_object* v_a_2423_){
_start:
{
lean_object* v___x_2424_; lean_object* v_fn_2425_; lean_object* v___x_2426_; 
v___x_2424_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__3);
v_fn_2425_ = lean_ctor_get(v___x_2424_, 1);
lean_inc_ref(v_fn_2425_);
v___x_2426_ = lean_apply_2(v_fn_2425_, v_a_2422_, v_a_2423_);
return v___x_2426_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2(void){
_start:
{
lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; 
v___x_2434_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4);
v___x_2435_ = l_Lean_Parser_ident;
v___x_2436_ = l_Lean_Parser_andthen(v___x_2435_, v___x_2434_);
return v___x_2436_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3(void){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; 
v___x_2437_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2);
v___x_2438_ = l_Lean_Parser_optional(v___x_2437_);
return v___x_2438_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4(void){
_start:
{
lean_object* v___x_2439_; lean_object* v___x_2440_; lean_object* v___x_2441_; 
v___x_2439_ = ((lean_object*)(l_Lean_Doc_Parser_codeBlockFence));
v___x_2440_ = ((lean_object*)(l_Lean_Doc_Parser_versoCodeBlock));
v___x_2441_ = l_Lean_Parser_andthen(v___x_2440_, v___x_2439_);
return v___x_2441_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5(void){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2442_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4);
v___x_2443_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3);
v___x_2444_ = l_Lean_Parser_andthen(v___x_2443_, v___x_2442_);
return v___x_2444_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6(void){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; 
v___x_2445_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5);
v___x_2446_ = ((lean_object*)(l_Lean_Doc_Parser_codeBlockFence));
v___x_2447_ = l_Lean_Parser_andthen(v___x_2446_, v___x_2445_);
return v___x_2447_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__7(void){
_start:
{
uint8_t v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2448_ = 0;
v___x_2449_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6);
v___x_2450_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1));
v___x_2451_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0));
v___x_2452_ = l_Lean_Parser_nodeWithAntiquot(v___x_2451_, v___x_2450_, v___x_2449_, v___x_2448_);
return v___x_2452_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot(lean_object* v_a_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v___x_2455_; lean_object* v_fn_2456_; lean_object* v___x_2457_; 
v___x_2455_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__7, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__7_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__7);
v_fn_2456_ = lean_ctor_get(v___x_2455_, 1);
lean_inc_ref(v_fn_2456_);
v___x_2457_ = lean_apply_2(v_fn_2456_, v_a_2453_, v_a_2454_);
return v___x_2457_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4(void){
_start:
{
lean_object* v___x_2477_; lean_object* v___x_2478_; 
v___x_2477_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__3));
v___x_2478_ = l_Lean_Parser_atomic(v___x_2477_);
return v___x_2478_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5(void){
_start:
{
lean_object* v___x_2479_; lean_object* v___x_2480_; 
v___x_2479_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4);
v___x_2480_ = l_Lean_Parser_many(v___x_2479_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot(lean_object* v_marker_2496_, lean_object* v_a_2497_, lean_object* v_a_2498_){
_start:
{
lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; uint8_t v___x_2507_; lean_object* v___x_2508_; lean_object* v_fn_2509_; lean_object* v___x_2510_; 
v___x_2499_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__0));
v___x_2500_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3));
v___x_2501_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2502_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot), 2, 0);
v___x_2503_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2503_, 0, v___x_2501_);
lean_ctor_set(v___x_2503_, 1, v___x_2502_);
v___x_2504_ = l_Lean_Parser_atomic(v___x_2503_);
v___x_2505_ = l_Lean_Parser_many(v___x_2504_);
v___x_2506_ = l_Lean_Parser_andthen(v_marker_2496_, v___x_2505_);
v___x_2507_ = 0;
v___x_2508_ = l_Lean_Parser_nodeWithAntiquot(v___x_2499_, v___x_2500_, v___x_2506_, v___x_2507_);
v_fn_2509_ = lean_ctor_get(v___x_2508_, 1);
lean_inc_ref(v_fn_2509_);
lean_dec_ref(v___x_2508_);
v___x_2510_ = lean_apply_2(v_fn_2509_, v_a_2497_, v_a_2498_);
return v___x_2510_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot(lean_object* v_a_2511_, lean_object* v_a_2512_){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; uint8_t v___x_2521_; lean_object* v___x_2522_; lean_object* v_fn_2523_; lean_object* v___x_2524_; 
v___x_2513_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0));
v___x_2514_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__1));
v___x_2515_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2516_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker));
v___x_2517_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot), 3, 1);
lean_closure_set(v___x_2517_, 0, v___x_2516_);
v___x_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2515_);
lean_ctor_set(v___x_2518_, 1, v___x_2517_);
v___x_2519_ = l_Lean_Parser_atomic(v___x_2518_);
v___x_2520_ = l_Lean_Parser_many1(v___x_2519_);
v___x_2521_ = 0;
v___x_2522_ = l_Lean_Parser_nodeWithAntiquot(v___x_2513_, v___x_2514_, v___x_2520_, v___x_2521_);
v_fn_2523_ = lean_ctor_get(v___x_2522_, 1);
lean_inc_ref(v_fn_2523_);
lean_dec_ref(v___x_2522_);
v___x_2524_ = lean_apply_2(v_fn_2523_, v_a_2511_, v_a_2512_);
return v___x_2524_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot(lean_object* v_a_2532_, lean_object* v_a_2533_){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; uint8_t v___x_2542_; lean_object* v___x_2543_; lean_object* v_fn_2544_; lean_object* v___x_2545_; 
v___x_2534_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0));
v___x_2535_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__1));
v___x_2536_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2537_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker));
v___x_2538_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot), 3, 1);
lean_closure_set(v___x_2538_, 0, v___x_2537_);
v___x_2539_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2539_, 0, v___x_2536_);
lean_ctor_set(v___x_2539_, 1, v___x_2538_);
v___x_2540_ = l_Lean_Parser_atomic(v___x_2539_);
v___x_2541_ = l_Lean_Parser_many1(v___x_2540_);
v___x_2542_ = 0;
v___x_2543_ = l_Lean_Parser_nodeWithAntiquot(v___x_2534_, v___x_2535_, v___x_2541_, v___x_2542_);
v_fn_2544_ = lean_ctor_get(v___x_2543_, 1);
lean_inc_ref(v_fn_2544_);
lean_dec_ref(v___x_2543_);
v___x_2545_ = lean_apply_2(v_fn_2544_, v_a_2532_, v_a_2533_);
return v___x_2545_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__3(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___x_2555_; 
v___x_2554_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__2));
v___x_2555_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2554_);
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot(lean_object* v_a_2556_, lean_object* v_a_2557_){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; lean_object* v___x_2568_; lean_object* v_fn_2569_; lean_object* v___x_2570_; 
v___x_2558_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0));
v___x_2559_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1));
v___x_2560_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__3);
v___x_2561_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2562_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot), 2, 0);
v___x_2563_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2563_, 0, v___x_2561_);
lean_ctor_set(v___x_2563_, 1, v___x_2562_);
v___x_2564_ = l_Lean_Parser_atomic(v___x_2563_);
v___x_2565_ = l_Lean_Parser_many(v___x_2564_);
v___x_2566_ = l_Lean_Parser_andthen(v___x_2560_, v___x_2565_);
v___x_2567_ = 0;
v___x_2568_ = l_Lean_Parser_nodeWithAntiquot(v___x_2558_, v___x_2559_, v___x_2566_, v___x_2567_);
v_fn_2569_ = lean_ctor_get(v___x_2568_, 1);
lean_inc_ref(v_fn_2569_);
lean_dec_ref(v___x_2568_);
v___x_2570_ = lean_apply_2(v_fn_2569_, v_a_2556_, v_a_2557_);
return v___x_2570_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0(void){
_start:
{
lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2571_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot), 2, 0);
v___x_2572_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2573_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2573_, 0, v___x_2572_);
lean_ctor_set(v___x_2573_, 1, v___x_2571_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot(lean_object* v_a_2581_, lean_object* v_a_2582_){
_start:
{
lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; uint8_t v___x_2597_; lean_object* v___x_2598_; lean_object* v_fn_2599_; lean_object* v___x_2600_; 
v___x_2583_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0));
v___x_2584_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__1));
v___x_2585_ = ((lean_object*)(l_Lean_Doc_Parser_directiveDelimiter));
v___x_2586_ = l_Lean_Parser_ident;
v___x_2587_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4);
v___x_2588_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2589_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot), 2, 0);
v___x_2590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2590_, 0, v___x_2588_);
lean_ctor_set(v___x_2590_, 1, v___x_2589_);
v___x_2591_ = l_Lean_Parser_atomic(v___x_2590_);
v___x_2592_ = l_Lean_Parser_many(v___x_2591_);
v___x_2593_ = l_Lean_Parser_andthen(v___x_2592_, v___x_2585_);
v___x_2594_ = l_Lean_Parser_andthen(v___x_2587_, v___x_2593_);
v___x_2595_ = l_Lean_Parser_andthen(v___x_2586_, v___x_2594_);
v___x_2596_ = l_Lean_Parser_andthen(v___x_2585_, v___x_2595_);
v___x_2597_ = 0;
v___x_2598_ = l_Lean_Parser_nodeWithAntiquot(v___x_2583_, v___x_2584_, v___x_2596_, v___x_2597_);
v_fn_2599_ = lean_ctor_get(v___x_2598_, 1);
lean_inc_ref(v_fn_2599_);
lean_dec_ref(v___x_2598_);
v___x_2600_ = lean_apply_2(v_fn_2599_, v_a_2581_, v_a_2582_);
return v___x_2600_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7(void){
_start:
{
uint8_t v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2607_ = 1;
v___x_2608_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6));
v___x_2609_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5));
v___x_2610_ = l_Lean_Parser_mkAntiquot(v___x_2609_, v___x_2608_, v___x_2607_, v___x_2607_);
return v___x_2610_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9(void){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot), 2, 0);
v___x_2612_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2613_, 0, v___x_2612_);
lean_ctor_set(v___x_2613_, 1, v___x_2611_);
return v___x_2613_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8(void){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2614_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot), 2, 0);
v___x_2615_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2616_, 0, v___x_2615_);
lean_ctor_set(v___x_2616_, 1, v___x_2614_);
return v___x_2616_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10(void){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2617_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9);
v___x_2618_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8);
v___x_2619_ = l_Lean_Parser_orelse(v___x_2618_, v___x_2617_);
return v___x_2619_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4(void){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2620_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot), 2, 0);
v___x_2621_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2621_);
lean_ctor_set(v___x_2622_, 1, v___x_2620_);
return v___x_2622_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11(void){
_start:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2623_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10);
v___x_2624_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4);
v___x_2625_ = l_Lean_Parser_orelse(v___x_2624_, v___x_2623_);
return v___x_2625_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3(void){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2626_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot), 2, 0);
v___x_2627_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2628_, 0, v___x_2627_);
lean_ctor_set(v___x_2628_, 1, v___x_2626_);
return v___x_2628_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12(void){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2629_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11);
v___x_2630_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3);
v___x_2631_ = l_Lean_Parser_orelse(v___x_2630_, v___x_2629_);
return v___x_2631_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2(void){
_start:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; 
v___x_2632_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot), 2, 0);
v___x_2633_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2634_, 0, v___x_2633_);
lean_ctor_set(v___x_2634_, 1, v___x_2632_);
return v___x_2634_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13(void){
_start:
{
lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2635_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12);
v___x_2636_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2);
v___x_2637_ = l_Lean_Parser_orelse(v___x_2636_, v___x_2635_);
return v___x_2637_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1(void){
_start:
{
lean_object* v___x_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2638_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot), 2, 0);
v___x_2639_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2639_);
lean_ctor_set(v___x_2640_, 1, v___x_2638_);
return v___x_2640_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__14(void){
_start:
{
lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2641_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13);
v___x_2642_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1);
v___x_2643_ = l_Lean_Parser_orelse(v___x_2642_, v___x_2641_);
return v___x_2643_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot(lean_object* v_c_2644_, lean_object* v_s_2645_){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v_fn_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v_alts_2666_; lean_object* v_fn_2667_; uint8_t v___x_2668_; lean_object* v___x_2669_; 
v___x_2646_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2647_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot), 2, 0);
v___x_2648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2646_);
lean_ctor_set(v___x_2648_, 1, v___x_2647_);
v___x_2649_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot), 2, 0);
v___x_2650_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2650_, 0, v___x_2646_);
lean_ctor_set(v___x_2650_, 1, v___x_2649_);
v___x_2651_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot), 2, 0);
v___x_2652_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2652_, 0, v___x_2646_);
lean_ctor_set(v___x_2652_, 1, v___x_2651_);
v___x_2653_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot), 2, 0);
v___x_2654_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2654_, 0, v___x_2646_);
lean_ctor_set(v___x_2654_, 1, v___x_2653_);
v___x_2655_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0);
v___x_2656_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot), 2, 0);
v___x_2657_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2657_, 0, v___x_2646_);
lean_ctor_set(v___x_2657_, 1, v___x_2656_);
v___x_2658_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7);
v_fn_2659_ = lean_ctor_get(v___x_2658_, 1);
v___x_2660_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__14, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__14_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__14);
v___x_2661_ = l_Lean_Parser_orelse(v___x_2657_, v___x_2660_);
v___x_2662_ = l_Lean_Parser_orelse(v___x_2655_, v___x_2661_);
v___x_2663_ = l_Lean_Parser_orelse(v___x_2654_, v___x_2662_);
v___x_2664_ = l_Lean_Parser_orelse(v___x_2652_, v___x_2663_);
v___x_2665_ = l_Lean_Parser_orelse(v___x_2650_, v___x_2664_);
v_alts_2666_ = l_Lean_Parser_orelse(v___x_2648_, v___x_2665_);
v_fn_2667_ = lean_ctor_get(v_alts_2666_, 1);
lean_inc_ref(v_fn_2667_);
lean_dec_ref(v_alts_2666_);
v___x_2668_ = 0;
lean_inc_ref(v_fn_2659_);
v___x_2669_ = l_Lean_Parser_withAntiquotFn(v_fn_2659_, v_fn_2667_, v___x_2668_, v_c_2644_, v_s_2645_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot(lean_object* v_a_2670_, lean_object* v_a_2671_){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; uint8_t v___x_2683_; lean_object* v___x_2684_; lean_object* v_fn_2685_; lean_object* v___x_2686_; 
v___x_2672_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__0));
v___x_2673_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2));
v___x_2674_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker));
v___x_2675_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2676_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5);
v___x_2677_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot), 2, 0);
v___x_2678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2678_, 0, v___x_2675_);
lean_ctor_set(v___x_2678_, 1, v___x_2677_);
v___x_2679_ = l_Lean_Parser_atomic(v___x_2678_);
v___x_2680_ = l_Lean_Parser_many(v___x_2679_);
v___x_2681_ = l_Lean_Parser_andthen(v___x_2676_, v___x_2680_);
v___x_2682_ = l_Lean_Parser_andthen(v___x_2674_, v___x_2681_);
v___x_2683_ = 0;
v___x_2684_ = l_Lean_Parser_nodeWithAntiquot(v___x_2672_, v___x_2673_, v___x_2682_, v___x_2683_);
v_fn_2685_ = lean_ctor_get(v___x_2684_, 1);
lean_inc_ref(v_fn_2685_);
lean_dec_ref(v___x_2684_);
v___x_2686_ = lean_apply_2(v_fn_2685_, v_a_2670_, v_a_2671_);
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot(lean_object* v_a_2687_, lean_object* v_a_2688_){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; uint8_t v___x_2696_; lean_object* v___x_2697_; lean_object* v_fn_2698_; lean_object* v___x_2699_; 
v___x_2689_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0));
v___x_2690_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__1));
v___x_2691_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2692_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot), 2, 0);
v___x_2693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2693_, 0, v___x_2691_);
lean_ctor_set(v___x_2693_, 1, v___x_2692_);
v___x_2694_ = l_Lean_Parser_atomic(v___x_2693_);
v___x_2695_ = l_Lean_Parser_many1(v___x_2694_);
v___x_2696_ = 0;
v___x_2697_ = l_Lean_Parser_nodeWithAntiquot(v___x_2689_, v___x_2690_, v___x_2695_, v___x_2696_);
v_fn_2698_ = lean_ctor_get(v___x_2697_, 1);
lean_inc_ref(v_fn_2698_);
lean_dec_ref(v___x_2697_);
v___x_2699_ = lean_apply_2(v_fn_2698_, v_a_2687_, v_a_2688_);
return v___x_2699_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1(){
_start:
{
lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; 
v___x_2708_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3));
v___x_2709_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1___closed__0));
v___x_2710_ = l_Lean_addBuiltinDocString(v___x_2708_, v___x_2709_);
return v___x_2710_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2711_;
v_res_2711_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1();
stack->m_obj
 = v_res_2711_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1___boxed(lean_object* v_a_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1();
return v_res_2713_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1(){
_start:
{
lean_object* v___x_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; 
v___x_2721_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2));
v___x_2722_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1___closed__0));
v___x_2723_ = l_Lean_addBuiltinDocString(v___x_2721_, v___x_2722_);
return v___x_2723_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2724_;
v_res_2724_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1();
stack->m_obj
 = v_res_2724_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1___boxed(lean_object* v_a_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1();
return v_res_2726_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_para___closed__0(void){
_start:
{
lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2727_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot), 2, 0);
v___x_2728_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2729_, 0, v___x_2728_);
lean_ctor_set(v___x_2729_, 1, v___x_2727_);
return v___x_2729_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_para(void){
_start:
{
lean_object* v___x_2730_; 
v___x_2730_ = lean_obj_once(&l_Lean_Doc_Parser_Block_para___closed__0, &l_Lean_Doc_Parser_Block_para___closed__0_once, _init_l_Lean_Doc_Parser_Block_para___closed__0);
return v___x_2730_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1(){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2733_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2));
v___x_2734_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1___closed__0));
v___x_2735_ = l_Lean_addBuiltinDocString(v___x_2733_, v___x_2734_);
return v___x_2735_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2736_;
v_res_2736_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1();
stack->m_obj
 = v_res_2736_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1___boxed(lean_object* v_a_2737_){
_start:
{
lean_object* v_res_2738_; 
v_res_2738_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1();
return v_res_2738_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1(){
_start:
{
lean_object* v___x_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; 
v___x_2746_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__1));
v___x_2747_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1___closed__0));
v___x_2748_ = l_Lean_addBuiltinDocString(v___x_2746_, v___x_2747_);
return v___x_2748_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2749_;
v_res_2749_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1();
stack->m_obj
 = v_res_2749_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1___boxed(lean_object* v_a_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1();
return v_res_2751_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1(){
_start:
{
lean_object* v___x_2759_; lean_object* v___x_2760_; lean_object* v___x_2761_; 
v___x_2759_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__1));
v___x_2760_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1___closed__0));
v___x_2761_ = l_Lean_addBuiltinDocString(v___x_2759_, v___x_2760_);
return v___x_2761_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2762_;
v_res_2762_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1();
stack->m_obj
 = v_res_2762_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1___boxed(lean_object* v_a_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1();
return v_res_2764_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1(){
_start:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2772_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__1));
v___x_2773_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1___closed__0));
v___x_2774_ = l_Lean_addBuiltinDocString(v___x_2772_, v___x_2773_);
return v___x_2774_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2775_;
v_res_2775_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1();
stack->m_obj
 = v_res_2775_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1___boxed(lean_object* v_a_2776_){
_start:
{
lean_object* v_res_2777_; 
v_res_2777_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1();
return v_res_2777_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1(){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; 
v___x_2785_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1));
v___x_2786_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1___closed__0));
v___x_2787_ = l_Lean_addBuiltinDocString(v___x_2785_, v___x_2786_);
return v___x_2787_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2788_;
v_res_2788_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1();
stack->m_obj
 = v_res_2788_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1___boxed(lean_object* v_a_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1();
return v_res_2790_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_codeblock___closed__0(void){
_start:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; 
v___x_2791_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot), 2, 0);
v___x_2792_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2793_, 0, v___x_2792_);
lean_ctor_set(v___x_2793_, 1, v___x_2791_);
return v___x_2793_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_codeblock(void){
_start:
{
lean_object* v___x_2794_; 
v___x_2794_ = lean_obj_once(&l_Lean_Doc_Parser_Block_codeblock___closed__0, &l_Lean_Doc_Parser_Block_codeblock___closed__0_once, _init_l_Lean_Doc_Parser_Block_codeblock___closed__0);
return v___x_2794_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1(){
_start:
{
lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; 
v___x_2797_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1));
v___x_2798_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1___closed__0));
v___x_2799_ = l_Lean_addBuiltinDocString(v___x_2797_, v___x_2798_);
return v___x_2799_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2800_;
v_res_2800_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1();
stack->m_obj
 = v_res_2800_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1___boxed(lean_object* v_a_2801_){
_start:
{
lean_object* v_res_2802_; 
v_res_2802_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1();
return v_res_2802_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1(){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2810_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__1));
v___x_2811_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1___closed__0));
v___x_2812_ = l_Lean_addBuiltinDocString(v___x_2810_, v___x_2811_);
return v___x_2812_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2813_;
v_res_2813_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1();
stack->m_obj
 = v_res_2813_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1___boxed(lean_object* v_a_2814_){
_start:
{
lean_object* v_res_2815_; 
v_res_2815_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1();
return v_res_2815_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_header___closed__0(void){
_start:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2816_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot), 2, 0);
v___x_2817_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2818_, 0, v___x_2817_);
lean_ctor_set(v___x_2818_, 1, v___x_2816_);
return v___x_2818_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_header(void){
_start:
{
lean_object* v___x_2819_; 
v___x_2819_ = lean_obj_once(&l_Lean_Doc_Parser_Block_header___closed__0, &l_Lean_Doc_Parser_Block_header___closed__0_once, _init_l_Lean_Doc_Parser_Block_header___closed__0);
return v___x_2819_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1(){
_start:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2822_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1));
v___x_2823_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1___closed__0));
v___x_2824_ = l_Lean_addBuiltinDocString(v___x_2822_, v___x_2823_);
return v___x_2824_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2825_;
v_res_2825_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1();
stack->m_obj
 = v_res_2825_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1___boxed(lean_object* v_a_2826_){
_start:
{
lean_object* v_res_2827_; 
v_res_2827_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1();
return v_res_2827_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_link__ref___closed__0(void){
_start:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2828_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot), 2, 0);
v___x_2829_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2830_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2830_, 0, v___x_2829_);
lean_ctor_set(v___x_2830_, 1, v___x_2828_);
return v___x_2830_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_link__ref(void){
_start:
{
lean_object* v___x_2831_; 
v___x_2831_ = lean_obj_once(&l_Lean_Doc_Parser_Block_link__ref___closed__0, &l_Lean_Doc_Parser_Block_link__ref___closed__0_once, _init_l_Lean_Doc_Parser_Block_link__ref___closed__0);
return v___x_2831_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1(){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; lean_object* v___x_2836_; 
v___x_2834_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1));
v___x_2835_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1___closed__0));
v___x_2836_ = l_Lean_addBuiltinDocString(v___x_2834_, v___x_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2837_;
v_res_2837_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1();
stack->m_obj
 = v_res_2837_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1___boxed(lean_object* v_a_2838_){
_start:
{
lean_object* v_res_2839_; 
v_res_2839_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1();
return v_res_2839_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_footnote__ref___closed__0(void){
_start:
{
lean_object* v___x_2840_; lean_object* v___x_2841_; lean_object* v___x_2842_; 
v___x_2840_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot), 2, 0);
v___x_2841_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2842_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2841_);
lean_ctor_set(v___x_2842_, 1, v___x_2840_);
return v___x_2842_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_footnote__ref(void){
_start:
{
lean_object* v___x_2843_; 
v___x_2843_ = lean_obj_once(&l_Lean_Doc_Parser_Block_footnote__ref___closed__0, &l_Lean_Doc_Parser_Block_footnote__ref___closed__0_once, _init_l_Lean_Doc_Parser_Block_footnote__ref___closed__0);
return v___x_2843_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1(){
_start:
{
lean_object* v___x_2846_; lean_object* v___x_2847_; lean_object* v___x_2848_; 
v___x_2846_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1));
v___x_2847_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1___closed__0));
v___x_2848_ = l_Lean_addBuiltinDocString(v___x_2846_, v___x_2847_);
return v___x_2848_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2849_;
v_res_2849_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1();
stack->m_obj
 = v_res_2849_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1___boxed(lean_object* v_a_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1();
return v_res_2851_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_metadata__block___closed__0(void){
_start:
{
lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2852_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot), 2, 0);
v___x_2853_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
lean_ctor_set(v___x_2854_, 1, v___x_2852_);
return v___x_2854_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_metadata__block(void){
_start:
{
lean_object* v___x_2855_; 
v___x_2855_ = lean_obj_once(&l_Lean_Doc_Parser_Block_metadata__block___closed__0, &l_Lean_Doc_Parser_Block_metadata__block___closed__0_once, _init_l_Lean_Doc_Parser_Block_metadata__block___closed__0);
return v___x_2855_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1(){
_start:
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2858_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1));
v___x_2859_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1___closed__0));
v___x_2860_ = l_Lean_addBuiltinDocString(v___x_2858_, v___x_2859_);
return v___x_2860_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2861_;
v_res_2861_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1();
stack->m_obj
 = v_res_2861_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1___boxed(lean_object* v_a_2862_){
_start:
{
lean_object* v_res_2863_; 
v_res_2863_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1();
return v_res_2863_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_command___closed__0(void){
_start:
{
lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2864_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot), 2, 0);
v___x_2865_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2865_);
lean_ctor_set(v___x_2866_, 1, v___x_2864_);
return v___x_2866_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_command(void){
_start:
{
lean_object* v___x_2867_; 
v___x_2867_ = lean_obj_once(&l_Lean_Doc_Parser_Block_command___closed__0, &l_Lean_Doc_Parser_Block_command___closed__0_once, _init_l_Lean_Doc_Parser_Block_command___closed__0);
return v___x_2867_;
}
}
lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1(){
_start:
{
lean_object* v___x_2870_; lean_object* v___x_2871_; lean_object* v___x_2872_; 
v___x_2870_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1));
v___x_2871_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1___closed__0));
v___x_2872_ = l_Lean_addBuiltinDocString(v___x_2870_, v___x_2871_);
return v___x_2872_;
}
}
LEAN_EXPORT void l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2873_;
v_res_2873_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1();
stack->m_obj
 = v_res_2873_;
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1___boxed(lean_object* v_a_2874_){
_start:
{
lean_object* v_res_2875_; 
v_res_2875_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1();
return v_res_2875_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_document___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2887_; lean_object* v___x_2888_; 
v___x_2887_ = ((lean_object*)(l_Lean_Doc_Parser_block));
v___x_2888_ = l_Lean_Parser_atomic(v___x_2887_);
return v___x_2888_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_document___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; 
v___x_2889_ = lean_obj_once(&l_Lean_Doc_Parser_document___lam__0___closed__2, &l_Lean_Doc_Parser_document___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_document___lam__0___closed__2);
v___x_2890_ = l_Lean_Parser_many(v___x_2889_);
return v___x_2890_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_document___lam__0___closed__4(void){
_start:
{
uint8_t v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; 
v___x_2891_ = 0;
v___x_2892_ = lean_obj_once(&l_Lean_Doc_Parser_document___lam__0___closed__3, &l_Lean_Doc_Parser_document___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_document___lam__0___closed__3);
v___x_2893_ = ((lean_object*)(l_Lean_Doc_Parser_document___lam__0___closed__1));
v___x_2894_ = ((lean_object*)(l_Lean_Doc_Parser_document___lam__0___closed__0));
v___x_2895_ = l_Lean_Parser_nodeWithAntiquot(v___x_2894_, v___x_2893_, v___x_2892_, v___x_2891_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document___lam__0(lean_object* v_c_2896_, lean_object* v_s_2897_){
_start:
{
lean_object* v___x_2898_; lean_object* v_fn_2899_; lean_object* v___x_2900_; 
v___x_2898_ = lean_obj_once(&l_Lean_Doc_Parser_document___lam__0___closed__4, &l_Lean_Doc_Parser_document___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_document___lam__0___closed__4);
v_fn_2899_ = lean_ctor_get(v___x_2898_, 1);
lean_inc_ref(v_fn_2899_);
v___x_2900_ = lean_apply_2(v_fn_2899_, v_c_2896_, v_s_2897_);
return v___x_2900_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0(size_t v_sz_2906_, size_t v_i_2907_, lean_object* v_bs_2908_){
_start:
{
uint8_t v___x_2909_; 
v___x_2909_ = lean_usize_dec_lt(v_i_2907_, v_sz_2906_);
if (v___x_2909_ == 0)
{
return v_bs_2908_;
}
else
{
lean_object* v_v_2910_; lean_object* v___x_2911_; lean_object* v_bs_x27_2912_; size_t v___x_2913_; size_t v___x_2914_; lean_object* v___x_2915_; 
v_v_2910_ = lean_array_uget(v_bs_2908_, v_i_2907_);
v___x_2911_ = lean_unsigned_to_nat(0u);
v_bs_x27_2912_ = lean_array_uset(v_bs_2908_, v_i_2907_, v___x_2911_);
v___x_2913_ = ((size_t)1ULL);
v___x_2914_ = lean_usize_add(v_i_2907_, v___x_2913_);
v___x_2915_ = lean_array_uset(v_bs_x27_2912_, v_i_2907_, v_v_2910_);
v_i_2907_ = v___x_2914_;
v_bs_2908_ = v___x_2915_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_2906_ = stack[0].m_num;
size_t v_i_2907_ = stack[1].m_num;
lean_object* v_bs_2908_ = stack[2].m_obj;
lean_object* v_res_2917_;
v_res_2917_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0(v_sz_2906_, v_i_2907_, v_bs_2908_);
stack->m_obj
 = v_res_2917_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0___boxed(lean_object* v_sz_2918_, lean_object* v_i_2919_, lean_object* v_bs_2920_){
_start:
{
size_t v_sz_boxed_2921_; size_t v_i_boxed_2922_; lean_object* v_res_2923_; 
v_sz_boxed_2921_ = lean_unbox_usize(v_sz_2918_);
lean_dec(v_sz_2918_);
v_i_boxed_2922_ = lean_unbox_usize(v_i_2919_);
lean_dec(v_i_2919_);
v_res_2923_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0(v_sz_boxed_2921_, v_i_boxed_2922_, v_bs_2920_);
return v_res_2923_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoBlocks(lean_object* v_doc_2924_){
_start:
{
lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; size_t v_sz_2928_; size_t v___x_2929_; lean_object* v___x_2930_; 
v___x_2925_ = lean_unsigned_to_nat(0u);
v___x_2926_ = l_Lean_Syntax_getArg(v_doc_2924_, v___x_2925_);
v___x_2927_ = l_Lean_Syntax_getArgs(v___x_2926_);
lean_dec(v___x_2926_);
v_sz_2928_ = lean_array_size(v___x_2927_);
v___x_2929_ = ((size_t)0ULL);
v___x_2930_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0(v_sz_2928_, v___x_2929_, v___x_2927_);
return v___x_2930_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoBlocks___boxed(lean_object* v_doc_2931_){
_start:
{
lean_object* v_res_2932_; 
v_res_2932_ = l_Lean_TSyntax_getVersoBlocks(v_doc_2931_);
lean_dec(v_doc_2931_);
return v_res_2932_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoDelimiter(lean_object* v_delim_2933_){
_start:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; 
v___x_2934_ = lean_unsigned_to_nat(0u);
v___x_2935_ = l_Lean_Syntax_getArg(v_delim_2933_, v___x_2934_);
v___x_2936_ = l_Lean_Syntax_getAtomVal(v___x_2935_);
lean_dec(v___x_2935_);
return v___x_2936_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoDelimiter___boxed(lean_object* v_delim_2937_){
_start:
{
lean_object* v_res_2938_; 
v_res_2938_ = l_Lean_TSyntax_getVersoDelimiter(v_delim_2937_);
lean_dec(v_delim_2937_);
return v_res_2938_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoDocument_view(lean_object* v_doc_2939_){
_start:
{
lean_object* v___x_2940_; 
v___x_2940_ = l_Lean_TSyntax_getVersoBlocks(v_doc_2939_);
return v___x_2940_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoDocument_view___boxed(lean_object* v_doc_2941_){
_start:
{
lean_object* v_res_2942_; 
v_res_2942_ = l_Lean_Doc_VersoDocument_view(v_doc_2941_);
lean_dec(v_doc_2941_);
return v_res_2942_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoDelimiter_view(lean_object* v_delim_2943_){
_start:
{
lean_object* v___x_2944_; 
v___x_2944_ = l_Lean_TSyntax_getVersoDelimiter(v_delim_2943_);
return v___x_2944_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoDelimiter_view___boxed(lean_object* v_delim_2945_){
_start:
{
lean_object* v_res_2946_; 
v_res_2946_ = l_Lean_Doc_VersoDelimiter_view(v_delim_2945_);
lean_dec(v_delim_2945_);
return v_res_2946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___lam__0(lean_object* v_s_2949_){
_start:
{
lean_inc(v_s_2949_);
return v_s_2949_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___lam__0___boxed(lean_object* v_s_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___lam__0(v_s_2950_);
lean_dec(v_s_2950_);
return v_res_2951_;
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
l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__3___boxed__const__1 = _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__3___boxed__const__1();
lean_mark_persistent(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__3___boxed__const__1);
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
