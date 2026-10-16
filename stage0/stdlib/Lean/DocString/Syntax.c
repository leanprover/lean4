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
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(lean_object* v_s_278_, uint8_t v___x_279_, lean_object* v_a_280_, uint8_t v_b_281_){
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg___boxed(lean_object* v_s_295_, lean_object* v___x_296_, lean_object* v_a_297_, lean_object* v_b_298_){
_start:
{
uint8_t v___x_973__boxed_299_; uint8_t v_b_boxed_300_; uint8_t v_res_301_; lean_object* v_r_302_; 
v___x_973__boxed_299_ = lean_unbox(v___x_296_);
v_b_boxed_300_ = lean_unbox(v_b_298_);
v_res_301_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(v_s_295_, v___x_973__boxed_299_, v_a_297_, v_b_boxed_300_);
lean_dec_ref(v_s_295_);
v_r_302_ = lean_box(v_res_301_);
return v_r_302_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0(uint8_t v___x_303_, lean_object* v_s_304_){
_start:
{
lean_object* v_searcher_305_; uint8_t v___x_306_; uint8_t v___x_307_; 
v_searcher_305_ = lean_unsigned_to_nat(0u);
v___x_306_ = 0;
v___x_307_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(v_s_304_, v___x_303_, v_searcher_305_, v___x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0___boxed(lean_object* v___x_308_, lean_object* v_s_309_){
_start:
{
uint8_t v___x_996__boxed_310_; uint8_t v_res_311_; lean_object* v_r_312_; 
v___x_996__boxed_310_ = lean_unbox(v___x_308_);
v_res_311_ = l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0(v___x_996__boxed_310_, v_s_309_);
lean_dec_ref(v_s_309_);
v_r_312_ = lean_box(v_res_311_);
return v_r_312_;
}
}
LEAN_EXPORT uint8_t l_Lean_Doc_versoCodeBoundarySpaces(lean_object* v_str_314_){
_start:
{
lean_object* v___x_315_; lean_object* v___x_316_; uint8_t v___x_317_; 
v___x_315_ = lean_string_utf8_byte_size(v_str_314_);
v___x_316_ = lean_unsigned_to_nat(1u);
v___x_317_ = lean_nat_dec_le(v___x_316_, v___x_315_);
if (v___x_317_ == 0)
{
lean_dec_ref(v_str_314_);
return v___x_317_;
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; uint8_t v___x_320_; 
v___x_318_ = ((lean_object*)(l_Lean_Doc_versoCodeBoundarySpaces___closed__0));
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = lean_string_memcmp(v_str_314_, v___x_318_, v___x_319_, v___x_319_, v___x_316_);
if (v___x_320_ == 0)
{
lean_dec_ref(v_str_314_);
return v___x_320_;
}
else
{
lean_object* v___x_321_; uint8_t v___x_322_; 
v___x_321_ = lean_nat_sub(v___x_315_, v___x_316_);
v___x_322_ = lean_string_memcmp(v_str_314_, v___x_318_, v___x_321_, v___x_319_, v___x_316_);
lean_dec(v___x_321_);
if (v___x_322_ == 0)
{
lean_dec_ref(v_str_314_);
return v___x_322_;
}
else
{
lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_323_, 0, v_str_314_);
lean_ctor_set(v___x_323_, 1, v___x_319_);
lean_ctor_set(v___x_323_, 2, v___x_315_);
v___x_324_ = l_String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0(v___x_322_, v___x_323_);
lean_dec_ref_known(v___x_323_, 3);
return v___x_324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_versoCodeBoundarySpaces___boxed(lean_object* v_str_325_){
_start:
{
uint8_t v_res_326_; lean_object* v_r_327_; 
v_res_326_ = l_Lean_Doc_versoCodeBoundarySpaces(v_str_325_);
v_r_327_ = lean_box(v_res_326_);
return v_r_327_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0(lean_object* v_s_328_, uint8_t v___x_329_, lean_object* v_inst_330_, lean_object* v_R_331_, lean_object* v_a_332_, uint8_t v_b_333_, lean_object* v_c_334_){
_start:
{
uint8_t v___x_335_; 
v___x_335_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___redArg(v_s_328_, v___x_329_, v_a_332_, v_b_333_);
return v___x_335_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0___boxed(lean_object* v_s_336_, lean_object* v___x_337_, lean_object* v_inst_338_, lean_object* v_R_339_, lean_object* v_a_340_, lean_object* v_b_341_, lean_object* v_c_342_){
_start:
{
uint8_t v___x_1026__boxed_343_; uint8_t v_b_boxed_344_; uint8_t v_res_345_; lean_object* v_r_346_; 
v___x_1026__boxed_343_ = lean_unbox(v___x_337_);
v_b_boxed_344_ = lean_unbox(v_b_341_);
v_res_345_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_contains___at___00Lean_Doc_versoCodeBoundarySpaces_spec__0_spec__0(v_s_336_, v___x_1026__boxed_343_, v_inst_338_, v_R_339_, v_a_340_, v_b_boxed_344_, v_c_342_);
lean_dec_ref(v_s_336_);
v_r_346_ = lean_box(v_res_345_);
return v_r_346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg(lean_object* v_str_347_, lean_object* v_a_348_){
_start:
{
lean_object* v_fst_349_; lean_object* v_snd_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_380_; 
v_fst_349_ = lean_ctor_get(v_a_348_, 0);
v_snd_350_ = lean_ctor_get(v_a_348_, 1);
v_isSharedCheck_380_ = !lean_is_exclusive(v_a_348_);
if (v_isSharedCheck_380_ == 0)
{
v___x_352_ = v_a_348_;
v_isShared_353_ = v_isSharedCheck_380_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_snd_350_);
lean_inc(v_fst_349_);
lean_dec(v_a_348_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_380_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; uint8_t v_decide_355_; 
v___x_354_ = lean_string_utf8_byte_size(v_str_347_);
v_decide_355_ = lean_nat_dec_eq(v_snd_350_, v___x_354_);
if (v_decide_355_ == 0)
{
uint32_t v___x_356_; lean_object* v___x_357_; uint32_t v___x_358_; uint8_t v___x_359_; 
v___x_356_ = lean_string_utf8_get_fast(v_str_347_, v_snd_350_);
v___x_357_ = lean_string_utf8_next_fast(v_str_347_, v_snd_350_);
lean_dec(v_snd_350_);
v___x_358_ = 92;
v___x_359_ = lean_uint32_dec_eq(v___x_356_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_360_ = lean_string_push(v_fst_349_, v___x_356_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 1, v___x_357_);
lean_ctor_set(v___x_352_, 0, v___x_360_);
v___x_362_ = v___x_352_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_360_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v___x_357_);
v___x_362_ = v_reuseFailAlloc_364_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
v_a_348_ = v___x_362_;
goto _start;
}
}
else
{
uint8_t v_decide_365_; 
v_decide_365_ = lean_nat_dec_eq(v___x_357_, v___x_354_);
if (v_decide_365_ == 0)
{
uint32_t v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_370_; 
v___x_366_ = lean_string_utf8_get_fast(v_str_347_, v___x_357_);
v___x_367_ = lean_string_push(v_fst_349_, v___x_366_);
v___x_368_ = lean_string_utf8_next_fast(v_str_347_, v___x_357_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 1, v___x_368_);
lean_ctor_set(v___x_352_, 0, v___x_367_);
v___x_370_ = v___x_352_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_372_; 
v_reuseFailAlloc_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_372_, 0, v___x_367_);
lean_ctor_set(v_reuseFailAlloc_372_, 1, v___x_368_);
v___x_370_ = v_reuseFailAlloc_372_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
v_a_348_ = v___x_370_;
goto _start;
}
}
else
{
lean_object* v___x_374_; 
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 1, v___x_357_);
v___x_374_ = v___x_352_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_376_; 
v_reuseFailAlloc_376_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_376_, 0, v_fst_349_);
lean_ctor_set(v_reuseFailAlloc_376_, 1, v___x_357_);
v___x_374_ = v_reuseFailAlloc_376_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
v_a_348_ = v___x_374_;
goto _start;
}
}
}
}
else
{
lean_object* v___x_378_; 
if (v_isShared_353_ == 0)
{
v___x_378_ = v___x_352_;
goto v_reusejp_377_;
}
else
{
lean_object* v_reuseFailAlloc_379_; 
v_reuseFailAlloc_379_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_379_, 0, v_fst_349_);
lean_ctor_set(v_reuseFailAlloc_379_, 1, v_snd_350_);
v___x_378_ = v_reuseFailAlloc_379_;
goto v_reusejp_377_;
}
v_reusejp_377_:
{
return v___x_378_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg___boxed(lean_object* v_str_381_, lean_object* v_a_382_){
_start:
{
lean_object* v_res_383_; 
v_res_383_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg(v_str_381_, v_a_382_);
lean_dec_ref(v_str_381_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(lean_object* v_str_388_){
_start:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v_fst_391_; 
v___x_389_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__1));
v___x_390_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg(v_str_388_, v___x_389_);
v_fst_391_ = lean_ctor_get(v___x_390_, 0);
lean_inc(v_fst_391_);
lean_dec_ref(v___x_390_);
return v_fst_391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___boxed(lean_object* v_str_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v_str_392_);
lean_dec_ref(v_str_392_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0(lean_object* v_str_394_, lean_object* v_inst_395_, lean_object* v_a_396_){
_start:
{
lean_object* v___x_397_; 
v___x_397_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___redArg(v_str_394_, v_a_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0___boxed(lean_object* v_str_398_, lean_object* v_inst_399_, lean_object* v_a_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso_spec__0(v_str_398_, v_inst_399_, v_a_400_);
lean_dec_ref(v_str_398_);
return v_res_401_;
}
}
LEAN_EXPORT uint8_t l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0(uint32_t v_a_402_, lean_object* v_x_403_){
_start:
{
if (lean_obj_tag(v_x_403_) == 0)
{
uint8_t v___x_404_; 
v___x_404_ = 0;
return v___x_404_;
}
else
{
lean_object* v_head_405_; lean_object* v_tail_406_; uint32_t v___x_407_; uint8_t v___x_408_; 
v_head_405_ = lean_ctor_get(v_x_403_, 0);
v_tail_406_ = lean_ctor_get(v_x_403_, 1);
v___x_407_ = lean_unbox_uint32(v_head_405_);
v___x_408_ = lean_uint32_dec_eq(v_a_402_, v___x_407_);
if (v___x_408_ == 0)
{
v_x_403_ = v_tail_406_;
goto _start;
}
else
{
return v___x_408_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0___boxed(lean_object* v_a_410_, lean_object* v_x_411_){
_start:
{
uint32_t v_a_boxed_412_; uint8_t v_res_413_; lean_object* v_r_414_; 
v_a_boxed_412_ = lean_unbox_uint32(v_a_410_);
lean_dec(v_a_410_);
v_res_413_ = l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0(v_a_boxed_412_, v_x_411_);
lean_dec(v_x_411_);
v_r_414_ = lean_box(v_res_413_);
return v_r_414_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg(lean_object* v_delimiters_415_, lean_object* v___x_416_, lean_object* v_value_417_, lean_object* v_a_418_, lean_object* v_b_419_){
_start:
{
uint8_t v_decide_420_; 
v_decide_420_ = lean_nat_dec_eq(v_a_418_, v___x_416_);
if (v_decide_420_ == 0)
{
uint32_t v___x_421_; lean_object* v___x_422_; uint32_t v___x_423_; uint8_t v___x_428_; 
v___x_421_ = lean_string_utf8_get_fast(v_value_417_, v_a_418_);
v___x_422_ = lean_string_utf8_next_fast(v_value_417_, v_a_418_);
lean_dec(v_a_418_);
v___x_423_ = 92;
v___x_428_ = lean_uint32_dec_eq(v___x_421_, v___x_423_);
if (v___x_428_ == 0)
{
uint8_t v___x_429_; 
v___x_429_ = l_List_elem___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__0(v___x_421_, v_delimiters_415_);
if (v___x_429_ == 0)
{
lean_object* v___x_430_; 
v___x_430_ = lean_string_push(v_b_419_, v___x_421_);
v_a_418_ = v___x_422_;
v_b_419_ = v___x_430_;
goto _start;
}
else
{
goto v___jp_424_;
}
}
else
{
goto v___jp_424_;
}
v___jp_424_:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = lean_string_push(v_b_419_, v___x_423_);
v___x_426_ = lean_string_push(v___x_425_, v___x_421_);
v_a_418_ = v___x_422_;
v_b_419_ = v___x_426_;
goto _start;
}
}
else
{
lean_dec(v_a_418_);
return v_b_419_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg___boxed(lean_object* v_delimiters_432_, lean_object* v___x_433_, lean_object* v_value_434_, lean_object* v_a_435_, lean_object* v_b_436_){
_start:
{
lean_object* v_res_437_; 
v_res_437_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg(v_delimiters_432_, v___x_433_, v_value_434_, v_a_435_, v_b_436_);
lean_dec_ref(v_value_434_);
lean_dec(v___x_433_);
lean_dec(v_delimiters_432_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited(lean_object* v_delimiters_438_, lean_object* v_value_439_){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; lean_object* v___x_443_; 
v___x_440_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_441_ = lean_string_utf8_byte_size(v_value_439_);
v___x_442_ = lean_unsigned_to_nat(0u);
v___x_443_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg(v_delimiters_438_, v___x_441_, v_value_439_, v___x_442_, v___x_440_);
return v___x_443_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited___boxed(lean_object* v_delimiters_444_, lean_object* v_value_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited(v_delimiters_444_, v_value_445_);
lean_dec_ref(v_value_445_);
lean_dec(v_delimiters_444_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1(lean_object* v_delimiters_447_, lean_object* v___x_448_, lean_object* v___x_449_, lean_object* v_value_450_, lean_object* v_inst_451_, lean_object* v_R_452_, lean_object* v_a_453_, lean_object* v_b_454_, lean_object* v_c_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___redArg(v_delimiters_447_, v___x_449_, v_value_450_, v_a_453_, v_b_454_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1___boxed(lean_object* v_delimiters_457_, lean_object* v___x_458_, lean_object* v___x_459_, lean_object* v_value_460_, lean_object* v_inst_461_, lean_object* v_R_462_, lean_object* v_a_463_, lean_object* v_b_464_, lean_object* v_c_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited_spec__1(v_delimiters_457_, v___x_458_, v___x_459_, v_value_460_, v_inst_461_, v_R_462_, v_a_463_, v_b_464_, v_c_465_);
lean_dec_ref(v_value_460_);
lean_dec(v___x_459_);
lean_dec_ref(v___x_458_);
lean_dec(v_delimiters_457_);
return v_res_466_;
}
}
static lean_object* _init_l_Lean_Doc_escapeVersoLinkUrl___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_467_; lean_object* v___x_468_; 
v___x_467_ = 41;
v___x_468_ = lean_box_uint32(v___x_467_);
return v___x_468_;
}
}
static lean_object* _init_l_Lean_Doc_escapeVersoLinkUrl___closed__0(void){
_start:
{
lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_469_ = lean_box(0);
v___x_470_ = l_Lean_Doc_escapeVersoLinkUrl___closed__0___boxed__const__1;
v___x_471_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v___x_469_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoLinkUrl(lean_object* v_value_472_){
_start:
{
lean_object* v___x_473_; lean_object* v___x_474_; 
v___x_473_ = lean_obj_once(&l_Lean_Doc_escapeVersoLinkUrl___closed__0, &l_Lean_Doc_escapeVersoLinkUrl___closed__0_once, _init_l_Lean_Doc_escapeVersoLinkUrl___closed__0);
v___x_474_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited(v___x_473_, v_value_472_);
return v___x_474_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoLinkUrl___boxed(lean_object* v_value_475_){
_start:
{
lean_object* v_res_476_; 
v_res_476_ = l_Lean_Doc_escapeVersoLinkUrl(v_value_475_);
lean_dec_ref(v_value_475_);
return v_res_476_;
}
}
static lean_object* _init_l_Lean_Doc_escapeVersoImageAlt___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_477_; lean_object* v___x_478_; 
v___x_477_ = 93;
v___x_478_ = lean_box_uint32(v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l_Lean_Doc_escapeVersoImageAlt___closed__0(void){
_start:
{
lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_479_ = lean_box(0);
v___x_480_ = l_Lean_Doc_escapeVersoImageAlt___closed__0___boxed__const__1;
v___x_481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_481_, 0, v___x_480_);
lean_ctor_set(v___x_481_, 1, v___x_479_);
return v___x_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoImageAlt(lean_object* v_value_482_){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = lean_obj_once(&l_Lean_Doc_escapeVersoImageAlt___closed__0, &l_Lean_Doc_escapeVersoImageAlt___closed__0_once, _init_l_Lean_Doc_escapeVersoImageAlt___closed__0);
v___x_484_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_escapeVersoDelimited(v___x_483_, v_value_482_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_escapeVersoImageAlt___boxed(lean_object* v_value_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Lean_Doc_escapeVersoImageAlt(v_value_485_);
lean_dec_ref(v_value_485_);
return v_res_486_;
}
}
static lean_object* _init_l_Lean_TSyntax_getVersoText___closed__0(void){
_start:
{
lean_object* v___x_487_; lean_object* v___x_488_; 
v___x_487_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_488_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoText(lean_object* v_s_489_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = ((lean_object*)(l_Lean_Doc_versoTextKind));
v___x_491_ = l_Lean_Syntax_isLit_x3f(v___x_490_, v_s_489_);
if (lean_obj_tag(v___x_491_) == 0)
{
lean_object* v___x_492_; 
v___x_492_ = lean_obj_once(&l_Lean_TSyntax_getVersoText___closed__0, &l_Lean_TSyntax_getVersoText___closed__0_once, _init_l_Lean_TSyntax_getVersoText___closed__0);
return v___x_492_;
}
else
{
lean_object* v_val_493_; lean_object* v___x_494_; 
v_val_493_ = lean_ctor_get(v___x_491_, 0);
lean_inc(v_val_493_);
lean_dec_ref_known(v___x_491_, 1);
v___x_494_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v_val_493_);
lean_dec(v_val_493_);
return v___x_494_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoText___boxed(lean_object* v_s_495_){
_start:
{
lean_object* v_res_496_; 
v_res_496_ = l_Lean_TSyntax_getVersoText(v_s_495_);
lean_dec(v_s_495_);
return v_res_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoTextSource(lean_object* v_s_497_){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; 
v___x_498_ = ((lean_object*)(l_Lean_Doc_versoTextKind));
v___x_499_ = l_Lean_Syntax_isLit_x3f(v___x_498_, v_s_497_);
if (lean_obj_tag(v___x_499_) == 0)
{
lean_object* v___x_500_; 
v___x_500_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
return v___x_500_;
}
else
{
lean_object* v_val_501_; 
v_val_501_ = lean_ctor_get(v___x_499_, 0);
lean_inc(v_val_501_);
lean_dec_ref_known(v___x_499_, 1);
return v_val_501_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoTextSource___boxed(lean_object* v_s_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_Lean_TSyntax_getVersoTextSource(v_s_502_);
lean_dec(v_s_502_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoRefName(lean_object* v_s_504_){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = ((lean_object*)(l_Lean_Doc_versoRefKind));
v___x_506_ = l_Lean_Syntax_isLit_x3f(v___x_505_, v_s_504_);
if (lean_obj_tag(v___x_506_) == 0)
{
lean_object* v___x_507_; 
v___x_507_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
return v___x_507_;
}
else
{
lean_object* v_val_508_; 
v_val_508_ = lean_ctor_get(v___x_506_, 0);
lean_inc(v_val_508_);
lean_dec_ref_known(v___x_506_, 1);
return v_val_508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoRefName___boxed(lean_object* v_s_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_TSyntax_getVersoRefName(v_s_509_);
lean_dec(v_s_509_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkUrl(lean_object* v_s_511_){
_start:
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = ((lean_object*)(l_Lean_Doc_versoLinkUrlKind));
v___x_513_ = l_Lean_Syntax_isLit_x3f(v___x_512_, v_s_511_);
if (lean_obj_tag(v___x_513_) == 0)
{
lean_object* v___x_514_; 
v___x_514_ = lean_obj_once(&l_Lean_TSyntax_getVersoText___closed__0, &l_Lean_TSyntax_getVersoText___closed__0_once, _init_l_Lean_TSyntax_getVersoText___closed__0);
return v___x_514_;
}
else
{
lean_object* v_val_515_; lean_object* v___x_516_; 
v_val_515_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_val_515_);
lean_dec_ref_known(v___x_513_, 1);
v___x_516_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v_val_515_);
lean_dec(v_val_515_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkUrl___boxed(lean_object* v_s_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_TSyntax_getVersoLinkUrl(v_s_517_);
lean_dec(v_s_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkRefUrl(lean_object* v_s_519_){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = ((lean_object*)(l_Lean_Doc_versoLinkRefUrlKind));
v___x_521_ = l_Lean_Syntax_isLit_x3f(v___x_520_, v_s_519_);
if (lean_obj_tag(v___x_521_) == 0)
{
lean_object* v___x_522_; 
v___x_522_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
return v___x_522_;
}
else
{
lean_object* v_val_523_; 
v_val_523_ = lean_ctor_get(v___x_521_, 0);
lean_inc(v_val_523_);
lean_dec_ref_known(v___x_521_, 1);
return v_val_523_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoLinkRefUrl___boxed(lean_object* v_s_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Lean_TSyntax_getVersoLinkRefUrl(v_s_524_);
lean_dec(v_s_524_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoImageAlt(lean_object* v_s_526_){
_start:
{
lean_object* v___x_527_; lean_object* v___x_528_; 
v___x_527_ = ((lean_object*)(l_Lean_Doc_versoImageAltKind));
v___x_528_ = l_Lean_Syntax_isLit_x3f(v___x_527_, v_s_526_);
if (lean_obj_tag(v___x_528_) == 0)
{
lean_object* v___x_529_; 
v___x_529_ = lean_obj_once(&l_Lean_TSyntax_getVersoText___closed__0, &l_Lean_TSyntax_getVersoText___closed__0_once, _init_l_Lean_TSyntax_getVersoText___closed__0);
return v___x_529_;
}
else
{
lean_object* v_val_530_; lean_object* v___x_531_; 
v_val_530_ = lean_ctor_get(v___x_528_, 0);
lean_inc(v_val_530_);
lean_dec_ref_known(v___x_528_, 1);
v___x_531_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso(v_val_530_);
lean_dec(v_val_530_);
return v___x_531_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoImageAlt___boxed(lean_object* v_s_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l_Lean_TSyntax_getVersoImageAlt(v_s_532_);
lean_dec(v_s_532_);
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLine(lean_object* v_s_534_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = ((lean_object*)(l_Lean_Doc_versoCodeLineKind));
v___x_536_ = l_Lean_Syntax_isLit_x3f(v___x_535_, v_s_534_);
if (lean_obj_tag(v___x_536_) == 0)
{
lean_object* v___x_537_; 
v___x_537_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
return v___x_537_;
}
else
{
lean_object* v_val_538_; 
v_val_538_ = lean_ctor_get(v___x_536_, 0);
lean_inc(v_val_538_);
lean_dec_ref_known(v___x_536_, 1);
return v_val_538_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLine___boxed(lean_object* v_s_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Lean_TSyntax_getVersoCodeLine(v_s_539_);
lean_dec(v_s_539_);
return v_res_540_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLines(lean_object* v_s_541_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_542_ = lean_unsigned_to_nat(0u);
v___x_543_ = l_Lean_Syntax_getArg(v_s_541_, v___x_542_);
v___x_544_ = l_Lean_Syntax_getArgs(v___x_543_);
lean_dec(v___x_543_);
return v___x_544_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeLines___boxed(lean_object* v_s_545_){
_start:
{
lean_object* v_res_546_; 
v_res_546_ = l_Lean_TSyntax_getVersoCodeLines(v_s_545_);
lean_dec(v_s_545_);
return v_res_546_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0(lean_object* v_as_547_, size_t v_sz_548_, size_t v_i_549_, lean_object* v_b_550_){
_start:
{
uint8_t v___x_551_; 
v___x_551_ = lean_usize_dec_lt(v_i_549_, v_sz_548_);
if (v___x_551_ == 0)
{
return v_b_550_;
}
else
{
lean_object* v_a_552_; lean_object* v___x_553_; lean_object* v___x_554_; size_t v___x_555_; size_t v___x_556_; 
v_a_552_ = lean_array_uget_borrowed(v_as_547_, v_i_549_);
v___x_553_ = l_Lean_TSyntax_getVersoCodeLine(v_a_552_);
v___x_554_ = lean_string_append(v_b_550_, v___x_553_);
lean_dec_ref(v___x_553_);
v___x_555_ = ((size_t)1ULL);
v___x_556_ = lean_usize_add(v_i_549_, v___x_555_);
v_i_549_ = v___x_556_;
v_b_550_ = v___x_554_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0___boxed(lean_object* v_as_558_, lean_object* v_sz_559_, lean_object* v_i_560_, lean_object* v_b_561_){
_start:
{
size_t v_sz_boxed_562_; size_t v_i_boxed_563_; lean_object* v_res_564_; 
v_sz_boxed_562_ = lean_unbox_usize(v_sz_559_);
lean_dec(v_sz_559_);
v_i_boxed_563_ = lean_unbox_usize(v_i_560_);
lean_dec(v_i_560_);
v_res_564_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0(v_as_558_, v_sz_boxed_562_, v_i_boxed_563_, v_b_561_);
lean_dec_ref(v_as_558_);
return v_res_564_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCode(lean_object* v_s_565_){
_start:
{
lean_object* v_str_566_; lean_object* v___x_567_; size_t v_sz_568_; size_t v___x_569_; lean_object* v___x_570_; 
v_str_566_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_567_ = l_Lean_TSyntax_getVersoCodeLines(v_s_565_);
v_sz_568_ = lean_array_size(v___x_567_);
v___x_569_ = ((size_t)0ULL);
v___x_570_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0(v___x_567_, v_sz_568_, v___x_569_, v_str_566_);
lean_dec_ref(v___x_567_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCode___boxed(lean_object* v_s_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Lean_TSyntax_getVersoCode(v_s_571_);
lean_dec(v_s_571_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlockLines(lean_object* v_s_573_){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; 
v___x_574_ = lean_unsigned_to_nat(0u);
v___x_575_ = l_Lean_Syntax_getArg(v_s_573_, v___x_574_);
v___x_576_ = l_Lean_Syntax_getArgs(v___x_575_);
lean_dec(v___x_575_);
return v___x_576_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlockLines___boxed(lean_object* v_s_577_){
_start:
{
lean_object* v_res_578_; 
v_res_578_ = l_Lean_TSyntax_getVersoCodeBlockLines(v_s_577_);
lean_dec(v_s_577_);
return v_res_578_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlock(lean_object* v_s_579_){
_start:
{
lean_object* v_out_580_; lean_object* v___x_581_; size_t v_sz_582_; size_t v___x_583_; lean_object* v___x_584_; 
v_out_580_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_581_ = l_Lean_TSyntax_getVersoCodeBlockLines(v_s_579_);
v_sz_582_ = lean_array_size(v___x_581_);
v___x_583_ = ((size_t)0ULL);
v___x_584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_TSyntax_getVersoCode_spec__0(v___x_581_, v_sz_582_, v___x_583_, v_out_580_);
lean_dec_ref(v___x_581_);
return v___x_584_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoCodeBlock___boxed(lean_object* v_s_585_){
_start:
{
lean_object* v_res_586_; 
v_res_586_ = l_Lean_TSyntax_getVersoCodeBlock(v_s_585_);
lean_dec(v_s_585_);
return v_res_586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoText_view(lean_object* v_s_587_){
_start:
{
lean_object* v___x_588_; 
v___x_588_ = l_Lean_TSyntax_getVersoText(v_s_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoText_view___boxed(lean_object* v_s_589_){
_start:
{
lean_object* v_res_590_; 
v_res_590_ = l_Lean_Doc_VersoText_view(v_s_589_);
lean_dec(v_s_589_);
return v_res_590_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoRefName_view(lean_object* v_s_591_){
_start:
{
lean_object* v___x_592_; 
v___x_592_ = l_Lean_TSyntax_getVersoRefName(v_s_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoRefName_view___boxed(lean_object* v_s_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_Lean_Doc_VersoRefName_view(v_s_593_);
lean_dec(v_s_593_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoLinkUrl_view(lean_object* v_s_595_){
_start:
{
lean_object* v___x_596_; 
v___x_596_ = l_Lean_TSyntax_getVersoLinkUrl(v_s_595_);
return v___x_596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoLinkUrl_view___boxed(lean_object* v_s_597_){
_start:
{
lean_object* v_res_598_; 
v_res_598_ = l_Lean_Doc_VersoLinkUrl_view(v_s_597_);
lean_dec(v_s_597_);
return v_res_598_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoLinkRefUrl_view(lean_object* v_s_599_){
_start:
{
lean_object* v___x_600_; 
v___x_600_ = l_Lean_TSyntax_getVersoLinkRefUrl(v_s_599_);
return v___x_600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoLinkRefUrl_view___boxed(lean_object* v_s_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l_Lean_Doc_VersoLinkRefUrl_view(v_s_601_);
lean_dec(v_s_601_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoImageAlt_view(lean_object* v_s_603_){
_start:
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_TSyntax_getVersoImageAlt(v_s_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoImageAlt_view___boxed(lean_object* v_s_605_){
_start:
{
lean_object* v_res_606_; 
v_res_606_ = l_Lean_Doc_VersoImageAlt_view(v_s_605_);
lean_dec(v_s_605_);
return v_res_606_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCodeLine_view(lean_object* v_s_607_){
_start:
{
lean_object* v___x_608_; 
v___x_608_ = l_Lean_TSyntax_getVersoCodeLine(v_s_607_);
return v___x_608_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCodeLine_view___boxed(lean_object* v_s_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l_Lean_Doc_VersoCodeLine_view(v_s_609_);
lean_dec(v_s_609_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCode_view(lean_object* v_s_611_){
_start:
{
lean_object* v___x_612_; 
v___x_612_ = l_Lean_TSyntax_getVersoCode(v_s_611_);
return v___x_612_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCode_view___boxed(lean_object* v_s_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_Lean_Doc_VersoCode_view(v_s_613_);
lean_dec(v_s_613_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCodeBlock_view(lean_object* v_s_615_){
_start:
{
lean_object* v___x_616_; 
v___x_616_ = l_Lean_TSyntax_getVersoCodeBlock(v_s_615_);
return v___x_616_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoCodeBlock_view___boxed(lean_object* v_s_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l_Lean_Doc_VersoCodeBlock_view(v_s_617_);
lean_dec(v_s_617_);
return v_res_618_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__4(void){
_start:
{
uint8_t v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
v___x_628_ = 0;
v___x_629_ = l_Lean_Parser_strLit;
v___x_630_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__3));
v___x_631_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__0));
v___x_632_ = l_Lean_Parser_nodeWithAntiquot(v___x_631_, v___x_630_, v___x_629_, v___x_628_);
return v___x_632_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_ArgVal_str___lam__0(lean_object* v_c_633_, lean_object* v_s_634_){
_start:
{
lean_object* v___x_635_; lean_object* v_fn_636_; lean_object* v___x_637_; 
v___x_635_ = lean_obj_once(&l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__4, &l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_ArgVal_str___lam__0___closed__4);
v_fn_636_ = lean_ctor_get(v___x_635_, 1);
lean_inc_ref(v_fn_636_);
v___x_637_ = lean_apply_2(v_fn_636_, v_c_633_, v_s_634_);
return v___x_637_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__3(void){
_start:
{
uint8_t v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_651_ = 0;
v___x_652_ = l_Lean_Parser_ident;
v___x_653_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__2));
v___x_654_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__0));
v___x_655_ = l_Lean_Parser_nodeWithAntiquot(v___x_654_, v___x_653_, v___x_652_, v___x_651_);
return v___x_655_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_ArgVal_ident___lam__0(lean_object* v_c_656_, lean_object* v_s_657_){
_start:
{
lean_object* v___x_658_; lean_object* v_fn_659_; lean_object* v___x_660_; 
v___x_658_ = lean_obj_once(&l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__3, &l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_ArgVal_ident___lam__0___closed__3);
v_fn_659_ = lean_ctor_get(v___x_658_, 1);
lean_inc_ref(v_fn_659_);
v___x_660_ = lean_apply_2(v_fn_659_, v_c_656_, v_s_657_);
return v___x_660_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__3(void){
_start:
{
uint8_t v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_674_ = 0;
v___x_675_ = l_Lean_Parser_numLit;
v___x_676_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__2));
v___x_677_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__0));
v___x_678_ = l_Lean_Parser_nodeWithAntiquot(v___x_677_, v___x_676_, v___x_675_, v___x_674_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_ArgVal_num___lam__0(lean_object* v_c_679_, lean_object* v_s_680_){
_start:
{
lean_object* v___x_681_; lean_object* v_fn_682_; lean_object* v___x_683_; 
v___x_681_ = lean_obj_once(&l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__3, &l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_ArgVal_num___lam__0___closed__3);
v_fn_682_ = lean_ctor_get(v___x_681_, 1);
lean_inc_ref(v_fn_682_);
v___x_683_ = lean_apply_2(v_fn_682_, v_c_679_, v_s_680_);
return v___x_683_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_argVal___lam__0___closed__2(void){
_start:
{
uint8_t v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_695_ = 1;
v___x_696_ = ((lean_object*)(l_Lean_Doc_Parser_argVal___lam__0___closed__1));
v___x_697_ = ((lean_object*)(l_Lean_Doc_Parser_argVal___lam__0___closed__0));
v___x_698_ = l_Lean_Parser_mkAntiquot(v___x_697_, v___x_696_, v___x_695_, v___x_695_);
return v___x_698_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_argVal___lam__0___closed__3(void){
_start:
{
lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_699_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_num));
v___x_700_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_ident));
v___x_701_ = l_Lean_Parser_orelse(v___x_700_, v___x_699_);
return v___x_701_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_argVal___lam__0___closed__4(void){
_start:
{
lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; 
v___x_702_ = lean_obj_once(&l_Lean_Doc_Parser_argVal___lam__0___closed__3, &l_Lean_Doc_Parser_argVal___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_argVal___lam__0___closed__3);
v___x_703_ = ((lean_object*)(l_Lean_Doc_Parser_ArgVal_str));
v___x_704_ = l_Lean_Parser_orelse(v___x_703_, v___x_702_);
return v___x_704_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_argVal___lam__0___closed__5(void){
_start:
{
lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v___x_705_ = lean_obj_once(&l_Lean_Doc_Parser_argVal___lam__0___closed__4, &l_Lean_Doc_Parser_argVal___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_argVal___lam__0___closed__4);
v___x_706_ = lean_obj_once(&l_Lean_Doc_Parser_argVal___lam__0___closed__2, &l_Lean_Doc_Parser_argVal___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_argVal___lam__0___closed__2);
v___x_707_ = l_Lean_Parser_withAntiquot(v___x_706_, v___x_705_);
return v___x_707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_argVal___lam__0(lean_object* v_c_708_, lean_object* v_s_709_){
_start:
{
lean_object* v___x_710_; lean_object* v_fn_711_; lean_object* v___x_712_; 
v___x_710_ = lean_obj_once(&l_Lean_Doc_Parser_argVal___lam__0___closed__5, &l_Lean_Doc_Parser_argVal___lam__0___closed__5_once, _init_l_Lean_Doc_Parser_argVal___lam__0___closed__5);
v_fn_711_ = lean_ctor_get(v___x_710_, 1);
lean_inc_ref(v_fn_711_);
v___x_712_ = lean_apply_2(v_fn_711_, v_c_708_, v_s_709_);
return v___x_712_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_anon___lam__0___closed__3(void){
_start:
{
uint8_t v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v___x_726_ = 0;
v___x_727_ = ((lean_object*)(l_Lean_Doc_Parser_argVal));
v___x_728_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_anon___lam__0___closed__2));
v___x_729_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_anon___lam__0___closed__0));
v___x_730_ = l_Lean_Parser_nodeWithAntiquot(v___x_729_, v___x_728_, v___x_727_, v___x_726_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_anon___lam__0(lean_object* v_c_731_, lean_object* v_s_732_){
_start:
{
lean_object* v___x_733_; lean_object* v_fn_734_; lean_object* v___x_735_; 
v___x_733_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_anon___lam__0___closed__3, &l_Lean_Doc_Parser_Arg_anon___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_Arg_anon___lam__0___closed__3);
v_fn_734_ = lean_ctor_get(v___x_733_, 1);
lean_inc_ref(v_fn_734_);
v___x_735_ = lean_apply_2(v_fn_734_, v_c_731_, v_s_732_);
return v___x_735_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1(){
_start:
{
lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_743_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_anon___lam__0___closed__2));
v___x_744_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1___closed__0));
v___x_745_ = l_Lean_addBuiltinDocString(v___x_743_, v___x_744_);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1___boxed(lean_object* v_a_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_anon___regBuiltin_Lean_Doc_Parser_Arg_anon_docString__1();
return v_res_747_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__3(void){
_start:
{
lean_object* v___x_756_; lean_object* v___x_757_; 
v___x_756_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named___lam__0___closed__2));
v___x_757_ = l_Lean_Parser_symbol(v___x_756_);
return v___x_757_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__5(void){
_start:
{
lean_object* v___x_759_; lean_object* v___x_760_; 
v___x_759_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named___lam__0___closed__4));
v___x_760_ = l_Lean_Parser_symbol(v___x_759_);
return v___x_760_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__7(void){
_start:
{
lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_762_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named___lam__0___closed__6));
v___x_763_ = l_Lean_Parser_symbol(v___x_762_);
return v___x_763_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__8(void){
_start:
{
lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_764_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__7, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__7_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__7);
v___x_765_ = ((lean_object*)(l_Lean_Doc_Parser_argVal));
v___x_766_ = l_Lean_Parser_andthen(v___x_765_, v___x_764_);
return v___x_766_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__9(void){
_start:
{
lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; 
v___x_767_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__8, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__8_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__8);
v___x_768_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__5, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__5_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__5);
v___x_769_ = l_Lean_Parser_andthen(v___x_768_, v___x_767_);
return v___x_769_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__10(void){
_start:
{
lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_770_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__9, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__9_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__9);
v___x_771_ = l_Lean_Parser_ident;
v___x_772_ = l_Lean_Parser_andthen(v___x_771_, v___x_770_);
return v___x_772_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__11(void){
_start:
{
lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; 
v___x_773_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__10, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__10_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__10);
v___x_774_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__3, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__3);
v___x_775_ = l_Lean_Parser_andthen(v___x_774_, v___x_773_);
return v___x_775_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__12(void){
_start:
{
uint8_t v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; 
v___x_776_ = 0;
v___x_777_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__11, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__11_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__11);
v___x_778_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named___lam__0___closed__1));
v___x_779_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named___lam__0___closed__0));
v___x_780_ = l_Lean_Parser_nodeWithAntiquot(v___x_779_, v___x_778_, v___x_777_, v___x_776_);
return v___x_780_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_named___lam__0(lean_object* v_c_781_, lean_object* v_s_782_){
_start:
{
lean_object* v___x_783_; lean_object* v_fn_784_; lean_object* v___x_785_; 
v___x_783_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__12, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__12_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__12);
v_fn_784_ = lean_ctor_get(v___x_783_, 1);
lean_inc_ref(v_fn_784_);
v___x_785_ = lean_apply_2(v_fn_784_, v_c_781_, v_s_782_);
return v___x_785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1(){
_start:
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; 
v___x_793_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named___lam__0___closed__1));
v___x_794_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1___closed__0));
v___x_795_ = l_Lean_addBuiltinDocString(v___x_793_, v___x_794_);
return v___x_795_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1___boxed(lean_object* v_a_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1();
return v_res_797_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__2(void){
_start:
{
lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; 
v___x_805_ = ((lean_object*)(l_Lean_Doc_Parser_argVal));
v___x_806_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__5, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__5_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__5);
v___x_807_ = l_Lean_Parser_andthen(v___x_806_, v___x_805_);
return v___x_807_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__3(void){
_start:
{
lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; 
v___x_808_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__2, &l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__2);
v___x_809_ = l_Lean_Parser_ident;
v___x_810_ = l_Lean_Parser_andthen(v___x_809_, v___x_808_);
return v___x_810_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__4(void){
_start:
{
uint8_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_811_ = 0;
v___x_812_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__3, &l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__3);
v___x_813_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__1));
v___x_814_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__0));
v___x_815_ = l_Lean_Parser_nodeWithAntiquot(v___x_814_, v___x_813_, v___x_812_, v___x_811_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_named__no__paren___lam__0(lean_object* v_c_816_, lean_object* v_s_817_){
_start:
{
lean_object* v___x_818_; lean_object* v_fn_819_; lean_object* v___x_820_; 
v___x_818_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__4, &l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__4);
v_fn_819_ = lean_ctor_get(v___x_818_, 1);
lean_inc_ref(v_fn_819_);
v___x_820_ = lean_apply_2(v_fn_819_, v_c_816_, v_s_817_);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1(){
_start:
{
lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; 
v___x_827_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named__no__paren___lam__0___closed__1));
v___x_828_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named___regBuiltin_Lean_Doc_Parser_Arg_named_docString__1___closed__0));
v___x_829_ = l_Lean_addBuiltinDocString(v___x_827_, v___x_828_);
return v___x_829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1___boxed(lean_object* v_a_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_named__no__paren___regBuiltin_Lean_Doc_Parser_Arg_named__no__paren_docString__1();
return v_res_831_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__3(void){
_start:
{
lean_object* v___x_840_; lean_object* v___x_841_; 
v___x_840_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__2));
v___x_841_ = l_Lean_Parser_symbol(v___x_840_);
return v___x_841_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__4(void){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; 
v___x_842_ = l_Lean_Parser_ident;
v___x_843_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__3, &l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__3);
v___x_844_ = l_Lean_Parser_andthen(v___x_843_, v___x_842_);
return v___x_844_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__5(void){
_start:
{
uint8_t v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; 
v___x_845_ = 0;
v___x_846_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__4, &l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__4);
v___x_847_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__1));
v___x_848_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__0));
v___x_849_ = l_Lean_Parser_nodeWithAntiquot(v___x_848_, v___x_847_, v___x_846_, v___x_845_);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_flag__on___lam__0(lean_object* v_c_850_, lean_object* v_s_851_){
_start:
{
lean_object* v___x_852_; lean_object* v_fn_853_; lean_object* v___x_854_; 
v___x_852_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__5, &l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__5_once, _init_l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__5);
v_fn_853_ = lean_ctor_get(v___x_852_, 1);
lean_inc_ref(v_fn_853_);
v___x_854_ = lean_apply_2(v_fn_853_, v_c_850_, v_s_851_);
return v___x_854_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1(){
_start:
{
lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_862_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__on___lam__0___closed__1));
v___x_863_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1___closed__0));
v___x_864_ = l_Lean_addBuiltinDocString(v___x_862_, v___x_863_);
return v___x_864_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1___boxed(lean_object* v_a_865_){
_start:
{
lean_object* v_res_866_; 
v_res_866_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__on___regBuiltin_Lean_Doc_Parser_Arg_flag__on_docString__1();
return v_res_866_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__3(void){
_start:
{
lean_object* v___x_875_; lean_object* v___x_876_; 
v___x_875_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__2));
v___x_876_ = l_Lean_Parser_symbol(v___x_875_);
return v___x_876_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__4(void){
_start:
{
lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_877_ = l_Lean_Parser_ident;
v___x_878_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__3, &l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__3);
v___x_879_ = l_Lean_Parser_andthen(v___x_878_, v___x_877_);
return v___x_879_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__5(void){
_start:
{
uint8_t v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; 
v___x_880_ = 0;
v___x_881_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__4, &l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__4);
v___x_882_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__1));
v___x_883_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__0));
v___x_884_ = l_Lean_Parser_nodeWithAntiquot(v___x_883_, v___x_882_, v___x_881_, v___x_880_);
return v___x_884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_Arg_flag__off___lam__0(lean_object* v_c_885_, lean_object* v_s_886_){
_start:
{
lean_object* v___x_887_; lean_object* v_fn_888_; lean_object* v___x_889_; 
v___x_887_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__5, &l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__5_once, _init_l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__5);
v_fn_888_ = lean_ctor_get(v___x_887_, 1);
lean_inc_ref(v_fn_888_);
v___x_889_ = lean_apply_2(v_fn_888_, v_c_885_, v_s_886_);
return v___x_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1(){
_start:
{
lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; 
v___x_897_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__off___lam__0___closed__1));
v___x_898_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1___closed__0));
v___x_899_ = l_Lean_addBuiltinDocString(v___x_897_, v___x_898_);
return v___x_899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1___boxed(lean_object* v_a_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Arg_flag__off___regBuiltin_Lean_Doc_Parser_Arg_flag__off_docString__1();
return v_res_901_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___lam__0___closed__2(void){
_start:
{
uint8_t v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; 
v___x_908_ = 1;
v___x_909_ = ((lean_object*)(l_Lean_Doc_Parser_arg___lam__0___closed__1));
v___x_910_ = ((lean_object*)(l_Lean_Doc_Parser_arg___lam__0___closed__0));
v___x_911_ = l_Lean_Parser_mkAntiquot(v___x_910_, v___x_909_, v___x_908_, v___x_908_);
return v___x_911_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_912_; lean_object* v___x_913_; 
v___x_912_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named__no__paren));
v___x_913_ = l_Lean_Parser_atomic(v___x_912_);
return v___x_913_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___lam__0___closed__4(void){
_start:
{
lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; 
v___x_914_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_anon));
v___x_915_ = lean_obj_once(&l_Lean_Doc_Parser_arg___lam__0___closed__3, &l_Lean_Doc_Parser_arg___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_arg___lam__0___closed__3);
v___x_916_ = l_Lean_Parser_orelse(v___x_915_, v___x_914_);
return v___x_916_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
v___x_917_ = lean_obj_once(&l_Lean_Doc_Parser_arg___lam__0___closed__4, &l_Lean_Doc_Parser_arg___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_arg___lam__0___closed__4);
v___x_918_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__off));
v___x_919_ = l_Lean_Parser_orelse(v___x_918_, v___x_917_);
return v___x_919_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___lam__0___closed__6(void){
_start:
{
lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; 
v___x_920_ = lean_obj_once(&l_Lean_Doc_Parser_arg___lam__0___closed__5, &l_Lean_Doc_Parser_arg___lam__0___closed__5_once, _init_l_Lean_Doc_Parser_arg___lam__0___closed__5);
v___x_921_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_flag__on));
v___x_922_ = l_Lean_Parser_orelse(v___x_921_, v___x_920_);
return v___x_922_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; 
v___x_923_ = lean_obj_once(&l_Lean_Doc_Parser_arg___lam__0___closed__6, &l_Lean_Doc_Parser_arg___lam__0___closed__6_once, _init_l_Lean_Doc_Parser_arg___lam__0___closed__6);
v___x_924_ = ((lean_object*)(l_Lean_Doc_Parser_Arg_named));
v___x_925_ = l_Lean_Parser_orelse(v___x_924_, v___x_923_);
return v___x_925_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_arg___lam__0___closed__8(void){
_start:
{
lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; 
v___x_926_ = lean_obj_once(&l_Lean_Doc_Parser_arg___lam__0___closed__7, &l_Lean_Doc_Parser_arg___lam__0___closed__7_once, _init_l_Lean_Doc_Parser_arg___lam__0___closed__7);
v___x_927_ = lean_obj_once(&l_Lean_Doc_Parser_arg___lam__0___closed__2, &l_Lean_Doc_Parser_arg___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_arg___lam__0___closed__2);
v___x_928_ = l_Lean_Parser_withAntiquot(v___x_927_, v___x_926_);
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_arg___lam__0(lean_object* v_c_929_, lean_object* v_s_930_){
_start:
{
lean_object* v___x_931_; lean_object* v_fn_932_; lean_object* v___x_933_; 
v___x_931_ = lean_obj_once(&l_Lean_Doc_Parser_arg___lam__0___closed__8, &l_Lean_Doc_Parser_arg___lam__0___closed__8_once, _init_l_Lean_Doc_Parser_arg___lam__0___closed__8);
v_fn_932_ = lean_ctor_get(v___x_931_, 1);
lean_inc_ref(v_fn_932_);
v___x_933_ = lean_apply_2(v_fn_932_, v_c_929_, v_s_930_);
return v___x_933_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__3(void){
_start:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; 
v___x_947_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__7, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__7_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__7);
v___x_948_ = ((lean_object*)(l_Lean_Doc_Parser_versoLinkUrl));
v___x_949_ = l_Lean_Parser_andthen(v___x_948_, v___x_947_);
return v___x_949_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__4(void){
_start:
{
lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; 
v___x_950_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__3, &l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__3);
v___x_951_ = lean_obj_once(&l_Lean_Doc_Parser_Arg_named___lam__0___closed__3, &l_Lean_Doc_Parser_Arg_named___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_Arg_named___lam__0___closed__3);
v___x_952_ = l_Lean_Parser_andthen(v___x_951_, v___x_950_);
return v___x_952_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__5(void){
_start:
{
uint8_t v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; 
v___x_953_ = 0;
v___x_954_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__4, &l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__4);
v___x_955_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__2));
v___x_956_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__0));
v___x_957_ = l_Lean_Parser_nodeWithAntiquot(v___x_956_, v___x_955_, v___x_954_, v___x_953_);
return v___x_957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_LinkTarget_url___lam__0(lean_object* v_c_958_, lean_object* v_s_959_){
_start:
{
lean_object* v___x_960_; lean_object* v_fn_961_; lean_object* v___x_962_; 
v___x_960_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__5, &l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__5_once, _init_l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__5);
v_fn_961_ = lean_ctor_get(v___x_960_, 1);
lean_inc_ref(v_fn_961_);
v___x_962_ = lean_apply_2(v_fn_961_, v_c_958_, v_s_959_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1(){
_start:
{
lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; 
v___x_970_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_url___lam__0___closed__2));
v___x_971_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1___closed__0));
v___x_972_ = l_Lean_addBuiltinDocString(v___x_970_, v___x_971_);
return v___x_972_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1___boxed(lean_object* v_a_973_){
_start:
{
lean_object* v_res_974_; 
v_res_974_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_url___regBuiltin_Lean_Doc_Parser_LinkTarget_url_docString__1();
return v_res_974_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__3(void){
_start:
{
lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_983_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__2));
v___x_984_ = l_Lean_Parser_symbol(v___x_983_);
return v___x_984_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__5(void){
_start:
{
lean_object* v___x_986_; lean_object* v___x_987_; 
v___x_986_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__4));
v___x_987_ = l_Lean_Parser_symbol(v___x_986_);
return v___x_987_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__6(void){
_start:
{
lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
v___x_988_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__5, &l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__5_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__5);
v___x_989_ = ((lean_object*)(l_Lean_Doc_Parser_versoRef));
v___x_990_ = l_Lean_Parser_andthen(v___x_989_, v___x_988_);
return v___x_990_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__7(void){
_start:
{
lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; 
v___x_991_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__6, &l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__6_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__6);
v___x_992_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__3, &l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__3);
v___x_993_ = l_Lean_Parser_andthen(v___x_992_, v___x_991_);
return v___x_993_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__8(void){
_start:
{
uint8_t v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; 
v___x_994_ = 0;
v___x_995_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__7, &l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__7_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__7);
v___x_996_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__1));
v___x_997_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__0));
v___x_998_ = l_Lean_Parser_nodeWithAntiquot(v___x_997_, v___x_996_, v___x_995_, v___x_994_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_LinkTarget_ref___lam__0(lean_object* v_c_999_, lean_object* v_s_1000_){
_start:
{
lean_object* v___x_1001_; lean_object* v_fn_1002_; lean_object* v___x_1003_; 
v___x_1001_ = lean_obj_once(&l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__8, &l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__8_once, _init_l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__8);
v_fn_1002_ = lean_ctor_get(v___x_1001_, 1);
lean_inc_ref(v_fn_1002_);
v___x_1003_ = lean_apply_2(v_fn_1002_, v_c_999_, v_s_1000_);
return v___x_1003_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1(){
_start:
{
lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1011_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__1));
v___x_1012_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1___closed__0));
v___x_1013_ = l_Lean_addBuiltinDocString(v___x_1011_, v___x_1012_);
return v___x_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1___boxed(lean_object* v_a_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_LinkTarget_ref___regBuiltin_Lean_Doc_Parser_LinkTarget_ref_docString__1();
return v_res_1015_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_linkTarget___lam__0___closed__2(void){
_start:
{
uint8_t v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1022_ = 1;
v___x_1023_ = ((lean_object*)(l_Lean_Doc_Parser_linkTarget___lam__0___closed__1));
v___x_1024_ = ((lean_object*)(l_Lean_Doc_Parser_linkTarget___lam__0___closed__0));
v___x_1025_ = l_Lean_Parser_mkAntiquot(v___x_1024_, v___x_1023_, v___x_1022_, v___x_1022_);
return v___x_1025_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_linkTarget___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; 
v___x_1026_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref));
v___x_1027_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_url));
v___x_1028_ = l_Lean_Parser_orelse(v___x_1027_, v___x_1026_);
return v___x_1028_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_linkTarget___lam__0___closed__4(void){
_start:
{
lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; 
v___x_1029_ = lean_obj_once(&l_Lean_Doc_Parser_linkTarget___lam__0___closed__3, &l_Lean_Doc_Parser_linkTarget___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_linkTarget___lam__0___closed__3);
v___x_1030_ = lean_obj_once(&l_Lean_Doc_Parser_linkTarget___lam__0___closed__2, &l_Lean_Doc_Parser_linkTarget___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_linkTarget___lam__0___closed__2);
v___x_1031_ = l_Lean_Parser_withAntiquot(v___x_1030_, v___x_1029_);
return v___x_1031_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_linkTarget___lam__0(lean_object* v_c_1032_, lean_object* v_s_1033_){
_start:
{
lean_object* v___x_1034_; lean_object* v_fn_1035_; lean_object* v___x_1036_; 
v___x_1034_ = lean_obj_once(&l_Lean_Doc_Parser_linkTarget___lam__0___closed__4, &l_Lean_Doc_Parser_linkTarget___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_linkTarget___lam__0___closed__4);
v_fn_1035_ = lean_ctor_get(v___x_1034_, 1);
lean_inc_ref(v_fn_1035_);
v___x_1036_ = lean_apply_2(v_fn_1035_, v_c_1032_, v_s_1033_);
return v___x_1036_;
}
}
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(lean_object* v_x_1042_, lean_object* v_x_1043_){
_start:
{
if (lean_obj_tag(v_x_1042_) == 0)
{
if (lean_obj_tag(v_x_1043_) == 0)
{
uint8_t v___x_1044_; 
v___x_1044_ = 1;
return v___x_1044_;
}
else
{
uint8_t v___x_1045_; 
v___x_1045_ = 0;
return v___x_1045_;
}
}
else
{
if (lean_obj_tag(v_x_1043_) == 0)
{
uint8_t v___x_1046_; 
v___x_1046_ = 0;
return v___x_1046_;
}
else
{
lean_object* v_val_1047_; lean_object* v_val_1048_; uint8_t v___x_1049_; 
v_val_1047_ = lean_ctor_get(v_x_1042_, 0);
v_val_1048_ = lean_ctor_get(v_x_1043_, 0);
v___x_1049_ = l_Lean_Parser_instBEqError_beq(v_val_1047_, v_val_1048_);
return v___x_1049_;
}
}
}
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1___boxed(lean_object* v_x_1050_, lean_object* v_x_1051_){
_start:
{
uint8_t v_res_1052_; lean_object* v_r_1053_; 
v_res_1052_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_x_1050_, v_x_1051_);
lean_dec(v_x_1051_);
lean_dec(v_x_1050_);
v_r_1053_ = lean_box(v_res_1052_);
return v_r_1053_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0(lean_object* v_x_1054_, lean_object* v_st_1055_){
_start:
{
lean_inc_ref(v_st_1055_);
return v_st_1055_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0___boxed(lean_object* v_x_1056_, lean_object* v_st_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__0(v_x_1056_, v_st_1057_);
lean_dec_ref(v_st_1057_);
lean_dec_ref(v_x_1056_);
return v_res_1058_;
}
}
LEAN_EXPORT uint8_t l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__0(uint32_t v___x_1059_, uint32_t v_x_1060_){
_start:
{
uint8_t v___x_1061_; 
v___x_1061_ = lean_uint32_dec_eq(v_x_1060_, v___x_1059_);
return v___x_1061_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__0___boxed(lean_object* v___x_1062_, lean_object* v_x_1063_){
_start:
{
uint32_t v___x_577__boxed_1064_; uint32_t v_x_578__boxed_1065_; uint8_t v_res_1066_; lean_object* v_r_1067_; 
v___x_577__boxed_1064_ = lean_unbox_uint32(v___x_1062_);
lean_dec(v___x_1062_);
v_x_578__boxed_1065_ = lean_unbox_uint32(v_x_1063_);
lean_dec(v_x_1063_);
v_res_1066_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__0(v___x_577__boxed_1064_, v_x_578__boxed_1065_);
v_r_1067_ = lean_box(v_res_1066_);
return v_r_1067_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__2(lean_object* v_b_1068_, lean_object* v___f_1069_, lean_object* v___y_1070_, lean_object* v___y_1071_){
_start:
{
lean_object* v___x_1072_; 
v___x_1072_ = l_Lean_Parser_andthenFn(v_b_1068_, v___f_1069_, v___y_1070_, v___y_1071_);
return v___x_1072_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__1(uint32_t v___x_1073_, lean_object* v___f_1074_, lean_object* v___y_1075_, lean_object* v___y_1076_){
_start:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; 
v___x_1077_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_1078_ = lean_string_push(v___x_1077_, v___x_1073_);
v___x_1079_ = l_Lean_Parser_satisfyFn(v___f_1074_, v___x_1078_, v___y_1075_, v___y_1076_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__1___boxed(lean_object* v___x_1080_, lean_object* v___f_1081_, lean_object* v___y_1082_, lean_object* v___y_1083_){
_start:
{
uint32_t v___x_594__boxed_1084_; lean_object* v_res_1085_; 
v___x_594__boxed_1084_ = lean_unbox_uint32(v___x_1080_);
lean_dec(v___x_1080_);
v_res_1085_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__1(v___x_594__boxed_1084_, v___f_1081_, v___y_1082_, v___y_1083_);
lean_dec_ref(v___y_1082_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg(lean_object* v___x_1086_, lean_object* v_s_1087_, lean_object* v_a_1088_, lean_object* v_b_1089_, lean_object* v___y_1090_, lean_object* v___y_1091_){
_start:
{
uint8_t v_decide_1092_; 
v_decide_1092_ = lean_nat_dec_eq(v_a_1088_, v___x_1086_);
if (v_decide_1092_ == 0)
{
uint32_t v___x_1093_; lean_object* v___x_1094_; lean_object* v___f_1095_; lean_object* v___x_1096_; lean_object* v___f_1097_; lean_object* v___f_1098_; lean_object* v___x_1099_; 
v___x_1093_ = lean_string_utf8_get_fast(v_s_1087_, v_a_1088_);
v___x_1094_ = lean_box_uint32(v___x_1093_);
v___f_1095_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1095_, 0, v___x_1094_);
v___x_1096_ = lean_box_uint32(v___x_1093_);
v___f_1097_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1097_, 0, v___x_1096_);
lean_closure_set(v___f_1097_, 1, v___f_1095_);
v___f_1098_ = lean_alloc_closure((void*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___lam__2), 4, 2);
lean_closure_set(v___f_1098_, 0, v_b_1089_);
lean_closure_set(v___f_1098_, 1, v___f_1097_);
v___x_1099_ = lean_string_utf8_next_fast(v_s_1087_, v_a_1088_);
lean_dec(v_a_1088_);
v_a_1088_ = v___x_1099_;
v_b_1089_ = v___f_1098_;
goto _start;
}
else
{
lean_object* v___x_1101_; 
lean_dec(v_a_1088_);
v___x_1101_ = lean_apply_2(v_b_1089_, v___y_1090_, v___y_1091_);
return v___x_1101_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg___boxed(lean_object* v___x_1102_, lean_object* v_s_1103_, lean_object* v_a_1104_, lean_object* v_b_1105_, lean_object* v___y_1106_, lean_object* v___y_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg(v___x_1102_, v_s_1103_, v_a_1104_, v_b_1105_, v___y_1106_, v___y_1107_);
lean_dec_ref(v_s_1103_);
lean_dec(v___x_1102_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1(lean_object* v_s_1110_, lean_object* v___f_1111_, lean_object* v_c_1112_, lean_object* v_st_1113_){
_start:
{
lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v_st_x27_1116_; lean_object* v_errorMsg_1117_; lean_object* v___x_1118_; uint8_t v___x_1119_; 
v___x_1114_ = lean_string_utf8_byte_size(v_s_1110_);
v___x_1115_ = lean_unsigned_to_nat(0u);
lean_inc_ref(v_st_1113_);
v_st_x27_1116_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg(v___x_1114_, v_s_1110_, v___x_1115_, v___f_1111_, v_c_1112_, v_st_1113_);
v_errorMsg_1117_ = lean_ctor_get(v_st_x27_1116_, 4);
v___x_1118_ = lean_box(0);
v___x_1119_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_1117_, v___x_1118_);
if (v___x_1119_ == 0)
{
lean_object* v_pos_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; 
v_pos_1120_ = lean_ctor_get(v_st_1113_, 2);
lean_inc(v_pos_1120_);
lean_dec_ref(v_st_1113_);
v___x_1121_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0));
v___x_1122_ = lean_string_append(v___x_1121_, v_s_1110_);
v___x_1123_ = lean_string_append(v___x_1122_, v___x_1121_);
v___x_1124_ = l_Lean_Parser_ParserState_mkErrorAt(v_st_x27_1116_, v___x_1123_, v_pos_1120_, v___x_1118_);
return v___x_1124_;
}
else
{
lean_dec_ref(v_st_1113_);
return v_st_x27_1116_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___boxed(lean_object* v_s_1125_, lean_object* v___f_1126_, lean_object* v_c_1127_, lean_object* v_st_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1(v_s_1125_, v___f_1126_, v_c_1127_, v_st_1128_);
lean_dec_ref(v_s_1125_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(lean_object* v_s_1131_){
_start:
{
lean_object* v___f_1132_; lean_object* v___f_1133_; lean_object* v___x_1134_; uint8_t v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
v___f_1132_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___closed__0));
v___f_1133_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1133_, 0, v_s_1131_);
lean_closure_set(v___f_1133_, 1, v___f_1132_);
v___x_1134_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_1135_ = 1;
v___x_1136_ = lean_box(v___x_1135_);
v___x_1137_ = lean_alloc_closure((void*)(l_Lean_Parser_rawFn___boxed), 4, 2);
lean_closure_set(v___x_1137_, 0, v___f_1133_);
lean_closure_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1138_, 0, v___x_1134_);
lean_ctor_set(v___x_1138_, 1, v___x_1137_);
v___x_1139_ = l_Lean_Parser_tokenWithAntiquot(v___x_1138_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0(lean_object* v___x_1140_, lean_object* v___x_1141_, lean_object* v_s_1142_, lean_object* v_inst_1143_, lean_object* v_R_1144_, lean_object* v_a_1145_, lean_object* v_b_1146_, lean_object* v_c_1147_, lean_object* v___y_1148_, lean_object* v___y_1149_){
_start:
{
lean_object* v___x_1150_; 
v___x_1150_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___redArg(v___x_1141_, v_s_1142_, v_a_1145_, v_b_1146_, v___y_1148_, v___y_1149_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0___boxed(lean_object* v___x_1151_, lean_object* v___x_1152_, lean_object* v_s_1153_, lean_object* v_inst_1154_, lean_object* v_R_1155_, lean_object* v_a_1156_, lean_object* v_b_1157_, lean_object* v_c_1158_, lean_object* v___y_1159_, lean_object* v___y_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__0(v___x_1151_, v___x_1152_, v_s_1153_, v_inst_1154_, v_R_1155_, v_a_1156_, v_b_1157_, v_c_1158_, v___y_1159_, v___y_1160_);
lean_dec_ref(v_s_1153_);
lean_dec(v___x_1152_);
lean_dec_ref(v___x_1151_);
return v_res_1161_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0(uint32_t v_ch_1162_, uint32_t v_x_1163_){
_start:
{
uint8_t v___x_1164_; 
v___x_1164_ = lean_uint32_dec_eq(v_x_1163_, v_ch_1162_);
return v___x_1164_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0___boxed(lean_object* v_ch_1165_, lean_object* v_x_1166_){
_start:
{
uint32_t v_ch_boxed_1167_; uint32_t v_x_149__boxed_1168_; uint8_t v_res_1169_; lean_object* v_r_1170_; 
v_ch_boxed_1167_ = lean_unbox_uint32(v_ch_1165_);
lean_dec(v_ch_1165_);
v_x_149__boxed_1168_ = lean_unbox_uint32(v_x_1166_);
lean_dec(v_x_1166_);
v_res_1169_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0(v_ch_boxed_1167_, v_x_149__boxed_1168_);
v_r_1170_ = lean_box(v_res_1169_);
return v_r_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1(uint32_t v_ch_1172_, lean_object* v___f_1173_, lean_object* v_c_1174_, lean_object* v_st_1175_){
_start:
{
lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v_st_x27_1181_; lean_object* v_errorMsg_1182_; lean_object* v___x_1183_; uint8_t v___x_1184_; 
v___x_1176_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0));
v___x_1177_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_1178_ = lean_string_push(v___x_1177_, v_ch_1172_);
v___x_1179_ = lean_string_append(v___x_1176_, v___x_1178_);
v___x_1180_ = lean_string_append(v___x_1179_, v___x_1176_);
lean_inc_ref(v_st_1175_);
v_st_x27_1181_ = l_Lean_Parser_takeWhile1Fn(v___f_1173_, v___x_1180_, v_c_1174_, v_st_1175_);
v_errorMsg_1182_ = lean_ctor_get(v_st_x27_1181_, 4);
v___x_1183_ = lean_box(0);
v___x_1184_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_1182_, v___x_1183_);
if (v___x_1184_ == 0)
{
lean_object* v_pos_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; 
v_pos_1185_ = lean_ctor_get(v_st_1175_, 2);
lean_inc(v_pos_1185_);
lean_dec_ref(v_st_1175_);
v___x_1186_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___closed__0));
v___x_1187_ = lean_string_append(v___x_1186_, v___x_1178_);
lean_dec_ref(v___x_1178_);
v___x_1188_ = lean_string_append(v___x_1187_, v___x_1176_);
v___x_1189_ = l_Lean_Parser_ParserState_mkErrorAt(v_st_x27_1181_, v___x_1188_, v_pos_1185_, v___x_1183_);
return v___x_1189_;
}
else
{
lean_dec_ref(v___x_1178_);
lean_dec_ref(v_st_1175_);
return v_st_x27_1181_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___boxed(lean_object* v_ch_1190_, lean_object* v___f_1191_, lean_object* v_c_1192_, lean_object* v_st_1193_){
_start:
{
uint32_t v_ch_boxed_1194_; lean_object* v_res_1195_; 
v_ch_boxed_1194_ = lean_unbox_uint32(v_ch_1190_);
lean_dec(v_ch_1190_);
v_res_1195_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1(v_ch_boxed_1194_, v___f_1191_, v_c_1192_, v_st_1193_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(uint32_t v_ch_1196_){
_start:
{
lean_object* v___x_1197_; lean_object* v___f_1198_; lean_object* v___x_1199_; lean_object* v___f_1200_; lean_object* v___x_1201_; uint8_t v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v___x_1197_ = lean_box_uint32(v_ch_1196_);
v___f_1198_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1198_, 0, v___x_1197_);
v___x_1199_ = lean_box_uint32(v_ch_1196_);
v___f_1200_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___lam__1___boxed), 4, 2);
lean_closure_set(v___f_1200_, 0, v___x_1199_);
lean_closure_set(v___f_1200_, 1, v___f_1198_);
v___x_1201_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_1202_ = 1;
v___x_1203_ = lean_box(v___x_1202_);
v___x_1204_ = lean_alloc_closure((void*)(l_Lean_Parser_rawFn___boxed), 4, 2);
lean_closure_set(v___x_1204_, 0, v___f_1200_);
lean_closure_set(v___x_1204_, 1, v___x_1203_);
v___x_1205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1205_, 0, v___x_1201_);
lean_ctor_set(v___x_1205_, 1, v___x_1204_);
v___x_1206_ = l_Lean_Parser_tokenWithAntiquot(v___x_1205_);
return v___x_1206_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun___boxed(lean_object* v_ch_1207_){
_start:
{
uint32_t v_ch_boxed_1208_; lean_object* v_res_1209_; 
v_ch_boxed_1208_ = lean_unbox_uint32(v_ch_1207_);
lean_dec(v_ch_1207_);
v_res_1209_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v_ch_boxed_1208_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0(lean_object* v_c_1211_, lean_object* v_s_1212_){
_start:
{
lean_object* v_toInputContext_1213_; lean_object* v_pos_1214_; uint8_t v___x_1215_; 
v_toInputContext_1213_ = lean_ctor_get(v_c_1211_, 0);
v_pos_1214_ = lean_ctor_get(v_s_1212_, 2);
v___x_1215_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1213_, v_pos_1214_);
if (v___x_1215_ == 0)
{
lean_object* v_inputString_1216_; uint32_t v_ch_1217_; uint32_t v___x_1218_; uint8_t v___x_1219_; 
lean_inc(v_pos_1214_);
v_inputString_1216_ = lean_ctor_get(v_toInputContext_1213_, 0);
v_ch_1217_ = lean_string_utf8_get_fast(v_inputString_1216_, v_pos_1214_);
v___x_1218_ = 42;
v___x_1219_ = lean_uint32_dec_eq(v_ch_1217_, v___x_1218_);
if (v___x_1219_ == 0)
{
uint32_t v___x_1220_; uint8_t v___x_1221_; 
v___x_1220_ = 45;
v___x_1221_ = lean_uint32_dec_eq(v_ch_1217_, v___x_1220_);
if (v___x_1221_ == 0)
{
uint32_t v___x_1222_; uint8_t v___x_1223_; 
v___x_1222_ = 43;
v___x_1223_ = lean_uint32_dec_eq(v_ch_1217_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; lean_object* v___x_1225_; lean_object* v___x_1226_; 
v___x_1224_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0___closed__0));
v___x_1225_ = lean_box(0);
v___x_1226_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_1212_, v___x_1224_, v_pos_1214_, v___x_1225_);
return v___x_1226_;
}
else
{
lean_object* v___x_1227_; 
v___x_1227_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1212_, v_c_1211_, v_pos_1214_);
lean_dec(v_pos_1214_);
return v___x_1227_;
}
}
else
{
lean_object* v___x_1228_; 
v___x_1228_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1212_, v_c_1211_, v_pos_1214_);
lean_dec(v_pos_1214_);
return v___x_1228_;
}
}
else
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1212_, v_c_1211_, v_pos_1214_);
lean_dec(v_pos_1214_);
return v___x_1229_;
}
}
else
{
lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1230_ = lean_box(0);
v___x_1231_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1212_, v___x_1230_);
return v___x_1231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0___boxed(lean_object* v_c_1232_, lean_object* v_s_1233_){
_start:
{
lean_object* v_res_1234_; 
v_res_1234_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__0(v_c_1232_, v_s_1233_);
lean_dec_ref(v_c_1232_);
return v_res_1234_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom___lam__3(lean_object* v___f_1235_, lean_object* v___f_1236_, lean_object* v___f_1237_, lean_object* v_c_1238_, lean_object* v_s_1239_){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; uint8_t v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v_fn_1247_; lean_object* v___x_1248_; 
v___x_1240_ = lean_box(1);
v___x_1241_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1241_, 0, v___f_1235_);
lean_ctor_set(v___x_1241_, 1, v___f_1236_);
lean_ctor_set(v___x_1241_, 2, v___x_1240_);
v___x_1242_ = 1;
v___x_1243_ = lean_box(v___x_1242_);
v___x_1244_ = lean_alloc_closure((void*)(l_Lean_Parser_rawFn___boxed), 4, 2);
lean_closure_set(v___x_1244_, 0, v___f_1237_);
lean_closure_set(v___x_1244_, 1, v___x_1243_);
v___x_1245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1245_, 0, v___x_1241_);
lean_ctor_set(v___x_1245_, 1, v___x_1244_);
v___x_1246_ = l_Lean_Parser_tokenWithAntiquot(v___x_1245_);
v_fn_1247_ = lean_ctor_get(v___x_1246_, 1);
lean_inc_ref(v_fn_1247_);
lean_dec_ref(v___x_1246_);
v___x_1248_ = lean_apply_2(v_fn_1247_, v_c_1238_, v_s_1239_);
return v___x_1248_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0(uint32_t v_x_1258_){
_start:
{
uint32_t v___x_1259_; uint8_t v___x_1260_; 
v___x_1259_ = 48;
v___x_1260_ = lean_uint32_dec_le(v___x_1259_, v_x_1258_);
if (v___x_1260_ == 0)
{
return v___x_1260_;
}
else
{
uint32_t v___x_1261_; uint8_t v___x_1262_; 
v___x_1261_ = 57;
v___x_1262_ = lean_uint32_dec_le(v_x_1258_, v___x_1261_);
return v___x_1262_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0___boxed(lean_object* v_x_1263_){
_start:
{
uint32_t v_x_330__boxed_1264_; uint8_t v_res_1265_; lean_object* v_r_1266_; 
v_x_330__boxed_1264_ = lean_unbox_uint32(v_x_1263_);
lean_dec(v_x_1263_);
v_res_1265_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__0(v_x_330__boxed_1264_);
v_r_1266_ = lean_box(v_res_1265_);
return v_r_1266_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1(uint32_t v_c_1267_){
_start:
{
uint32_t v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = 46;
v___x_1269_ = lean_uint32_dec_eq(v_c_1267_, v___x_1268_);
if (v___x_1269_ == 0)
{
uint32_t v___x_1270_; uint8_t v___x_1271_; 
v___x_1270_ = 41;
v___x_1271_ = lean_uint32_dec_eq(v_c_1267_, v___x_1270_);
return v___x_1271_;
}
else
{
return v___x_1269_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1___boxed(lean_object* v_c_1272_){
_start:
{
uint32_t v_c_boxed_1273_; uint8_t v_res_1274_; lean_object* v_r_1275_; 
v_c_boxed_1273_ = lean_unbox_uint32(v_c_1272_);
lean_dec(v_c_1272_);
v_res_1274_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__1(v_c_boxed_1273_);
v_r_1275_ = lean_box(v_res_1274_);
return v_r_1275_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2(lean_object* v___f_1277_, lean_object* v___y_1278_, lean_object* v___y_1279_){
_start:
{
lean_object* v___x_1280_; lean_object* v___x_1281_; 
v___x_1280_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2___closed__0));
v___x_1281_ = l_Lean_Parser_satisfyFn(v___f_1277_, v___x_1280_, v___y_1278_, v___y_1279_);
return v___x_1281_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2___boxed(lean_object* v___f_1282_, lean_object* v___y_1283_, lean_object* v___y_1284_){
_start:
{
lean_object* v_res_1285_; 
v_res_1285_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__2(v___f_1282_, v___y_1283_, v___y_1284_);
lean_dec_ref(v___y_1283_);
return v_res_1285_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3(lean_object* v___f_1288_, lean_object* v___f_1289_, lean_object* v_c_1290_, lean_object* v_s_1291_){
_start:
{
lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v_s_x27_1294_; lean_object* v_errorMsg_1295_; lean_object* v___x_1296_; uint8_t v___x_1297_; 
v___x_1292_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3___closed__0));
v___x_1293_ = lean_alloc_closure((void*)(l_Lean_Parser_takeWhile1Fn), 4, 2);
lean_closure_set(v___x_1293_, 0, v___f_1288_);
lean_closure_set(v___x_1293_, 1, v___x_1292_);
lean_inc_ref(v_s_1291_);
v_s_x27_1294_ = l_Lean_Parser_andthenFn(v___x_1293_, v___f_1289_, v_c_1290_, v_s_1291_);
v_errorMsg_1295_ = lean_ctor_get(v_s_x27_1294_, 4);
v___x_1296_ = lean_box(0);
v___x_1297_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_1295_, v___x_1296_);
if (v___x_1297_ == 0)
{
lean_object* v_pos_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; 
v_pos_1298_ = lean_ctor_get(v_s_1291_, 2);
lean_inc(v_pos_1298_);
lean_dec_ref(v_s_1291_);
v___x_1299_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom___lam__3___closed__1));
v___x_1300_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_x27_1294_, v___x_1299_, v_pos_1298_, v___x_1296_);
return v___x_1300_;
}
else
{
lean_dec_ref(v_s_1291_);
return v_s_x27_1294_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__0(lean_object* v_c_1317_){
_start:
{
lean_object* v_toInputContext_1318_; lean_object* v_toParserModuleContext_1319_; lean_object* v_toCacheableParserContext_1320_; lean_object* v_tokens_1321_; lean_object* v___x_1323_; uint8_t v_isShared_1324_; uint8_t v_isSharedCheck_1330_; 
v_toInputContext_1318_ = lean_ctor_get(v_c_1317_, 0);
v_toParserModuleContext_1319_ = lean_ctor_get(v_c_1317_, 1);
v_toCacheableParserContext_1320_ = lean_ctor_get(v_c_1317_, 2);
v_tokens_1321_ = lean_ctor_get(v_c_1317_, 3);
v_isSharedCheck_1330_ = !lean_is_exclusive(v_c_1317_);
if (v_isSharedCheck_1330_ == 0)
{
v___x_1323_ = v_c_1317_;
v_isShared_1324_ = v_isSharedCheck_1330_;
goto v_resetjp_1322_;
}
else
{
lean_inc(v_tokens_1321_);
lean_inc(v_toCacheableParserContext_1320_);
lean_inc(v_toParserModuleContext_1319_);
lean_inc(v_toInputContext_1318_);
lean_dec(v_c_1317_);
v___x_1323_ = lean_box(0);
v_isShared_1324_ = v_isSharedCheck_1330_;
goto v_resetjp_1322_;
}
v_resetjp_1322_:
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1325_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__0___closed__0));
v___x_1326_ = l_Lean_Data_Trie_insert___redArg(v_tokens_1321_, v___x_1325_, v___x_1325_);
if (v_isShared_1324_ == 0)
{
lean_ctor_set(v___x_1323_, 3, v___x_1326_);
v___x_1328_ = v___x_1323_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v_toInputContext_1318_);
lean_ctor_set(v_reuseFailAlloc_1329_, 1, v_toParserModuleContext_1319_);
lean_ctor_set(v_reuseFailAlloc_1329_, 2, v_toCacheableParserContext_1320_);
lean_ctor_set(v_reuseFailAlloc_1329_, 3, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__4(void){
_start:
{
uint8_t v___x_1339_; uint8_t v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1339_ = 0;
v___x_1340_ = 1;
v___x_1341_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__3));
v___x_1342_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__0));
v___x_1343_ = l_Lean_Parser_mkAntiquot(v___x_1342_, v___x_1341_, v___x_1340_, v___x_1339_);
return v___x_1343_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__6(void){
_start:
{
lean_object* v___x_1345_; lean_object* v___x_1346_; 
v___x_1345_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__5));
v___x_1346_ = l_Lean_Parser_symbol(v___x_1345_);
return v___x_1346_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__10(void){
_start:
{
lean_object* v___x_1351_; lean_object* v___x_1352_; 
v___x_1351_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__9));
v___x_1352_ = l_Lean_Parser_symbol(v___x_1351_);
return v___x_1352_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__11(void){
_start:
{
lean_object* v___x_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v_p_1356_; 
v___x_1353_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__10, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__10_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__10);
v___x_1354_ = l_Lean_Parser_Term_structInstField;
v___x_1355_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__8));
v_p_1356_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1355_, v___x_1354_, v___x_1353_);
return v_p_1356_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__13(void){
_start:
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
v___x_1358_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__12));
v___x_1359_ = l_Lean_Parser_checkColGe(v___x_1358_);
return v___x_1359_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__14(void){
_start:
{
lean_object* v_p_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v_p_1360_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__11, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__11_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__11);
v___x_1361_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__13, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__13_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__13);
v___x_1362_ = l_Lean_Parser_andthen(v___x_1361_, v_p_1360_);
return v___x_1362_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__15(void){
_start:
{
lean_object* v___x_1363_; lean_object* v___x_1364_; 
v___x_1363_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__12));
v___x_1364_ = l_Lean_Parser_checkColEq(v___x_1363_);
return v___x_1364_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__17(void){
_start:
{
lean_object* v___x_1366_; lean_object* v___x_1367_; 
v___x_1366_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__16));
v___x_1367_ = l_Lean_Parser_checkLinebreakBefore(v___x_1366_);
return v___x_1367_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__18(void){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; 
v___x_1368_ = l_Lean_Parser_pushNone;
v___x_1369_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__17, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__17_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__17);
v___x_1370_ = l_Lean_Parser_andthen(v___x_1369_, v___x_1368_);
return v___x_1370_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__19(void){
_start:
{
lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1371_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__18, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__18_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__18);
v___x_1372_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__15, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__15_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__15);
v___x_1373_ = l_Lean_Parser_andthen(v___x_1372_, v___x_1371_);
return v___x_1373_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__20(void){
_start:
{
lean_object* v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; 
v___x_1374_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__19, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__19_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__19);
v___x_1375_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__6);
v___x_1376_ = l_Lean_Parser_orelse(v___x_1375_, v___x_1374_);
return v___x_1376_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__21(void){
_start:
{
uint8_t v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; 
v___x_1377_ = 1;
v___x_1378_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__20, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__20_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__20);
v___x_1379_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__5));
v___x_1380_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__14, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__14_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__14);
v___x_1381_ = l_Lean_Parser_sepBy(v___x_1380_, v___x_1379_, v___x_1378_, v___x_1377_);
return v___x_1381_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__22(void){
_start:
{
lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1382_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__21, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__21_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__21);
v___x_1383_ = l_Lean_Parser_withPosition(v___x_1382_);
return v___x_1383_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__23(void){
_start:
{
lean_object* v___x_1384_; lean_object* v___x_1385_; 
v___x_1384_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__22, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__22_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__22);
v___x_1385_ = l_Lean_Parser_Term_structInstFields(v___x_1384_);
return v___x_1385_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__24(void){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; lean_object* v___x_1388_; 
v___x_1386_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__23, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__23_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__23);
v___x_1387_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__4);
v___x_1388_ = l_Lean_Parser_withAntiquot(v___x_1387_, v___x_1386_);
return v___x_1388_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1(lean_object* v___f_1389_, lean_object* v_c_1390_, lean_object* v_s_1391_){
_start:
{
lean_object* v___x_1392_; lean_object* v_fn_1393_; lean_object* v___x_1394_; 
v___x_1392_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__24, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__24_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__1___closed__24);
v_fn_1393_ = lean_ctor_get(v___x_1392_, 1);
lean_inc_ref(v_fn_1393_);
v___x_1394_ = l_Lean_Parser_adaptUncacheableContextFn(v___f_1389_, v_fn_1393_, v_c_1390_, v_s_1391_);
return v___x_1394_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_headerMarker___lam__0___closed__2(void){
_start:
{
uint32_t v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = 35;
v___x_1409_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_1408_);
return v___x_1409_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_headerMarker___lam__0___closed__3(void){
_start:
{
uint8_t v___x_1410_; lean_object* v___x_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; 
v___x_1410_ = 0;
v___x_1411_ = lean_obj_once(&l_Lean_Doc_Parser_headerMarker___lam__0___closed__2, &l_Lean_Doc_Parser_headerMarker___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_headerMarker___lam__0___closed__2);
v___x_1412_ = ((lean_object*)(l_Lean_Doc_Parser_headerMarker___lam__0___closed__1));
v___x_1413_ = ((lean_object*)(l_Lean_Doc_Parser_headerMarker___lam__0___closed__0));
v___x_1414_ = l_Lean_Parser_nodeWithAntiquot(v___x_1413_, v___x_1412_, v___x_1411_, v___x_1410_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_headerMarker___lam__0(lean_object* v_c_1415_, lean_object* v_s_1416_){
_start:
{
lean_object* v___x_1417_; lean_object* v_fn_1418_; lean_object* v___x_1419_; 
v___x_1417_ = lean_obj_once(&l_Lean_Doc_Parser_headerMarker___lam__0___closed__3, &l_Lean_Doc_Parser_headerMarker___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_headerMarker___lam__0___closed__3);
v_fn_1418_ = lean_ctor_get(v___x_1417_, 1);
lean_inc_ref(v_fn_1418_);
v___x_1419_ = lean_apply_2(v_fn_1418_, v_c_1415_, v_s_1416_);
return v___x_1419_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_listMarker___lam__0___closed__2(void){
_start:
{
lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1431_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom));
v___x_1432_ = l_Lean_Parser_atomic(v___x_1431_);
return v___x_1432_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_listMarker___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1433_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom));
v___x_1434_ = lean_obj_once(&l_Lean_Doc_Parser_listMarker___lam__0___closed__2, &l_Lean_Doc_Parser_listMarker___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_listMarker___lam__0___closed__2);
v___x_1435_ = l_Lean_Parser_orelse(v___x_1434_, v___x_1433_);
return v___x_1435_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_listMarker___lam__0___closed__4(void){
_start:
{
uint8_t v___x_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
v___x_1436_ = 0;
v___x_1437_ = lean_obj_once(&l_Lean_Doc_Parser_listMarker___lam__0___closed__3, &l_Lean_Doc_Parser_listMarker___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_listMarker___lam__0___closed__3);
v___x_1438_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___lam__0___closed__1));
v___x_1439_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___lam__0___closed__0));
v___x_1440_ = l_Lean_Parser_nodeWithAntiquot(v___x_1439_, v___x_1438_, v___x_1437_, v___x_1436_);
return v___x_1440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_listMarker___lam__0(lean_object* v_c_1441_, lean_object* v_s_1442_){
_start:
{
lean_object* v___x_1443_; lean_object* v_fn_1444_; lean_object* v___x_1445_; 
v___x_1443_ = lean_obj_once(&l_Lean_Doc_Parser_listMarker___lam__0___closed__4, &l_Lean_Doc_Parser_listMarker___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_listMarker___lam__0___closed__4);
v_fn_1444_ = lean_ctor_get(v___x_1443_, 1);
lean_inc_ref(v_fn_1444_);
v___x_1445_ = lean_apply_2(v_fn_1444_, v_c_1441_, v_s_1442_);
return v___x_1445_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___lam__0___closed__0(void){
_start:
{
uint8_t v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1451_ = 0;
v___x_1452_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_bulletAtom));
v___x_1453_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___lam__0___closed__1));
v___x_1454_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___lam__0___closed__0));
v___x_1455_ = l_Lean_Parser_nodeWithAntiquot(v___x_1454_, v___x_1453_, v___x_1452_, v___x_1451_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___lam__0(lean_object* v_c_1456_, lean_object* v_s_1457_){
_start:
{
lean_object* v___x_1458_; lean_object* v_fn_1459_; lean_object* v___x_1460_; 
v___x_1458_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___lam__0___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___lam__0___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker___lam__0___closed__0);
v_fn_1459_ = lean_ctor_get(v___x_1458_, 1);
lean_inc_ref(v_fn_1459_);
v___x_1460_ = lean_apply_2(v_fn_1459_, v_c_1456_, v_s_1457_);
return v___x_1460_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___lam__0___closed__0(void){
_start:
{
uint8_t v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; 
v___x_1466_ = 0;
v___x_1467_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_numberAtom));
v___x_1468_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___lam__0___closed__1));
v___x_1469_ = ((lean_object*)(l_Lean_Doc_Parser_listMarker___lam__0___closed__0));
v___x_1470_ = l_Lean_Parser_nodeWithAntiquot(v___x_1469_, v___x_1468_, v___x_1467_, v___x_1466_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___lam__0(lean_object* v_c_1471_, lean_object* v_s_1472_){
_start:
{
lean_object* v___x_1473_; lean_object* v_fn_1474_; lean_object* v___x_1475_; 
v___x_1473_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___lam__0___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___lam__0___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker___lam__0___closed__0);
v_fn_1474_ = lean_ctor_get(v___x_1473_, 1);
lean_inc_ref(v_fn_1474_);
v___x_1475_ = lean_apply_2(v_fn_1474_, v_c_1471_, v_s_1472_);
return v___x_1475_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0(uint32_t v_x_1481_){
_start:
{
uint32_t v___x_1482_; uint8_t v___x_1483_; 
v___x_1482_ = 58;
v___x_1483_ = lean_uint32_dec_eq(v_x_1481_, v___x_1482_);
return v___x_1483_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0___boxed(lean_object* v_x_1484_){
_start:
{
uint32_t v_x_136__boxed_1485_; uint8_t v_res_1486_; lean_object* v_r_1487_; 
v_x_136__boxed_1485_ = lean_unbox_uint32(v_x_1484_);
lean_dec(v_x_1484_);
v_res_1486_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__0(v_x_136__boxed_1485_);
v_r_1487_ = lean_box(v_res_1486_);
return v_r_1487_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__1(void){
_start:
{
lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1489_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__0));
v___x_1490_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_1489_);
return v___x_1490_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3(lean_object* v___f_1492_, lean_object* v___f_1493_, lean_object* v___f_1494_, lean_object* v_c_1495_, lean_object* v_s_1496_){
_start:
{
lean_object* v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v_fn_1506_; lean_object* v___x_1507_; 
v___x_1497_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__1);
v___x_1498_ = lean_box(1);
v___x_1499_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1499_, 0, v___f_1492_);
lean_ctor_set(v___x_1499_, 1, v___f_1493_);
lean_ctor_set(v___x_1499_, 2, v___x_1498_);
v___x_1500_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker___lam__3___closed__2));
v___x_1501_ = lean_alloc_closure((void*)(l_Lean_Parser_satisfyFn___boxed), 4, 2);
lean_closure_set(v___x_1501_, 0, v___f_1494_);
lean_closure_set(v___x_1501_, 1, v___x_1500_);
v___x_1502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1502_, 0, v___x_1499_);
lean_ctor_set(v___x_1502_, 1, v___x_1501_);
v___x_1503_ = l_Lean_Parser_notFollowedBy(v___x_1502_, v___x_1500_);
v___x_1504_ = l_Lean_Parser_andthen(v___x_1497_, v___x_1503_);
v___x_1505_ = l_Lean_Parser_atomic(v___x_1504_);
v_fn_1506_ = lean_ctor_get(v___x_1505_, 1);
lean_inc_ref(v_fn_1506_);
lean_dec_ref(v___x_1505_);
v___x_1507_ = lean_apply_2(v_fn_1506_, v_c_1495_, v_s_1496_);
return v___x_1507_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__2(void){
_start:
{
uint32_t v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = 95;
v___x_1524_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_1523_);
return v___x_1524_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__3(void){
_start:
{
uint8_t v___x_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1525_ = 0;
v___x_1526_ = lean_obj_once(&l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__2, &l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__2);
v___x_1527_ = ((lean_object*)(l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__1));
v___x_1528_ = ((lean_object*)(l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__0));
v___x_1529_ = l_Lean_Parser_nodeWithAntiquot(v___x_1528_, v___x_1527_, v___x_1526_, v___x_1525_);
return v___x_1529_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_emphDelimiter___lam__0(lean_object* v_c_1530_, lean_object* v_s_1531_){
_start:
{
lean_object* v___x_1532_; lean_object* v_fn_1533_; lean_object* v___x_1534_; 
v___x_1532_ = lean_obj_once(&l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__3, &l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_emphDelimiter___lam__0___closed__3);
v_fn_1533_ = lean_ctor_get(v___x_1532_, 1);
lean_inc_ref(v_fn_1533_);
v___x_1534_ = lean_apply_2(v_fn_1533_, v_c_1530_, v_s_1531_);
return v___x_1534_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__2(void){
_start:
{
uint32_t v___x_1546_; lean_object* v___x_1547_; 
v___x_1546_ = 42;
v___x_1547_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_1546_);
return v___x_1547_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__3(void){
_start:
{
uint8_t v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1548_ = 0;
v___x_1549_ = lean_obj_once(&l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__2, &l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__2);
v___x_1550_ = ((lean_object*)(l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__1));
v___x_1551_ = ((lean_object*)(l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__0));
v___x_1552_ = l_Lean_Parser_nodeWithAntiquot(v___x_1551_, v___x_1550_, v___x_1549_, v___x_1548_);
return v___x_1552_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_boldDelimiter___lam__0(lean_object* v_c_1553_, lean_object* v_s_1554_){
_start:
{
lean_object* v___x_1555_; lean_object* v_fn_1556_; lean_object* v___x_1557_; 
v___x_1555_ = lean_obj_once(&l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__3, &l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_boldDelimiter___lam__0___closed__3);
v_fn_1556_ = lean_ctor_get(v___x_1555_, 1);
lean_inc_ref(v_fn_1556_);
v___x_1557_ = lean_apply_2(v_fn_1556_, v_c_1553_, v_s_1554_);
return v___x_1557_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2(void){
_start:
{
uint32_t v___x_1569_; lean_object* v___x_1570_; 
v___x_1569_ = 96;
v___x_1570_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_1569_);
return v___x_1570_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__3(void){
_start:
{
uint8_t v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1571_ = 0;
v___x_1572_ = lean_obj_once(&l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2, &l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2);
v___x_1573_ = ((lean_object*)(l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__1));
v___x_1574_ = ((lean_object*)(l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__0));
v___x_1575_ = l_Lean_Parser_nodeWithAntiquot(v___x_1574_, v___x_1573_, v___x_1572_, v___x_1571_);
return v___x_1575_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_codeDelimiter___lam__0(lean_object* v_c_1576_, lean_object* v_s_1577_){
_start:
{
lean_object* v___x_1578_; lean_object* v_fn_1579_; lean_object* v___x_1580_; 
v___x_1578_ = lean_obj_once(&l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__3, &l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__3);
v_fn_1579_ = lean_ctor_get(v___x_1578_, 1);
lean_inc_ref(v_fn_1579_);
v___x_1580_ = lean_apply_2(v_fn_1579_, v_c_1576_, v_s_1577_);
return v___x_1580_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__2(void){
_start:
{
uint8_t v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1592_ = 0;
v___x_1593_ = lean_obj_once(&l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2, &l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_codeDelimiter___lam__0___closed__2);
v___x_1594_ = ((lean_object*)(l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__1));
v___x_1595_ = ((lean_object*)(l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__0));
v___x_1596_ = l_Lean_Parser_nodeWithAntiquot(v___x_1595_, v___x_1594_, v___x_1593_, v___x_1592_);
return v___x_1596_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_codeBlockFence___lam__0(lean_object* v_c_1597_, lean_object* v_s_1598_){
_start:
{
lean_object* v___x_1599_; lean_object* v_fn_1600_; lean_object* v___x_1601_; 
v___x_1599_ = lean_obj_once(&l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__2, &l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_codeBlockFence___lam__0___closed__2);
v_fn_1600_ = lean_ctor_get(v___x_1599_, 1);
lean_inc_ref(v_fn_1600_);
v___x_1601_ = lean_apply_2(v_fn_1600_, v_c_1597_, v_s_1598_);
return v___x_1601_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1614_ = ((lean_object*)(l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__2));
v___x_1615_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_1614_);
return v___x_1615_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__4(void){
_start:
{
uint8_t v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1616_ = 0;
v___x_1617_ = lean_obj_once(&l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__3, &l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__3);
v___x_1618_ = ((lean_object*)(l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__1));
v___x_1619_ = ((lean_object*)(l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__0));
v___x_1620_ = l_Lean_Parser_nodeWithAntiquot(v___x_1619_, v___x_1618_, v___x_1617_, v___x_1616_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_inlineMathMarker___lam__0(lean_object* v_c_1621_, lean_object* v_s_1622_){
_start:
{
lean_object* v___x_1623_; lean_object* v_fn_1624_; lean_object* v___x_1625_; 
v___x_1623_ = lean_obj_once(&l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__4, &l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_inlineMathMarker___lam__0___closed__4);
v_fn_1624_ = lean_ctor_get(v___x_1623_, 1);
lean_inc_ref(v_fn_1624_);
v___x_1625_ = lean_apply_2(v_fn_1624_, v_c_1621_, v_s_1622_);
return v___x_1625_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__3(void){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1638_ = ((lean_object*)(l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__2));
v___x_1639_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_1638_);
return v___x_1639_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__4(void){
_start:
{
uint8_t v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; 
v___x_1640_ = 0;
v___x_1641_ = lean_obj_once(&l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__3, &l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__3);
v___x_1642_ = ((lean_object*)(l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__1));
v___x_1643_ = ((lean_object*)(l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__0));
v___x_1644_ = l_Lean_Parser_nodeWithAntiquot(v___x_1643_, v___x_1642_, v___x_1641_, v___x_1640_);
return v___x_1644_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_displayMathMarker___lam__0(lean_object* v_c_1645_, lean_object* v_s_1646_){
_start:
{
lean_object* v___x_1647_; lean_object* v_fn_1648_; lean_object* v___x_1649_; 
v___x_1647_ = lean_obj_once(&l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__4, &l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_displayMathMarker___lam__0___closed__4);
v_fn_1648_ = lean_ctor_get(v___x_1647_, 1);
lean_inc_ref(v_fn_1648_);
v___x_1649_ = lean_apply_2(v_fn_1648_, v_c_1645_, v_s_1646_);
return v___x_1649_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__2(void){
_start:
{
uint32_t v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = 58;
v___x_1662_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_1661_);
return v___x_1662_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__3(void){
_start:
{
uint8_t v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; 
v___x_1663_ = 0;
v___x_1664_ = lean_obj_once(&l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__2, &l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__2);
v___x_1665_ = ((lean_object*)(l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__1));
v___x_1666_ = ((lean_object*)(l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__0));
v___x_1667_ = l_Lean_Parser_nodeWithAntiquot(v___x_1666_, v___x_1665_, v___x_1664_, v___x_1663_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_directiveDelimiter___lam__0(lean_object* v_c_1668_, lean_object* v_s_1669_){
_start:
{
lean_object* v___x_1670_; lean_object* v_fn_1671_; lean_object* v___x_1672_; 
v___x_1670_ = lean_obj_once(&l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__3, &l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_directiveDelimiter___lam__0___closed__3);
v_fn_1671_ = lean_ctor_get(v___x_1670_, 1);
lean_inc_ref(v_fn_1671_);
v___x_1672_ = lean_apply_2(v_fn_1671_, v_c_1668_, v_s_1669_);
return v___x_1672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength(lean_object* v_x_1678_){
_start:
{
if (lean_obj_tag(v_x_1678_) == 1)
{
lean_object* v_args_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; uint8_t v___x_1682_; 
v_args_1679_ = lean_ctor_get(v_x_1678_, 2);
v___x_1680_ = lean_array_get_size(v_args_1679_);
v___x_1681_ = lean_unsigned_to_nat(1u);
v___x_1682_ = lean_nat_dec_eq(v___x_1680_, v___x_1681_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; 
v___x_1683_ = lean_box(0);
return v___x_1683_;
}
else
{
lean_object* v___x_1684_; lean_object* v___x_1685_; 
v___x_1684_ = lean_unsigned_to_nat(0u);
v___x_1685_ = lean_array_fget_borrowed(v_args_1679_, v___x_1684_);
if (lean_obj_tag(v___x_1685_) == 2)
{
lean_object* v_val_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; 
v_val_1686_ = lean_ctor_get(v___x_1685_, 1);
v___x_1687_ = lean_string_length(v_val_1686_);
v___x_1688_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1688_, 0, v___x_1687_);
return v___x_1688_;
}
else
{
lean_object* v___x_1689_; 
v___x_1689_ = lean_box(0);
return v___x_1689_;
}
}
}
else
{
lean_object* v___x_1690_; 
v___x_1690_ = lean_box(0);
return v___x_1690_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength___boxed(lean_object* v_x_1691_){
_start:
{
lean_object* v_res_1692_; 
v_res_1692_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength(v_x_1691_);
lean_dec(v_x_1691_);
return v_res_1692_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0(uint32_t v_ch_1693_, lean_object* v_x_1694_, lean_object* v_x_1695_){
_start:
{
lean_object* v_zero_1696_; uint8_t v_isZero_1697_; 
v_zero_1696_ = lean_unsigned_to_nat(0u);
v_isZero_1697_ = lean_nat_dec_eq(v_x_1694_, v_zero_1696_);
if (v_isZero_1697_ == 1)
{
lean_dec(v_x_1694_);
return v_x_1695_;
}
else
{
lean_object* v_one_1698_; lean_object* v_n_1699_; lean_object* v___x_1700_; 
v_one_1698_ = lean_unsigned_to_nat(1u);
v_n_1699_ = lean_nat_sub(v_x_1694_, v_one_1698_);
lean_dec(v_x_1694_);
v___x_1700_ = lean_string_push(v_x_1695_, v_ch_1693_);
v_x_1694_ = v_n_1699_;
v_x_1695_ = v___x_1700_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0___boxed(lean_object* v_ch_1702_, lean_object* v_x_1703_, lean_object* v_x_1704_){
_start:
{
uint32_t v_ch_boxed_1705_; lean_object* v_res_1706_; 
v_ch_boxed_1705_ = lean_unbox_uint32(v_ch_1702_);
lean_dec(v_ch_1702_);
v_res_1706_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0(v_ch_boxed_1705_, v_x_1703_, v_x_1704_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths(lean_object* v_delim_1709_, uint32_t v_ch_1710_, lean_object* v_contents_1711_, lean_object* v_c_1712_, lean_object* v_s_1713_){
_start:
{
lean_object* v_fn_1714_; lean_object* v_s_1715_; lean_object* v_stxStack_1716_; lean_object* v_errorMsg_1717_; lean_object* v___x_1718_; uint8_t v___x_1719_; 
v_fn_1714_ = lean_ctor_get(v_delim_1709_, 1);
lean_inc_ref_n(v_fn_1714_, 2);
lean_dec_ref(v_delim_1709_);
lean_inc_ref(v_c_1712_);
v_s_1715_ = lean_apply_2(v_fn_1714_, v_c_1712_, v_s_1713_);
v_stxStack_1716_ = lean_ctor_get(v_s_1715_, 0);
lean_inc_ref(v_stxStack_1716_);
v_errorMsg_1717_ = lean_ctor_get(v_s_1715_, 4);
lean_inc(v_errorMsg_1717_);
v___x_1718_ = lean_box(0);
v___x_1719_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_1717_, v___x_1718_);
lean_dec(v_errorMsg_1717_);
if (v___x_1719_ == 0)
{
lean_dec_ref(v_stxStack_1716_);
lean_dec_ref(v_fn_1714_);
lean_dec_ref(v_c_1712_);
lean_dec_ref(v_contents_1711_);
return v_s_1715_;
}
else
{
lean_object* v_fn_1720_; lean_object* v_s_1721_; lean_object* v_pos_1722_; lean_object* v_errorMsg_1723_; uint8_t v___x_1724_; 
v_fn_1720_ = lean_ctor_get(v_contents_1711_, 1);
lean_inc_ref(v_fn_1720_);
lean_dec_ref(v_contents_1711_);
lean_inc_ref(v_c_1712_);
v_s_1721_ = lean_apply_2(v_fn_1720_, v_c_1712_, v_s_1715_);
v_pos_1722_ = lean_ctor_get(v_s_1721_, 2);
lean_inc(v_pos_1722_);
v_errorMsg_1723_ = lean_ctor_get(v_s_1721_, 4);
lean_inc(v_errorMsg_1723_);
v___x_1724_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_1723_, v___x_1718_);
lean_dec(v_errorMsg_1723_);
if (v___x_1724_ == 0)
{
lean_dec(v_pos_1722_);
lean_dec_ref(v_stxStack_1716_);
lean_dec_ref(v_fn_1714_);
lean_dec_ref(v_c_1712_);
return v_s_1721_;
}
else
{
lean_object* v_s_1725_; lean_object* v_stxStack_1726_; lean_object* v_errorMsg_1727_; uint8_t v___x_1728_; 
v_s_1725_ = lean_apply_2(v_fn_1714_, v_c_1712_, v_s_1721_);
v_stxStack_1726_ = lean_ctor_get(v_s_1725_, 0);
lean_inc_ref(v_stxStack_1726_);
v_errorMsg_1727_ = lean_ctor_get(v_s_1725_, 4);
lean_inc(v_errorMsg_1727_);
v___x_1728_ = l_instBEqOption_beq___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf_spec__1(v_errorMsg_1727_, v___x_1718_);
lean_dec(v_errorMsg_1727_);
if (v___x_1728_ == 0)
{
lean_dec_ref(v_stxStack_1726_);
lean_dec(v_pos_1722_);
lean_dec_ref(v_stxStack_1716_);
return v_s_1725_;
}
else
{
lean_object* v_opener_1729_; lean_object* v___x_1730_; 
v_opener_1729_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1716_);
lean_dec_ref(v_stxStack_1716_);
v___x_1730_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength(v_opener_1729_);
lean_dec(v_opener_1729_);
if (lean_obj_tag(v___x_1730_) == 1)
{
lean_object* v_val_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v_val_1731_ = lean_ctor_get(v___x_1730_, 0);
lean_inc(v_val_1731_);
lean_dec_ref_known(v___x_1730_, 1);
v___x_1732_ = l_Lean_Parser_SyntaxStack_back(v_stxStack_1726_);
lean_dec_ref(v_stxStack_1726_);
v___x_1733_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_runLength(v___x_1732_);
lean_dec(v___x_1732_);
if (lean_obj_tag(v___x_1733_) == 1)
{
lean_object* v_val_1734_; uint8_t v___x_1735_; 
v_val_1734_ = lean_ctor_get(v___x_1733_, 0);
lean_inc(v_val_1734_);
lean_dec_ref_known(v___x_1733_, 1);
v___x_1735_ = lean_nat_dec_eq(v_val_1731_, v_val_1734_);
lean_dec(v_val_1734_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1736_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf___lam__1___closed__0));
v___x_1737_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_unescapeVerso___closed__0));
v___x_1738_ = l___private_Init_Data_Nat_Basic_0__Nat_repeatTR_loop___at___00__private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths_spec__0(v_ch_1710_, v_val_1731_, v___x_1737_);
v___x_1739_ = lean_string_append(v___x_1736_, v___x_1738_);
v___x_1740_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___closed__0));
v___x_1741_ = lean_string_append(v___x_1739_, v___x_1740_);
v___x_1742_ = lean_string_append(v___x_1741_, v___x_1738_);
lean_dec_ref(v___x_1738_);
v___x_1743_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___closed__1));
v___x_1744_ = lean_string_append(v___x_1742_, v___x_1743_);
v___x_1745_ = l_Lean_Parser_ParserState_mkErrorAt(v_s_1725_, v___x_1744_, v_pos_1722_, v___x_1718_);
return v___x_1745_;
}
else
{
lean_dec(v_val_1731_);
lean_dec(v_pos_1722_);
return v_s_1725_;
}
}
else
{
lean_dec(v___x_1733_);
lean_dec(v_val_1731_);
lean_dec(v_pos_1722_);
return v_s_1725_;
}
}
else
{
lean_dec(v___x_1730_);
lean_dec_ref(v_stxStack_1726_);
lean_dec(v_pos_1722_);
return v_s_1725_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___boxed(lean_object* v_delim_1746_, lean_object* v_ch_1747_, lean_object* v_contents_1748_, lean_object* v_c_1749_, lean_object* v_s_1750_){
_start:
{
uint32_t v_ch_boxed_1751_; lean_object* v_res_1752_; 
v_ch_boxed_1751_ = lean_unbox_uint32(v_ch_1747_);
lean_dec(v_ch_1747_);
v_res_1752_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths(v_delim_1746_, v_ch_boxed_1751_, v_contents_1748_, v_c_1749_, v_s_1750_);
return v_res_1752_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__3___boxed__const__1(void){
_start:
{
uint32_t v___x_1761_; lean_object* v___x_1762_; 
v___x_1761_ = 96;
v___x_1762_ = lean_box_uint32(v___x_1761_);
return v___x_1762_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__3(void){
_start:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1763_ = ((lean_object*)(l_Lean_Doc_Parser_versoCode));
v___x_1764_ = ((lean_object*)(l_Lean_Doc_Parser_codeDelimiter));
v___x_1765_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__3___boxed__const__1;
v___x_1766_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___boxed), 5, 3);
lean_closure_set(v___x_1766_, 0, v___x_1764_);
lean_closure_set(v___x_1766_, 1, v___x_1765_);
lean_closure_set(v___x_1766_, 2, v___x_1763_);
return v___x_1766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2(lean_object* v___f_1767_, lean_object* v___f_1768_, lean_object* v_c_1769_, lean_object* v_s_1770_){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; uint8_t v___x_1777_; lean_object* v___x_1778_; lean_object* v_fn_1779_; lean_object* v___x_1780_; 
v___x_1771_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__0));
v___x_1772_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2));
v___x_1773_ = lean_box(1);
v___x_1774_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1774_, 0, v___f_1767_);
lean_ctor_set(v___x_1774_, 1, v___f_1768_);
lean_ctor_set(v___x_1774_, 2, v___x_1773_);
v___x_1775_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__3);
v___x_1776_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1776_, 0, v___x_1774_);
lean_ctor_set(v___x_1776_, 1, v___x_1775_);
v___x_1777_ = 0;
v___x_1778_ = l_Lean_Parser_nodeWithAntiquot(v___x_1771_, v___x_1772_, v___x_1776_, v___x_1777_);
v_fn_1779_ = lean_ctor_get(v___x_1778_, 1);
lean_inc_ref(v_fn_1779_);
lean_dec_ref(v___x_1778_);
v___x_1780_ = lean_apply_2(v_fn_1779_, v_c_1769_, v_s_1770_);
return v___x_1780_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2(void){
_start:
{
uint32_t v___x_1795_; lean_object* v___x_1796_; 
v___x_1795_ = 10;
v___x_1796_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_charRun(v___x_1795_);
return v___x_1796_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__3(void){
_start:
{
uint8_t v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1797_ = 0;
v___x_1798_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__2);
v___x_1799_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__1));
v___x_1800_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__0));
v___x_1801_ = l_Lean_Parser_nodeWithAntiquot(v___x_1800_, v___x_1799_, v___x_1798_, v___x_1797_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot(lean_object* v_a_1802_, lean_object* v_a_1803_){
_start:
{
lean_object* v___x_1804_; lean_object* v_fn_1805_; lean_object* v___x_1806_; 
v___x_1804_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot___closed__3);
v_fn_1805_ = lean_ctor_get(v___x_1804_, 1);
lean_inc_ref(v_fn_1805_);
v___x_1806_ = lean_apply_2(v_fn_1805_, v_a_1802_, v_a_1803_);
return v___x_1806_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; 
v___x_1815_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__2));
v___x_1816_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_1815_);
return v___x_1816_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4(void){
_start:
{
lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1817_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__4));
v___x_1818_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_1817_);
return v___x_1818_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5(void){
_start:
{
lean_object* v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1819_ = ((lean_object*)(l_Lean_Doc_Parser_linkTarget));
v___x_1820_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4);
v___x_1821_ = l_Lean_Parser_andthen(v___x_1820_, v___x_1819_);
return v___x_1821_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6(void){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5);
v___x_1823_ = ((lean_object*)(l_Lean_Doc_Parser_versoImageAlt));
v___x_1824_ = l_Lean_Parser_andthen(v___x_1823_, v___x_1822_);
return v___x_1824_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7(void){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1825_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__6);
v___x_1826_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__3);
v___x_1827_ = l_Lean_Parser_andthen(v___x_1826_, v___x_1825_);
return v___x_1827_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__8(void){
_start:
{
uint8_t v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1828_ = 0;
v___x_1829_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__7);
v___x_1830_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1));
v___x_1831_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__0));
v___x_1832_ = l_Lean_Parser_nodeWithAntiquot(v___x_1831_, v___x_1830_, v___x_1829_, v___x_1828_);
return v___x_1832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot(lean_object* v_a_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v___x_1835_; lean_object* v_fn_1836_; lean_object* v___x_1837_; 
v___x_1835_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__8, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__8_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__8);
v_fn_1836_ = lean_ctor_get(v___x_1835_, 1);
lean_inc_ref(v_fn_1836_);
v___x_1837_ = lean_apply_2(v_fn_1836_, v_a_1833_, v_a_1834_);
return v___x_1837_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; 
v___x_1846_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__2));
v___x_1847_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_1846_);
return v___x_1847_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4(void){
_start:
{
lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1848_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4);
v___x_1849_ = ((lean_object*)(l_Lean_Doc_Parser_versoRef));
v___x_1850_ = l_Lean_Parser_andthen(v___x_1849_, v___x_1848_);
return v___x_1850_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__5(void){
_start:
{
lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1851_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__4);
v___x_1852_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3);
v___x_1853_ = l_Lean_Parser_andthen(v___x_1852_, v___x_1851_);
return v___x_1853_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__6(void){
_start:
{
uint8_t v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1854_ = 0;
v___x_1855_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__5);
v___x_1856_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1));
v___x_1857_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__0));
v___x_1858_ = l_Lean_Parser_nodeWithAntiquot(v___x_1857_, v___x_1856_, v___x_1855_, v___x_1854_);
return v___x_1858_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot(lean_object* v_a_1859_, lean_object* v_a_1860_){
_start:
{
lean_object* v___x_1861_; lean_object* v_fn_1862_; lean_object* v___x_1863_; 
v___x_1861_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__6);
v_fn_1862_ = lean_ctor_get(v___x_1861_, 1);
lean_inc_ref(v_fn_1862_);
v___x_1863_ = lean_apply_2(v_fn_1862_, v_a_1859_, v_a_1860_);
return v___x_1863_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2(void){
_start:
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; 
v___x_1871_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode));
v___x_1872_ = ((lean_object*)(l_Lean_Doc_Parser_inlineMathMarker));
v___x_1873_ = l_Lean_Parser_andthen(v___x_1872_, v___x_1871_);
return v___x_1873_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__3(void){
_start:
{
uint8_t v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1874_ = 0;
v___x_1875_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__2);
v___x_1876_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1));
v___x_1877_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__0));
v___x_1878_ = l_Lean_Parser_nodeWithAntiquot(v___x_1877_, v___x_1876_, v___x_1875_, v___x_1874_);
return v___x_1878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot(lean_object* v_a_1879_, lean_object* v_a_1880_){
_start:
{
lean_object* v___x_1881_; lean_object* v_fn_1882_; lean_object* v___x_1883_; 
v___x_1881_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__3);
v_fn_1882_ = lean_ctor_get(v___x_1881_, 1);
lean_inc_ref(v_fn_1882_);
v___x_1883_ = lean_apply_2(v_fn_1882_, v_a_1879_, v_a_1880_);
return v___x_1883_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2(void){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode));
v___x_1892_ = ((lean_object*)(l_Lean_Doc_Parser_displayMathMarker));
v___x_1893_ = l_Lean_Parser_andthen(v___x_1892_, v___x_1891_);
return v___x_1893_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__3(void){
_start:
{
uint8_t v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1894_ = 0;
v___x_1895_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__2);
v___x_1896_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1));
v___x_1897_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__0));
v___x_1898_ = l_Lean_Parser_nodeWithAntiquot(v___x_1897_, v___x_1896_, v___x_1895_, v___x_1894_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot(lean_object* v_a_1899_, lean_object* v_a_1900_){
_start:
{
lean_object* v___x_1901_; lean_object* v_fn_1902_; lean_object* v___x_1903_; 
v___x_1901_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__3);
v_fn_1902_ = lean_ctor_get(v___x_1901_, 1);
lean_inc_ref(v_fn_1902_);
v___x_1903_ = lean_apply_2(v_fn_1902_, v_a_1899_, v_a_1900_);
return v___x_1903_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0(void){
_start:
{
lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v___x_1904_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot), 2, 0);
v___x_1905_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
lean_ctor_set(v___x_1906_, 1, v___x_1904_);
return v___x_1906_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1(void){
_start:
{
lean_object* v___x_1907_; lean_object* v___x_1908_; 
v___x_1907_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0);
v___x_1908_ = l_Lean_Parser_atomic(v___x_1907_);
return v___x_1908_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2(void){
_start:
{
lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1909_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot), 2, 0);
v___x_1910_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_1911_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1911_, 0, v___x_1910_);
lean_ctor_set(v___x_1911_, 1, v___x_1909_);
return v___x_1911_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3(void){
_start:
{
lean_object* v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; 
v___x_1912_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2);
v___x_1913_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__1);
v___x_1914_ = l_Lean_Parser_orelse(v___x_1913_, v___x_1912_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot(lean_object* v_a_1915_, lean_object* v_a_1916_){
_start:
{
lean_object* v___x_1917_; lean_object* v_fn_1918_; lean_object* v___x_1919_; 
v___x_1917_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__3);
v_fn_1918_ = lean_ctor_get(v___x_1917_, 1);
lean_inc_ref(v_fn_1918_);
v___x_1919_ = lean_apply_2(v_fn_1918_, v_a_1915_, v_a_1916_);
return v___x_1919_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__2(void){
_start:
{
uint8_t v___x_1927_; lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1927_ = 0;
v___x_1928_ = ((lean_object*)(l_Lean_Doc_Parser_versoText));
v___x_1929_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__1));
v___x_1930_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__0));
v___x_1931_ = l_Lean_Parser_nodeWithAntiquot(v___x_1930_, v___x_1929_, v___x_1928_, v___x_1927_);
return v___x_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot(lean_object* v_a_1932_, lean_object* v_a_1933_){
_start:
{
lean_object* v___x_1934_; lean_object* v_fn_1935_; lean_object* v___x_1936_; 
v___x_1934_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot___closed__2);
v_fn_1935_ = lean_ctor_get(v___x_1934_, 1);
lean_inc_ref(v_fn_1935_);
v___x_1936_ = lean_apply_2(v_fn_1935_, v_a_1932_, v_a_1933_);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0(lean_object* v___y_1937_){
_start:
{
lean_inc(v___y_1937_);
return v___y_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0___boxed(lean_object* v___y_1938_){
_start:
{
lean_object* v_res_1939_; 
v_res_1939_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__0(v___y_1938_);
lean_dec(v___y_1938_);
return v_res_1939_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1(lean_object* v___y_1940_){
_start:
{
lean_inc_ref(v___y_1940_);
return v___y_1940_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1___boxed(lean_object* v___y_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___lam__1(v___y_1941_);
lean_dec_ref(v___y_1941_);
return v_res_1942_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___boxed__const__1(void){
_start:
{
uint32_t v___x_1956_; lean_object* v___x_1957_; 
v___x_1956_ = 42;
v___x_1957_ = lean_box_uint32(v___x_1956_);
return v___x_1957_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0(void){
_start:
{
lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1958_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot), 2, 0);
v___x_1959_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_1960_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1960_, 0, v___x_1959_);
lean_ctor_set(v___x_1960_, 1, v___x_1958_);
return v___x_1960_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___boxed__const__1(void){
_start:
{
uint32_t v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = 95;
v___x_1969_ = lean_box_uint32(v___x_1968_);
return v___x_1969_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot(lean_object* v_a_1970_, lean_object* v_a_1971_){
_start:
{
lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; uint8_t v___x_1983_; lean_object* v___x_1984_; lean_object* v_fn_1985_; lean_object* v___x_1986_; 
v___x_1972_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__0));
v___x_1973_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__1));
v___x_1974_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_1975_ = ((lean_object*)(l_Lean_Doc_Parser_emphDelimiter));
v___x_1976_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot), 2, 0);
v___x_1977_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1977_, 0, v___x_1974_);
lean_ctor_set(v___x_1977_, 1, v___x_1976_);
v___x_1978_ = l_Lean_Parser_atomic(v___x_1977_);
v___x_1979_ = l_Lean_Parser_many(v___x_1978_);
v___x_1980_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___boxed__const__1;
v___x_1981_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___boxed), 5, 3);
lean_closure_set(v___x_1981_, 0, v___x_1975_);
lean_closure_set(v___x_1981_, 1, v___x_1980_);
lean_closure_set(v___x_1981_, 2, v___x_1979_);
v___x_1982_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1982_, 0, v___x_1974_);
lean_ctor_set(v___x_1982_, 1, v___x_1981_);
v___x_1983_ = 0;
v___x_1984_ = l_Lean_Parser_nodeWithAntiquot(v___x_1972_, v___x_1973_, v___x_1982_, v___x_1983_);
v_fn_1985_ = lean_ctor_get(v___x_1984_, 1);
lean_inc_ref(v_fn_1985_);
lean_dec_ref(v___x_1984_);
v___x_1986_ = lean_apply_2(v_fn_1985_, v_a_1970_, v_a_1971_);
return v___x_1986_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1(void){
_start:
{
lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1987_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot), 2, 0);
v___x_1988_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_1989_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1989_, 0, v___x_1988_);
lean_ctor_set(v___x_1989_, 1, v___x_1987_);
return v___x_1989_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2(void){
_start:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1990_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot), 2, 0);
v___x_1991_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_1992_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1992_, 0, v___x_1991_);
lean_ctor_set(v___x_1992_, 1, v___x_1990_);
return v___x_1992_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__2(void){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_2000_ = ((lean_object*)(l_Lean_Doc_Parser_LinkTarget_ref___lam__0___closed__2));
v___x_2001_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot(lean_object* v_a_2002_, lean_object* v_a_2003_){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; lean_object* v___x_2013_; lean_object* v___x_2014_; uint8_t v___x_2015_; lean_object* v___x_2016_; lean_object* v_fn_2017_; lean_object* v___x_2018_; 
v___x_2004_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__0));
v___x_2005_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1));
v___x_2006_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__2);
v___x_2007_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2008_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot), 2, 0);
v___x_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2009_, 0, v___x_2007_);
lean_ctor_set(v___x_2009_, 1, v___x_2008_);
v___x_2010_ = l_Lean_Parser_atomic(v___x_2009_);
v___x_2011_ = l_Lean_Parser_many(v___x_2010_);
v___x_2012_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__5);
v___x_2013_ = l_Lean_Parser_andthen(v___x_2011_, v___x_2012_);
v___x_2014_ = l_Lean_Parser_andthen(v___x_2006_, v___x_2013_);
v___x_2015_ = 0;
v___x_2016_ = l_Lean_Parser_nodeWithAntiquot(v___x_2004_, v___x_2005_, v___x_2014_, v___x_2015_);
v_fn_2017_ = lean_ctor_get(v___x_2016_, 1);
lean_inc_ref(v_fn_2017_);
lean_dec_ref(v___x_2016_);
v___x_2018_ = lean_apply_2(v_fn_2017_, v_a_2002_, v_a_2003_);
return v___x_2018_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2019_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot), 2, 0);
v___x_2020_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2021_, 0, v___x_2020_);
lean_ctor_set(v___x_2021_, 1, v___x_2019_);
return v___x_2021_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6(void){
_start:
{
uint8_t v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; lean_object* v___x_2031_; 
v___x_2028_ = 1;
v___x_2029_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__5));
v___x_2030_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__4));
v___x_2031_ = l_Lean_Parser_mkAntiquot(v___x_2030_, v___x_2029_, v___x_2028_, v___x_2028_);
return v___x_2031_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__7(void){
_start:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2034_; 
v___x_2032_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot), 2, 0);
v___x_2033_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2034_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2034_, 0, v___x_2033_);
lean_ctor_set(v___x_2034_, 1, v___x_2032_);
return v___x_2034_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3(void){
_start:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__2));
v___x_2044_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2043_);
return v___x_2044_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4(void){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = ((lean_object*)(l_Lean_Doc_Parser_arg));
v___x_2046_ = l_Lean_Parser_many(v___x_2045_);
return v___x_2046_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6(void){
_start:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; 
v___x_2048_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__5));
v___x_2049_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2048_);
return v___x_2049_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__9(void){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; 
v___x_2053_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__2);
v___x_2054_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8));
v___x_2055_ = l_Lean_Parser_node(v___x_2054_, v___x_2053_);
return v___x_2055_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__10(void){
_start:
{
lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; 
v___x_2056_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__4);
v___x_2057_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8));
v___x_2058_ = l_Lean_Parser_node(v___x_2057_, v___x_2056_);
return v___x_2058_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__11(void){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___x_2059_ = l_Lean_Parser_skip;
v___x_2060_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__8));
v___x_2061_ = l_Lean_Parser_node(v___x_2060_, v___x_2059_);
return v___x_2061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot(lean_object* v_a_2062_, lean_object* v_a_2063_){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; uint8_t v___x_2088_; lean_object* v___x_2089_; lean_object* v_fn_2090_; lean_object* v___x_2091_; 
v___x_2064_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__0));
v___x_2065_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1));
v___x_2066_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3);
v___x_2067_ = l_Lean_Parser_ident;
v___x_2068_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4);
v___x_2069_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6);
v___x_2070_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__9, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__9_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__9);
v___x_2071_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2072_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot), 2, 0);
v___x_2073_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2073_, 0, v___x_2071_);
lean_ctor_set(v___x_2073_, 1, v___x_2072_);
v___x_2074_ = l_Lean_Parser_atomic(v___x_2073_);
lean_inc_ref(v___x_2074_);
v___x_2075_ = l_Lean_Parser_many(v___x_2074_);
v___x_2076_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__10, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__10_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__10);
v___x_2077_ = l_Lean_Parser_andthen(v___x_2075_, v___x_2076_);
v___x_2078_ = l_Lean_Parser_andthen(v___x_2070_, v___x_2077_);
v___x_2079_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__11, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__11_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__11);
v___x_2080_ = l_Lean_Parser_many1(v___x_2074_);
v___x_2081_ = l_Lean_Parser_andthen(v___x_2080_, v___x_2079_);
v___x_2082_ = l_Lean_Parser_andthen(v___x_2079_, v___x_2081_);
v___x_2083_ = l_Lean_Parser_orelse(v___x_2078_, v___x_2082_);
v___x_2084_ = l_Lean_Parser_andthen(v___x_2069_, v___x_2083_);
v___x_2085_ = l_Lean_Parser_andthen(v___x_2068_, v___x_2084_);
v___x_2086_ = l_Lean_Parser_andthen(v___x_2067_, v___x_2085_);
v___x_2087_ = l_Lean_Parser_andthen(v___x_2066_, v___x_2086_);
v___x_2088_ = 0;
v___x_2089_ = l_Lean_Parser_nodeWithAntiquot(v___x_2064_, v___x_2065_, v___x_2087_, v___x_2088_);
v_fn_2090_ = lean_ctor_get(v___x_2089_, 1);
lean_inc_ref(v_fn_2090_);
lean_dec_ref(v___x_2089_);
v___x_2091_ = lean_apply_2(v_fn_2090_, v_a_2062_, v_a_2063_);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot(lean_object* v_c_2092_, lean_object* v_s_2093_){
_start:
{
lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; lean_object* v___x_2101_; lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v_fn_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v_alts_2119_; lean_object* v_fn_2120_; uint8_t v___x_2121_; lean_object* v___x_2122_; 
v___x_2094_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2095_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__0);
v___x_2096_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot), 2, 0);
v___x_2097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2097_, 0, v___x_2094_);
lean_ctor_set(v___x_2097_, 1, v___x_2096_);
v___x_2098_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot), 2, 0);
v___x_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2099_, 0, v___x_2094_);
lean_ctor_set(v___x_2099_, 1, v___x_2098_);
v___x_2100_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__1);
v___x_2101_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__2);
v___x_2102_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot), 2, 0);
v___x_2103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2103_, 0, v___x_2094_);
lean_ctor_set(v___x_2103_, 1, v___x_2102_);
v___x_2104_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__3);
v___x_2105_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__6);
v_fn_2106_ = lean_ctor_get(v___x_2105_, 1);
v___x_2107_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__7, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__7_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot___closed__7);
v___x_2108_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode));
v___x_2109_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot), 2, 0);
v___x_2110_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2094_);
lean_ctor_set(v___x_2110_, 1, v___x_2109_);
v___x_2111_ = l_Lean_Parser_orelse(v___x_2107_, v___x_2110_);
v___x_2112_ = l_Lean_Parser_orelse(v___x_2104_, v___x_2111_);
v___x_2113_ = l_Lean_Parser_orelse(v___x_2103_, v___x_2112_);
v___x_2114_ = l_Lean_Parser_orelse(v___x_2101_, v___x_2113_);
v___x_2115_ = l_Lean_Parser_orelse(v___x_2100_, v___x_2114_);
v___x_2116_ = l_Lean_Parser_orelse(v___x_2108_, v___x_2115_);
v___x_2117_ = l_Lean_Parser_orelse(v___x_2099_, v___x_2116_);
v___x_2118_ = l_Lean_Parser_orelse(v___x_2097_, v___x_2117_);
v_alts_2119_ = l_Lean_Parser_orelse(v___x_2095_, v___x_2118_);
v_fn_2120_ = lean_ctor_get(v_alts_2119_, 1);
lean_inc_ref(v_fn_2120_);
lean_dec_ref(v_alts_2119_);
v___x_2121_ = 0;
lean_inc_ref(v_fn_2106_);
v___x_2122_ = l_Lean_Parser_withAntiquotFn(v_fn_2106_, v_fn_2120_, v___x_2121_, v_c_2092_, v_s_2093_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot(lean_object* v_a_2123_, lean_object* v_a_2124_){
_start:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; lean_object* v___x_2127_; lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; uint8_t v___x_2136_; lean_object* v___x_2137_; lean_object* v_fn_2138_; lean_object* v___x_2139_; 
v___x_2125_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__2));
v___x_2126_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_2127_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2128_ = ((lean_object*)(l_Lean_Doc_Parser_boldDelimiter));
v___x_2129_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineQuot), 2, 0);
v___x_2130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2130_, 0, v___x_2127_);
lean_ctor_set(v___x_2130_, 1, v___x_2129_);
v___x_2131_ = l_Lean_Parser_atomic(v___x_2130_);
v___x_2132_ = l_Lean_Parser_many(v___x_2131_);
v___x_2133_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___boxed__const__1;
v___x_2134_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_matchingDelimiterLengths___boxed), 5, 3);
lean_closure_set(v___x_2134_, 0, v___x_2128_);
lean_closure_set(v___x_2134_, 1, v___x_2133_);
lean_closure_set(v___x_2134_, 2, v___x_2132_);
v___x_2135_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2135_, 0, v___x_2127_);
lean_ctor_set(v___x_2135_, 1, v___x_2134_);
v___x_2136_ = 0;
v___x_2137_ = l_Lean_Parser_nodeWithAntiquot(v___x_2125_, v___x_2126_, v___x_2135_, v___x_2136_);
v_fn_2138_ = lean_ctor_get(v___x_2137_, 1);
lean_inc_ref(v_fn_2138_);
lean_dec_ref(v___x_2137_);
v___x_2139_ = lean_apply_2(v_fn_2138_, v_a_2123_, v_a_2124_);
return v___x_2139_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_text___closed__0(void){
_start:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; 
v___x_2140_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_textQuot), 2, 0);
v___x_2141_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2142_, 0, v___x_2141_);
lean_ctor_set(v___x_2142_, 1, v___x_2140_);
return v___x_2142_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_text(void){
_start:
{
lean_object* v___x_2143_; 
v___x_2143_ = lean_obj_once(&l_Lean_Doc_Parser_Inline_text___closed__0, &l_Lean_Doc_Parser_Inline_text___closed__0_once, _init_l_Lean_Doc_Parser_Inline_text___closed__0);
return v___x_2143_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1(){
_start:
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
v___x_2151_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_emphQuot___closed__1));
v___x_2152_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1___closed__0));
v___x_2153_ = l_Lean_addBuiltinDocString(v___x_2151_, v___x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1___boxed(lean_object* v_a_2154_){
_start:
{
lean_object* v_res_2155_; 
v_res_2155_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_emph___regBuiltin_Lean_Doc_Parser_Inline_emph_docString__1();
return v_res_2155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1(){
_start:
{
lean_object* v___x_2163_; lean_object* v___x_2164_; lean_object* v___x_2165_; 
v___x_2163_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__3));
v___x_2164_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1___closed__0));
v___x_2165_ = l_Lean_addBuiltinDocString(v___x_2163_, v___x_2164_);
return v___x_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1___boxed(lean_object* v_a_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_bold___regBuiltin_Lean_Doc_Parser_Inline_bold_docString__1();
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1(){
_start:
{
lean_object* v___x_2171_; lean_object* v___x_2172_; lean_object* v___x_2173_; 
v___x_2171_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineCode___lam__2___closed__2));
v___x_2172_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1___closed__0));
v___x_2173_ = l_Lean_addBuiltinDocString(v___x_2171_, v___x_2172_);
return v___x_2173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1___boxed(lean_object* v_a_2174_){
_start:
{
lean_object* v_res_2175_; 
v_res_2175_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_code___regBuiltin_Lean_Doc_Parser_Inline_code_docString__1();
return v_res_2175_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_inline__math(void){
_start:
{
lean_object* v___x_2176_; 
v___x_2176_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__2);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1(){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2179_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_inlineMathQuot___closed__1));
v___x_2180_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1___closed__0));
v___x_2181_ = l_Lean_addBuiltinDocString(v___x_2179_, v___x_2180_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1___boxed(lean_object* v_a_2182_){
_start:
{
lean_object* v_res_2183_; 
v_res_2183_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_inline__math___regBuiltin_Lean_Doc_Parser_Inline_inline__math_docString__1();
return v_res_2183_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_display__math(void){
_start:
{
lean_object* v___x_2184_; 
v___x_2184_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_mathQuot___closed__0);
return v___x_2184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1(){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; 
v___x_2187_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_displayMathQuot___closed__1));
v___x_2188_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1___closed__0));
v___x_2189_ = l_Lean_addBuiltinDocString(v___x_2187_, v___x_2188_);
return v___x_2189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1___boxed(lean_object* v_a_2190_){
_start:
{
lean_object* v_res_2191_; 
v_res_2191_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_display__math___regBuiltin_Lean_Doc_Parser_Inline_display__math_docString__1();
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1(){
_start:
{
lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; 
v___x_2199_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__1));
v___x_2200_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1___closed__0));
v___x_2201_ = l_Lean_addBuiltinDocString(v___x_2199_, v___x_2200_);
return v___x_2201_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1___boxed(lean_object* v_a_2202_){
_start:
{
lean_object* v_res_2203_; 
v_res_2203_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_link___regBuiltin_Lean_Doc_Parser_Inline_link_docString__1();
return v_res_2203_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_image___closed__0(void){
_start:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2204_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot), 2, 0);
v___x_2205_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
lean_ctor_set(v___x_2206_, 1, v___x_2204_);
return v___x_2206_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_image(void){
_start:
{
lean_object* v___x_2207_; 
v___x_2207_ = lean_obj_once(&l_Lean_Doc_Parser_Inline_image___closed__0, &l_Lean_Doc_Parser_Inline_image___closed__0_once, _init_l_Lean_Doc_Parser_Inline_image___closed__0);
return v___x_2207_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1(){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_imageQuot___closed__1));
v___x_2211_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1___closed__0));
v___x_2212_ = l_Lean_addBuiltinDocString(v___x_2210_, v___x_2211_);
return v___x_2212_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1___boxed(lean_object* v_a_2213_){
_start:
{
lean_object* v_res_2214_; 
v_res_2214_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_image___regBuiltin_Lean_Doc_Parser_Inline_image_docString__1();
return v_res_2214_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_footnote___closed__0(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; 
v___x_2215_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot), 2, 0);
v___x_2216_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2217_, 0, v___x_2216_);
lean_ctor_set(v___x_2217_, 1, v___x_2215_);
return v___x_2217_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_footnote(void){
_start:
{
lean_object* v___x_2218_; 
v___x_2218_ = lean_obj_once(&l_Lean_Doc_Parser_Inline_footnote___closed__0, &l_Lean_Doc_Parser_Inline_footnote___closed__0_once, _init_l_Lean_Doc_Parser_Inline_footnote___closed__0);
return v___x_2218_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1(){
_start:
{
lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; 
v___x_2221_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__1));
v___x_2222_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1___closed__0));
v___x_2223_ = l_Lean_addBuiltinDocString(v___x_2221_, v___x_2222_);
return v___x_2223_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1___boxed(lean_object* v_a_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_footnote___regBuiltin_Lean_Doc_Parser_Inline_footnote_docString__1();
return v_res_2225_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_linebreak___closed__0(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; lean_object* v___x_2228_; 
v___x_2226_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linebreakQuot), 2, 0);
v___x_2227_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2228_, 0, v___x_2227_);
lean_ctor_set(v___x_2228_, 1, v___x_2226_);
return v___x_2228_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Inline_linebreak(void){
_start:
{
lean_object* v___x_2229_; 
v___x_2229_ = lean_obj_once(&l_Lean_Doc_Parser_Inline_linebreak___closed__0, &l_Lean_Doc_Parser_Inline_linebreak___closed__0_once, _init_l_Lean_Doc_Parser_Inline_linebreak___closed__0);
return v___x_2229_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1(){
_start:
{
lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; 
v___x_2237_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__1));
v___x_2238_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1___closed__0));
v___x_2239_ = l_Lean_addBuiltinDocString(v___x_2237_, v___x_2238_);
return v___x_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1___boxed(lean_object* v_a_2240_){
_start:
{
lean_object* v_res_2241_; 
v_res_2241_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Inline_role___regBuiltin_Lean_Doc_Parser_Inline_role_docString__1();
return v_res_2241_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3(void){
_start:
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
v___x_2255_ = ((lean_object*)(l_Lean_Doc_Parser_inline___closed__1));
v___x_2256_ = l_Lean_Parser_atomic(v___x_2255_);
return v___x_2256_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4(void){
_start:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; 
v___x_2257_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3);
v___x_2258_ = l_Lean_Parser_many1(v___x_2257_);
return v___x_2258_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__5(void){
_start:
{
uint8_t v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2259_ = 0;
v___x_2260_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4);
v___x_2261_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2));
v___x_2262_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__0));
v___x_2263_ = l_Lean_Parser_nodeWithAntiquot(v___x_2262_, v___x_2261_, v___x_2260_, v___x_2259_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot(lean_object* v_a_2264_, lean_object* v_a_2265_){
_start:
{
lean_object* v___x_2266_; lean_object* v_fn_2267_; lean_object* v___x_2268_; 
v___x_2266_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__5);
v_fn_2267_ = lean_ctor_get(v___x_2266_, 1);
lean_inc_ref(v_fn_2267_);
v___x_2268_ = lean_apply_2(v_fn_2267_, v_a_2264_, v_a_2265_);
return v___x_2268_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2(void){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; lean_object* v___x_2278_; 
v___x_2276_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__6);
v___x_2277_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4);
v___x_2278_ = l_Lean_Parser_andthen(v___x_2277_, v___x_2276_);
return v___x_2278_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3(void){
_start:
{
lean_object* v___x_2279_; lean_object* v___x_2280_; lean_object* v___x_2281_; 
v___x_2279_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__2);
v___x_2280_ = l_Lean_Parser_ident;
v___x_2281_ = l_Lean_Parser_andthen(v___x_2280_, v___x_2279_);
return v___x_2281_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4(void){
_start:
{
lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2282_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__3);
v___x_2283_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__3);
v___x_2284_ = l_Lean_Parser_andthen(v___x_2283_, v___x_2282_);
return v___x_2284_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__5(void){
_start:
{
uint8_t v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; 
v___x_2285_ = 0;
v___x_2286_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__4);
v___x_2287_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1));
v___x_2288_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__0));
v___x_2289_ = l_Lean_Parser_nodeWithAntiquot(v___x_2288_, v___x_2287_, v___x_2286_, v___x_2285_);
return v___x_2289_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot(lean_object* v_a_2290_, lean_object* v_a_2291_){
_start:
{
lean_object* v___x_2292_; lean_object* v_fn_2293_; lean_object* v___x_2294_; 
v___x_2292_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__5);
v_fn_2293_ = lean_ctor_get(v___x_2292_, 1);
lean_inc_ref(v_fn_2293_);
v___x_2294_ = lean_apply_2(v_fn_2293_, v_a_2290_, v_a_2291_);
return v___x_2294_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2(void){
_start:
{
lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2302_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit___lam__0___closed__0));
v___x_2303_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2302_);
return v___x_2303_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3(void){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2304_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2);
v___x_2305_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataContentsLit));
v___x_2306_ = l_Lean_Parser_andthen(v___x_2305_, v___x_2304_);
return v___x_2306_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4(void){
_start:
{
lean_object* v___x_2307_; lean_object* v___x_2308_; lean_object* v___x_2309_; 
v___x_2307_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__3);
v___x_2308_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__2);
v___x_2309_ = l_Lean_Parser_andthen(v___x_2308_, v___x_2307_);
return v___x_2309_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__5(void){
_start:
{
uint8_t v___x_2310_; lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2310_ = 0;
v___x_2311_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__4);
v___x_2312_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1));
v___x_2313_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__0));
v___x_2314_ = l_Lean_Parser_nodeWithAntiquot(v___x_2313_, v___x_2312_, v___x_2311_, v___x_2310_);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot(lean_object* v_a_2315_, lean_object* v_a_2316_){
_start:
{
lean_object* v___x_2317_; lean_object* v_fn_2318_; lean_object* v___x_2319_; 
v___x_2317_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__5);
v_fn_2318_ = lean_ctor_get(v___x_2317_, 1);
lean_inc_ref(v_fn_2318_);
v___x_2319_ = lean_apply_2(v_fn_2318_, v_a_2315_, v_a_2316_);
return v___x_2319_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3(void){
_start:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2328_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__2));
v___x_2329_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2328_);
return v___x_2329_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4(void){
_start:
{
lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; 
v___x_2330_ = ((lean_object*)(l_Lean_Doc_Parser_versoLinkRefUrl));
v___x_2331_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3);
v___x_2332_ = l_Lean_Parser_andthen(v___x_2331_, v___x_2330_);
return v___x_2332_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5(void){
_start:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; 
v___x_2333_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__4);
v___x_2334_ = ((lean_object*)(l_Lean_Doc_Parser_versoRef));
v___x_2335_ = l_Lean_Parser_andthen(v___x_2334_, v___x_2333_);
return v___x_2335_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__6(void){
_start:
{
lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; 
v___x_2336_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__5);
v___x_2337_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkQuot___closed__2);
v___x_2338_ = l_Lean_Parser_andthen(v___x_2337_, v___x_2336_);
return v___x_2338_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__7(void){
_start:
{
uint8_t v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; 
v___x_2339_ = 0;
v___x_2340_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__6);
v___x_2341_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1));
v___x_2342_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__0));
v___x_2343_ = l_Lean_Parser_nodeWithAntiquot(v___x_2342_, v___x_2341_, v___x_2340_, v___x_2339_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot(lean_object* v_a_2344_, lean_object* v_a_2345_){
_start:
{
lean_object* v___x_2346_; lean_object* v_fn_2347_; lean_object* v___x_2348_; 
v___x_2346_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__7, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__7_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__7);
v_fn_2347_ = lean_ctor_get(v___x_2346_, 1);
lean_inc_ref(v_fn_2347_);
v___x_2348_ = lean_apply_2(v_fn_2347_, v_a_2344_, v_a_2345_);
return v___x_2348_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2(void){
_start:
{
lean_object* v___x_2356_; lean_object* v___x_2357_; 
v___x_2356_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__3);
v___x_2357_ = l_Lean_Parser_many(v___x_2356_);
return v___x_2357_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3(void){
_start:
{
lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2360_; 
v___x_2358_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__2);
v___x_2359_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__3);
v___x_2360_ = l_Lean_Parser_andthen(v___x_2359_, v___x_2358_);
return v___x_2360_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4(void){
_start:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
v___x_2361_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__3);
v___x_2362_ = ((lean_object*)(l_Lean_Doc_Parser_versoRef));
v___x_2363_ = l_Lean_Parser_andthen(v___x_2362_, v___x_2361_);
return v___x_2363_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5(void){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; lean_object* v___x_2366_; 
v___x_2364_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__4);
v___x_2365_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteQuot___closed__3);
v___x_2366_ = l_Lean_Parser_andthen(v___x_2365_, v___x_2364_);
return v___x_2366_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__6(void){
_start:
{
uint8_t v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v___x_2367_ = 0;
v___x_2368_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__5);
v___x_2369_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1));
v___x_2370_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__0));
v___x_2371_ = l_Lean_Parser_nodeWithAntiquot(v___x_2370_, v___x_2369_, v___x_2368_, v___x_2367_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot(lean_object* v_a_2372_, lean_object* v_a_2373_){
_start:
{
lean_object* v___x_2374_; lean_object* v_fn_2375_; lean_object* v___x_2376_; 
v___x_2374_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__6);
v_fn_2375_ = lean_ctor_get(v___x_2374_, 1);
lean_inc_ref(v_fn_2375_);
v___x_2376_ = lean_apply_2(v_fn_2375_, v_a_2372_, v_a_2373_);
return v___x_2376_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2(void){
_start:
{
lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; 
v___x_2384_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__4);
v___x_2385_ = ((lean_object*)(l_Lean_Doc_Parser_headerMarker));
v___x_2386_ = l_Lean_Parser_andthen(v___x_2385_, v___x_2384_);
return v___x_2386_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__3(void){
_start:
{
uint8_t v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; lean_object* v___x_2390_; lean_object* v___x_2391_; 
v___x_2387_ = 0;
v___x_2388_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__2);
v___x_2389_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1));
v___x_2390_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__0));
v___x_2391_ = l_Lean_Parser_nodeWithAntiquot(v___x_2390_, v___x_2389_, v___x_2388_, v___x_2387_);
return v___x_2391_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot(lean_object* v_a_2392_, lean_object* v_a_2393_){
_start:
{
lean_object* v___x_2394_; lean_object* v_fn_2395_; lean_object* v___x_2396_; 
v___x_2394_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__3);
v_fn_2395_ = lean_ctor_get(v___x_2394_, 1);
lean_inc_ref(v_fn_2395_);
v___x_2396_ = lean_apply_2(v_fn_2395_, v_a_2392_, v_a_2393_);
return v___x_2396_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2(void){
_start:
{
lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v___x_2404_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4);
v___x_2405_ = l_Lean_Parser_ident;
v___x_2406_ = l_Lean_Parser_andthen(v___x_2405_, v___x_2404_);
return v___x_2406_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3(void){
_start:
{
lean_object* v___x_2407_; lean_object* v___x_2408_; 
v___x_2407_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__2);
v___x_2408_ = l_Lean_Parser_optional(v___x_2407_);
return v___x_2408_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4(void){
_start:
{
lean_object* v___x_2409_; lean_object* v___x_2410_; lean_object* v___x_2411_; 
v___x_2409_ = ((lean_object*)(l_Lean_Doc_Parser_codeBlockFence));
v___x_2410_ = ((lean_object*)(l_Lean_Doc_Parser_versoCodeBlock));
v___x_2411_ = l_Lean_Parser_andthen(v___x_2410_, v___x_2409_);
return v___x_2411_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5(void){
_start:
{
lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2412_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__4);
v___x_2413_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__3);
v___x_2414_ = l_Lean_Parser_andthen(v___x_2413_, v___x_2412_);
return v___x_2414_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6(void){
_start:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; 
v___x_2415_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__5);
v___x_2416_ = ((lean_object*)(l_Lean_Doc_Parser_codeBlockFence));
v___x_2417_ = l_Lean_Parser_andthen(v___x_2416_, v___x_2415_);
return v___x_2417_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__7(void){
_start:
{
uint8_t v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; 
v___x_2418_ = 0;
v___x_2419_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__6);
v___x_2420_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1));
v___x_2421_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__0));
v___x_2422_ = l_Lean_Parser_nodeWithAntiquot(v___x_2421_, v___x_2420_, v___x_2419_, v___x_2418_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot(lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v___x_2425_; lean_object* v_fn_2426_; lean_object* v___x_2427_; 
v___x_2425_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__7, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__7_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__7);
v_fn_2426_ = lean_ctor_get(v___x_2425_, 1);
lean_inc_ref(v_fn_2426_);
v___x_2427_ = lean_apply_2(v_fn_2426_, v_a_2423_, v_a_2424_);
return v___x_2427_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4(void){
_start:
{
lean_object* v___x_2447_; lean_object* v___x_2448_; 
v___x_2447_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__3));
v___x_2448_ = l_Lean_Parser_atomic(v___x_2447_);
return v___x_2448_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; 
v___x_2449_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__4);
v___x_2450_ = l_Lean_Parser_many(v___x_2449_);
return v___x_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot(lean_object* v_marker_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_){
_start:
{
lean_object* v___x_2469_; lean_object* v___x_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; lean_object* v___x_2476_; uint8_t v___x_2477_; lean_object* v___x_2478_; lean_object* v_fn_2479_; lean_object* v___x_2480_; 
v___x_2469_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__0));
v___x_2470_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3));
v___x_2471_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2472_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot), 2, 0);
v___x_2473_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2473_, 0, v___x_2471_);
lean_ctor_set(v___x_2473_, 1, v___x_2472_);
v___x_2474_ = l_Lean_Parser_atomic(v___x_2473_);
v___x_2475_ = l_Lean_Parser_many(v___x_2474_);
v___x_2476_ = l_Lean_Parser_andthen(v_marker_2466_, v___x_2475_);
v___x_2477_ = 0;
v___x_2478_ = l_Lean_Parser_nodeWithAntiquot(v___x_2469_, v___x_2470_, v___x_2476_, v___x_2477_);
v_fn_2479_ = lean_ctor_get(v___x_2478_, 1);
lean_inc_ref(v_fn_2479_);
lean_dec_ref(v___x_2478_);
v___x_2480_ = lean_apply_2(v_fn_2479_, v_a_2467_, v_a_2468_);
return v___x_2480_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot(lean_object* v_a_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v___x_2483_; lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; uint8_t v___x_2491_; lean_object* v___x_2492_; lean_object* v_fn_2493_; lean_object* v___x_2494_; 
v___x_2483_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__0));
v___x_2484_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__1));
v___x_2485_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2486_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_unorderedListMarker));
v___x_2487_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot), 3, 1);
lean_closure_set(v___x_2487_, 0, v___x_2486_);
v___x_2488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2488_, 0, v___x_2485_);
lean_ctor_set(v___x_2488_, 1, v___x_2487_);
v___x_2489_ = l_Lean_Parser_atomic(v___x_2488_);
v___x_2490_ = l_Lean_Parser_many1(v___x_2489_);
v___x_2491_ = 0;
v___x_2492_ = l_Lean_Parser_nodeWithAntiquot(v___x_2483_, v___x_2484_, v___x_2490_, v___x_2491_);
v_fn_2493_ = lean_ctor_get(v___x_2492_, 1);
lean_inc_ref(v_fn_2493_);
lean_dec_ref(v___x_2492_);
v___x_2494_ = lean_apply_2(v_fn_2493_, v_a_2481_, v_a_2482_);
return v___x_2494_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot(lean_object* v_a_2502_, lean_object* v_a_2503_){
_start:
{
lean_object* v___x_2504_; lean_object* v___x_2505_; lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; uint8_t v___x_2512_; lean_object* v___x_2513_; lean_object* v_fn_2514_; lean_object* v___x_2515_; 
v___x_2504_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__0));
v___x_2505_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__1));
v___x_2506_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2507_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_orderedListMarker));
v___x_2508_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot), 3, 1);
lean_closure_set(v___x_2508_, 0, v___x_2507_);
v___x_2509_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2509_, 0, v___x_2506_);
lean_ctor_set(v___x_2509_, 1, v___x_2508_);
v___x_2510_ = l_Lean_Parser_atomic(v___x_2509_);
v___x_2511_ = l_Lean_Parser_many1(v___x_2510_);
v___x_2512_ = 0;
v___x_2513_ = l_Lean_Parser_nodeWithAntiquot(v___x_2504_, v___x_2505_, v___x_2511_, v___x_2512_);
v_fn_2514_ = lean_ctor_get(v___x_2513_, 1);
lean_inc_ref(v_fn_2514_);
lean_dec_ref(v___x_2513_);
v___x_2515_ = lean_apply_2(v_fn_2514_, v_a_2502_, v_a_2503_);
return v___x_2515_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__3(void){
_start:
{
lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2524_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__2));
v___x_2525_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_atomOf(v___x_2524_);
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot(lean_object* v_a_2526_, lean_object* v_a_2527_){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; lean_object* v___x_2536_; uint8_t v___x_2537_; lean_object* v___x_2538_; lean_object* v_fn_2539_; lean_object* v___x_2540_; 
v___x_2528_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__0));
v___x_2529_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1));
v___x_2530_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__3);
v___x_2531_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2532_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot), 2, 0);
v___x_2533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2533_, 0, v___x_2531_);
lean_ctor_set(v___x_2533_, 1, v___x_2532_);
v___x_2534_ = l_Lean_Parser_atomic(v___x_2533_);
v___x_2535_ = l_Lean_Parser_many(v___x_2534_);
v___x_2536_ = l_Lean_Parser_andthen(v___x_2530_, v___x_2535_);
v___x_2537_ = 0;
v___x_2538_ = l_Lean_Parser_nodeWithAntiquot(v___x_2528_, v___x_2529_, v___x_2536_, v___x_2537_);
v_fn_2539_ = lean_ctor_get(v___x_2538_, 1);
lean_inc_ref(v_fn_2539_);
lean_dec_ref(v___x_2538_);
v___x_2540_ = lean_apply_2(v_fn_2539_, v_a_2526_, v_a_2527_);
return v___x_2540_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0(void){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; 
v___x_2541_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot), 2, 0);
v___x_2542_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2543_, 0, v___x_2542_);
lean_ctor_set(v___x_2543_, 1, v___x_2541_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot(lean_object* v_a_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v___x_2553_; lean_object* v___x_2554_; lean_object* v___x_2555_; lean_object* v___x_2556_; lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; uint8_t v___x_2567_; lean_object* v___x_2568_; lean_object* v_fn_2569_; lean_object* v___x_2570_; 
v___x_2553_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__0));
v___x_2554_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__1));
v___x_2555_ = ((lean_object*)(l_Lean_Doc_Parser_directiveDelimiter));
v___x_2556_ = l_Lean_Parser_ident;
v___x_2557_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_roleQuot___closed__4);
v___x_2558_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2559_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot), 2, 0);
v___x_2560_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2560_, 0, v___x_2558_);
lean_ctor_set(v___x_2560_, 1, v___x_2559_);
v___x_2561_ = l_Lean_Parser_atomic(v___x_2560_);
v___x_2562_ = l_Lean_Parser_many(v___x_2561_);
v___x_2563_ = l_Lean_Parser_andthen(v___x_2562_, v___x_2555_);
v___x_2564_ = l_Lean_Parser_andthen(v___x_2557_, v___x_2563_);
v___x_2565_ = l_Lean_Parser_andthen(v___x_2556_, v___x_2564_);
v___x_2566_ = l_Lean_Parser_andthen(v___x_2555_, v___x_2565_);
v___x_2567_ = 0;
v___x_2568_ = l_Lean_Parser_nodeWithAntiquot(v___x_2553_, v___x_2554_, v___x_2566_, v___x_2567_);
v_fn_2569_ = lean_ctor_get(v___x_2568_, 1);
lean_inc_ref(v_fn_2569_);
lean_dec_ref(v___x_2568_);
v___x_2570_ = lean_apply_2(v_fn_2569_, v_a_2551_, v_a_2552_);
return v___x_2570_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7(void){
_start:
{
uint8_t v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2577_ = 1;
v___x_2578_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__6));
v___x_2579_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__5));
v___x_2580_ = l_Lean_Parser_mkAntiquot(v___x_2579_, v___x_2578_, v___x_2577_, v___x_2577_);
return v___x_2580_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9(void){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2581_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot), 2, 0);
v___x_2582_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2583_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2583_, 0, v___x_2582_);
lean_ctor_set(v___x_2583_, 1, v___x_2581_);
return v___x_2583_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8(void){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2584_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot), 2, 0);
v___x_2585_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2586_, 0, v___x_2585_);
lean_ctor_set(v___x_2586_, 1, v___x_2584_);
return v___x_2586_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10(void){
_start:
{
lean_object* v___x_2587_; lean_object* v___x_2588_; lean_object* v___x_2589_; 
v___x_2587_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__9);
v___x_2588_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__8);
v___x_2589_ = l_Lean_Parser_orelse(v___x_2588_, v___x_2587_);
return v___x_2589_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4(void){
_start:
{
lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; 
v___x_2590_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot), 2, 0);
v___x_2591_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2592_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2592_, 0, v___x_2591_);
lean_ctor_set(v___x_2592_, 1, v___x_2590_);
return v___x_2592_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11(void){
_start:
{
lean_object* v___x_2593_; lean_object* v___x_2594_; lean_object* v___x_2595_; 
v___x_2593_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__10);
v___x_2594_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__4);
v___x_2595_ = l_Lean_Parser_orelse(v___x_2594_, v___x_2593_);
return v___x_2595_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3(void){
_start:
{
lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; 
v___x_2596_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot), 2, 0);
v___x_2597_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2598_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2598_, 0, v___x_2597_);
lean_ctor_set(v___x_2598_, 1, v___x_2596_);
return v___x_2598_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12(void){
_start:
{
lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2599_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__11);
v___x_2600_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__3);
v___x_2601_ = l_Lean_Parser_orelse(v___x_2600_, v___x_2599_);
return v___x_2601_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2(void){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2602_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot), 2, 0);
v___x_2603_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2604_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2604_, 0, v___x_2603_);
lean_ctor_set(v___x_2604_, 1, v___x_2602_);
return v___x_2604_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13(void){
_start:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2605_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__12);
v___x_2606_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__2);
v___x_2607_ = l_Lean_Parser_orelse(v___x_2606_, v___x_2605_);
return v___x_2607_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1(void){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2608_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot), 2, 0);
v___x_2609_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
lean_ctor_set(v___x_2610_, 1, v___x_2608_);
return v___x_2610_;
}
}
static lean_object* _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__14(void){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__13);
v___x_2612_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__1);
v___x_2613_ = l_Lean_Parser_orelse(v___x_2612_, v___x_2611_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot(lean_object* v_c_2614_, lean_object* v_s_2615_){
_start:
{
lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; lean_object* v_fn_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v_alts_2636_; lean_object* v_fn_2637_; uint8_t v___x_2638_; lean_object* v___x_2639_; 
v___x_2616_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2617_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot), 2, 0);
v___x_2618_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2618_, 0, v___x_2616_);
lean_ctor_set(v___x_2618_, 1, v___x_2617_);
v___x_2619_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot), 2, 0);
v___x_2620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2620_, 0, v___x_2616_);
lean_ctor_set(v___x_2620_, 1, v___x_2619_);
v___x_2621_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot), 2, 0);
v___x_2622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2622_, 0, v___x_2616_);
lean_ctor_set(v___x_2622_, 1, v___x_2621_);
v___x_2623_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot), 2, 0);
v___x_2624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2624_, 0, v___x_2616_);
lean_ctor_set(v___x_2624_, 1, v___x_2623_);
v___x_2625_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__0);
v___x_2626_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot), 2, 0);
v___x_2627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2627_, 0, v___x_2616_);
lean_ctor_set(v___x_2627_, 1, v___x_2626_);
v___x_2628_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__7);
v_fn_2629_ = lean_ctor_get(v___x_2628_, 1);
v___x_2630_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__14, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__14_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot___closed__14);
v___x_2631_ = l_Lean_Parser_orelse(v___x_2627_, v___x_2630_);
v___x_2632_ = l_Lean_Parser_orelse(v___x_2625_, v___x_2631_);
v___x_2633_ = l_Lean_Parser_orelse(v___x_2624_, v___x_2632_);
v___x_2634_ = l_Lean_Parser_orelse(v___x_2622_, v___x_2633_);
v___x_2635_ = l_Lean_Parser_orelse(v___x_2620_, v___x_2634_);
v_alts_2636_ = l_Lean_Parser_orelse(v___x_2618_, v___x_2635_);
v_fn_2637_ = lean_ctor_get(v_alts_2636_, 1);
lean_inc_ref(v_fn_2637_);
lean_dec_ref(v_alts_2636_);
v___x_2638_ = 0;
lean_inc_ref(v_fn_2629_);
v___x_2639_ = l_Lean_Parser_withAntiquotFn(v_fn_2629_, v_fn_2637_, v___x_2638_, v_c_2614_, v_s_2615_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot(lean_object* v_a_2640_, lean_object* v_a_2641_){
_start:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; uint8_t v___x_2653_; lean_object* v___x_2654_; lean_object* v_fn_2655_; lean_object* v___x_2656_; 
v___x_2642_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__0));
v___x_2643_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2));
v___x_2644_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemMarker));
v___x_2645_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2646_ = lean_obj_once(&l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5, &l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5_once, _init_l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__5);
v___x_2647_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockQuot), 2, 0);
v___x_2648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2645_);
lean_ctor_set(v___x_2648_, 1, v___x_2647_);
v___x_2649_ = l_Lean_Parser_atomic(v___x_2648_);
v___x_2650_ = l_Lean_Parser_many(v___x_2649_);
v___x_2651_ = l_Lean_Parser_andthen(v___x_2646_, v___x_2650_);
v___x_2652_ = l_Lean_Parser_andthen(v___x_2644_, v___x_2651_);
v___x_2653_ = 0;
v___x_2654_ = l_Lean_Parser_nodeWithAntiquot(v___x_2642_, v___x_2643_, v___x_2652_, v___x_2653_);
v_fn_2655_ = lean_ctor_get(v___x_2654_, 1);
lean_inc_ref(v_fn_2655_);
lean_dec_ref(v___x_2654_);
v___x_2656_ = lean_apply_2(v_fn_2655_, v_a_2640_, v_a_2641_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot(lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; uint8_t v___x_2666_; lean_object* v___x_2667_; lean_object* v_fn_2668_; lean_object* v___x_2669_; 
v___x_2659_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__0));
v___x_2660_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__1));
v___x_2661_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_boldQuot___closed__4));
v___x_2662_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot), 2, 0);
v___x_2663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2663_, 0, v___x_2661_);
lean_ctor_set(v___x_2663_, 1, v___x_2662_);
v___x_2664_ = l_Lean_Parser_atomic(v___x_2663_);
v___x_2665_ = l_Lean_Parser_many1(v___x_2664_);
v___x_2666_ = 0;
v___x_2667_ = l_Lean_Parser_nodeWithAntiquot(v___x_2659_, v___x_2660_, v___x_2665_, v___x_2666_);
v_fn_2668_ = lean_ctor_get(v___x_2667_, 1);
lean_inc_ref(v_fn_2668_);
lean_dec_ref(v___x_2667_);
v___x_2669_ = lean_apply_2(v_fn_2668_, v_a_2657_, v_a_2658_);
return v___x_2669_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1(){
_start:
{
lean_object* v___x_2678_; lean_object* v___x_2679_; lean_object* v___x_2680_; 
v___x_2678_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_listItemQuot___closed__3));
v___x_2679_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1___closed__0));
v___x_2680_ = l_Lean_addBuiltinDocString(v___x_2678_, v___x_2679_);
return v___x_2680_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1___boxed(lean_object* v_a_2681_){
_start:
{
lean_object* v_res_2682_; 
v_res_2682_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ListItem_item___regBuiltin_Lean_Doc_Parser_ListItem_item_docString__1();
return v_res_2682_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1(){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___x_2692_; 
v___x_2690_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_descItemQuot___closed__2));
v___x_2691_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1___closed__0));
v___x_2692_ = l_Lean_addBuiltinDocString(v___x_2690_, v___x_2691_);
return v___x_2692_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1___boxed(lean_object* v_a_2693_){
_start:
{
lean_object* v_res_2694_; 
v_res_2694_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_DescItem_item___regBuiltin_Lean_Doc_Parser_DescItem_item_docString__1();
return v_res_2694_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_para___closed__0(void){
_start:
{
lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v___x_2695_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot), 2, 0);
v___x_2696_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2697_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2696_);
lean_ctor_set(v___x_2697_, 1, v___x_2695_);
return v___x_2697_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_para(void){
_start:
{
lean_object* v___x_2698_; 
v___x_2698_ = lean_obj_once(&l_Lean_Doc_Parser_Block_para___closed__0, &l_Lean_Doc_Parser_Block_para___closed__0_once, _init_l_Lean_Doc_Parser_Block_para___closed__0);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1(){
_start:
{
lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; 
v___x_2701_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_paraQuot___closed__2));
v___x_2702_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1___closed__0));
v___x_2703_ = l_Lean_addBuiltinDocString(v___x_2701_, v___x_2702_);
return v___x_2703_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1___boxed(lean_object* v_a_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_para___regBuiltin_Lean_Doc_Parser_Block_para_docString__1();
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1(){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; lean_object* v___x_2715_; 
v___x_2713_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_ulQuot___closed__1));
v___x_2714_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1___closed__0));
v___x_2715_ = l_Lean_addBuiltinDocString(v___x_2713_, v___x_2714_);
return v___x_2715_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1___boxed(lean_object* v_a_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ul___regBuiltin_Lean_Doc_Parser_Block_ul_docString__1();
return v_res_2717_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1(){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; 
v___x_2725_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_olQuot___closed__1));
v___x_2726_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1___closed__0));
v___x_2727_ = l_Lean_addBuiltinDocString(v___x_2725_, v___x_2726_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1___boxed(lean_object* v_a_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_ol___regBuiltin_Lean_Doc_Parser_Block_ol_docString__1();
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1(){
_start:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; 
v___x_2737_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_dlQuot___closed__1));
v___x_2738_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1___closed__0));
v___x_2739_ = l_Lean_addBuiltinDocString(v___x_2737_, v___x_2738_);
return v___x_2739_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1___boxed(lean_object* v_a_2740_){
_start:
{
lean_object* v_res_2741_; 
v_res_2741_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_dl___regBuiltin_Lean_Doc_Parser_Block_dl_docString__1();
return v_res_2741_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1(){
_start:
{
lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; 
v___x_2749_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_blockquoteQuot___closed__1));
v___x_2750_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1___closed__0));
v___x_2751_ = l_Lean_addBuiltinDocString(v___x_2749_, v___x_2750_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1___boxed(lean_object* v_a_2752_){
_start:
{
lean_object* v_res_2753_; 
v_res_2753_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_blockquote___regBuiltin_Lean_Doc_Parser_Block_blockquote_docString__1();
return v_res_2753_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_codeblock___closed__0(void){
_start:
{
lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; 
v___x_2754_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot), 2, 0);
v___x_2755_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2756_, 0, v___x_2755_);
lean_ctor_set(v___x_2756_, 1, v___x_2754_);
return v___x_2756_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_codeblock(void){
_start:
{
lean_object* v___x_2757_; 
v___x_2757_ = lean_obj_once(&l_Lean_Doc_Parser_Block_codeblock___closed__0, &l_Lean_Doc_Parser_Block_codeblock___closed__0_once, _init_l_Lean_Doc_Parser_Block_codeblock___closed__0);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1(){
_start:
{
lean_object* v___x_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; 
v___x_2760_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_codeblockQuot___closed__1));
v___x_2761_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1___closed__0));
v___x_2762_ = l_Lean_addBuiltinDocString(v___x_2760_, v___x_2761_);
return v___x_2762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1___boxed(lean_object* v_a_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_codeblock___regBuiltin_Lean_Doc_Parser_Block_codeblock_docString__1();
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1(){
_start:
{
lean_object* v___x_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; 
v___x_2772_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_directiveQuot___closed__1));
v___x_2773_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1___closed__0));
v___x_2774_ = l_Lean_addBuiltinDocString(v___x_2772_, v___x_2773_);
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1___boxed(lean_object* v_a_2775_){
_start:
{
lean_object* v_res_2776_; 
v_res_2776_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_directive___regBuiltin_Lean_Doc_Parser_Block_directive_docString__1();
return v_res_2776_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_header___closed__0(void){
_start:
{
lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; 
v___x_2777_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot), 2, 0);
v___x_2778_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2779_, 0, v___x_2778_);
lean_ctor_set(v___x_2779_, 1, v___x_2777_);
return v___x_2779_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_header(void){
_start:
{
lean_object* v___x_2780_; 
v___x_2780_ = lean_obj_once(&l_Lean_Doc_Parser_Block_header___closed__0, &l_Lean_Doc_Parser_Block_header___closed__0_once, _init_l_Lean_Doc_Parser_Block_header___closed__0);
return v___x_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1(){
_start:
{
lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; 
v___x_2783_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_headerQuot___closed__1));
v___x_2784_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1___closed__0));
v___x_2785_ = l_Lean_addBuiltinDocString(v___x_2783_, v___x_2784_);
return v___x_2785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1___boxed(lean_object* v_a_2786_){
_start:
{
lean_object* v_res_2787_; 
v_res_2787_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_header___regBuiltin_Lean_Doc_Parser_Block_header_docString__1();
return v_res_2787_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_link__ref___closed__0(void){
_start:
{
lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2788_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot), 2, 0);
v___x_2789_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2790_, 0, v___x_2789_);
lean_ctor_set(v___x_2790_, 1, v___x_2788_);
return v___x_2790_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_link__ref(void){
_start:
{
lean_object* v___x_2791_; 
v___x_2791_ = lean_obj_once(&l_Lean_Doc_Parser_Block_link__ref___closed__0, &l_Lean_Doc_Parser_Block_link__ref___closed__0_once, _init_l_Lean_Doc_Parser_Block_link__ref___closed__0);
return v___x_2791_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1(){
_start:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; 
v___x_2794_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_linkRefQuot___closed__1));
v___x_2795_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1___closed__0));
v___x_2796_ = l_Lean_addBuiltinDocString(v___x_2794_, v___x_2795_);
return v___x_2796_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1___boxed(lean_object* v_a_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_link__ref___regBuiltin_Lean_Doc_Parser_Block_link__ref_docString__1();
return v_res_2798_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_footnote__ref___closed__0(void){
_start:
{
lean_object* v___x_2799_; lean_object* v___x_2800_; lean_object* v___x_2801_; 
v___x_2799_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot), 2, 0);
v___x_2800_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2801_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2801_, 0, v___x_2800_);
lean_ctor_set(v___x_2801_, 1, v___x_2799_);
return v___x_2801_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_footnote__ref(void){
_start:
{
lean_object* v___x_2802_; 
v___x_2802_ = lean_obj_once(&l_Lean_Doc_Parser_Block_footnote__ref___closed__0, &l_Lean_Doc_Parser_Block_footnote__ref___closed__0_once, _init_l_Lean_Doc_Parser_Block_footnote__ref___closed__0);
return v___x_2802_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1(){
_start:
{
lean_object* v___x_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2805_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_footnoteRefQuot___closed__1));
v___x_2806_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1___closed__0));
v___x_2807_ = l_Lean_addBuiltinDocString(v___x_2805_, v___x_2806_);
return v___x_2807_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1___boxed(lean_object* v_a_2808_){
_start:
{
lean_object* v_res_2809_; 
v_res_2809_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_footnote__ref___regBuiltin_Lean_Doc_Parser_Block_footnote__ref_docString__1();
return v_res_2809_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_metadata__block___closed__0(void){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; 
v___x_2810_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot), 2, 0);
v___x_2811_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2812_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2812_, 0, v___x_2811_);
lean_ctor_set(v___x_2812_, 1, v___x_2810_);
return v___x_2812_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_metadata__block(void){
_start:
{
lean_object* v___x_2813_; 
v___x_2813_ = lean_obj_once(&l_Lean_Doc_Parser_Block_metadata__block___closed__0, &l_Lean_Doc_Parser_Block_metadata__block___closed__0_once, _init_l_Lean_Doc_Parser_Block_metadata__block___closed__0);
return v___x_2813_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1(){
_start:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2816_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_metadataQuot___closed__1));
v___x_2817_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1___closed__0));
v___x_2818_ = l_Lean_addBuiltinDocString(v___x_2816_, v___x_2817_);
return v___x_2818_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1___boxed(lean_object* v_a_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_metadata__block___regBuiltin_Lean_Doc_Parser_Block_metadata__block_docString__1();
return v_res_2820_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_command___closed__0(void){
_start:
{
lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2821_ = lean_alloc_closure((void*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot), 2, 0);
v___x_2822_ = ((lean_object*)(l_Lean_Doc_Parser_versoText___closed__3));
v___x_2823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2823_, 0, v___x_2822_);
lean_ctor_set(v___x_2823_, 1, v___x_2821_);
return v___x_2823_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_Block_command(void){
_start:
{
lean_object* v___x_2824_; 
v___x_2824_ = lean_obj_once(&l_Lean_Doc_Parser_Block_command___closed__0, &l_Lean_Doc_Parser_Block_command___closed__0_once, _init_l_Lean_Doc_Parser_Block_command___closed__0);
return v___x_2824_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1(){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2827_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_commandQuot___closed__1));
v___x_2828_ = ((lean_object*)(l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1___closed__0));
v___x_2829_ = l_Lean_addBuiltinDocString(v___x_2827_, v___x_2828_);
return v___x_2829_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1___boxed(lean_object* v_a_2830_){
_start:
{
lean_object* v_res_2831_; 
v_res_2831_ = l___private_Lean_DocString_Syntax_0__Lean_Doc_Parser_Block_command___regBuiltin_Lean_Doc_Parser_Block_command_docString__1();
return v_res_2831_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_document___lam__0___closed__2(void){
_start:
{
lean_object* v___x_2843_; lean_object* v___x_2844_; 
v___x_2843_ = ((lean_object*)(l_Lean_Doc_Parser_block));
v___x_2844_ = l_Lean_Parser_atomic(v___x_2843_);
return v___x_2844_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_document___lam__0___closed__3(void){
_start:
{
lean_object* v___x_2845_; lean_object* v___x_2846_; 
v___x_2845_ = lean_obj_once(&l_Lean_Doc_Parser_document___lam__0___closed__2, &l_Lean_Doc_Parser_document___lam__0___closed__2_once, _init_l_Lean_Doc_Parser_document___lam__0___closed__2);
v___x_2846_ = l_Lean_Parser_many(v___x_2845_);
return v___x_2846_;
}
}
static lean_object* _init_l_Lean_Doc_Parser_document___lam__0___closed__4(void){
_start:
{
uint8_t v___x_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2847_ = 0;
v___x_2848_ = lean_obj_once(&l_Lean_Doc_Parser_document___lam__0___closed__3, &l_Lean_Doc_Parser_document___lam__0___closed__3_once, _init_l_Lean_Doc_Parser_document___lam__0___closed__3);
v___x_2849_ = ((lean_object*)(l_Lean_Doc_Parser_document___lam__0___closed__1));
v___x_2850_ = ((lean_object*)(l_Lean_Doc_Parser_document___lam__0___closed__0));
v___x_2851_ = l_Lean_Parser_nodeWithAntiquot(v___x_2850_, v___x_2849_, v___x_2848_, v___x_2847_);
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_Parser_document___lam__0(lean_object* v_c_2852_, lean_object* v_s_2853_){
_start:
{
lean_object* v___x_2854_; lean_object* v_fn_2855_; lean_object* v___x_2856_; 
v___x_2854_ = lean_obj_once(&l_Lean_Doc_Parser_document___lam__0___closed__4, &l_Lean_Doc_Parser_document___lam__0___closed__4_once, _init_l_Lean_Doc_Parser_document___lam__0___closed__4);
v_fn_2855_ = lean_ctor_get(v___x_2854_, 1);
lean_inc_ref(v_fn_2855_);
v___x_2856_ = lean_apply_2(v_fn_2855_, v_c_2852_, v_s_2853_);
return v___x_2856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0(size_t v_sz_2862_, size_t v_i_2863_, lean_object* v_bs_2864_){
_start:
{
uint8_t v___x_2865_; 
v___x_2865_ = lean_usize_dec_lt(v_i_2863_, v_sz_2862_);
if (v___x_2865_ == 0)
{
return v_bs_2864_;
}
else
{
lean_object* v_v_2866_; lean_object* v___x_2867_; lean_object* v_bs_x27_2868_; size_t v___x_2869_; size_t v___x_2870_; lean_object* v___x_2871_; 
v_v_2866_ = lean_array_uget(v_bs_2864_, v_i_2863_);
v___x_2867_ = lean_unsigned_to_nat(0u);
v_bs_x27_2868_ = lean_array_uset(v_bs_2864_, v_i_2863_, v___x_2867_);
v___x_2869_ = ((size_t)1ULL);
v___x_2870_ = lean_usize_add(v_i_2863_, v___x_2869_);
v___x_2871_ = lean_array_uset(v_bs_x27_2868_, v_i_2863_, v_v_2866_);
v_i_2863_ = v___x_2870_;
v_bs_2864_ = v___x_2871_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0___boxed(lean_object* v_sz_2873_, lean_object* v_i_2874_, lean_object* v_bs_2875_){
_start:
{
size_t v_sz_boxed_2876_; size_t v_i_boxed_2877_; lean_object* v_res_2878_; 
v_sz_boxed_2876_ = lean_unbox_usize(v_sz_2873_);
lean_dec(v_sz_2873_);
v_i_boxed_2877_ = lean_unbox_usize(v_i_2874_);
lean_dec(v_i_2874_);
v_res_2878_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0(v_sz_boxed_2876_, v_i_boxed_2877_, v_bs_2875_);
return v_res_2878_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoBlocks(lean_object* v_doc_2879_){
_start:
{
lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; size_t v_sz_2883_; size_t v___x_2884_; lean_object* v___x_2885_; 
v___x_2880_ = lean_unsigned_to_nat(0u);
v___x_2881_ = l_Lean_Syntax_getArg(v_doc_2879_, v___x_2880_);
v___x_2882_ = l_Lean_Syntax_getArgs(v___x_2881_);
lean_dec(v___x_2881_);
v_sz_2883_ = lean_array_size(v___x_2882_);
v___x_2884_ = ((size_t)0ULL);
v___x_2885_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_TSyntax_getVersoBlocks_spec__0(v_sz_2883_, v___x_2884_, v___x_2882_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoBlocks___boxed(lean_object* v_doc_2886_){
_start:
{
lean_object* v_res_2887_; 
v_res_2887_ = l_Lean_TSyntax_getVersoBlocks(v_doc_2886_);
lean_dec(v_doc_2886_);
return v_res_2887_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoDelimiter(lean_object* v_delim_2888_){
_start:
{
lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; 
v___x_2889_ = lean_unsigned_to_nat(0u);
v___x_2890_ = l_Lean_Syntax_getArg(v_delim_2888_, v___x_2889_);
v___x_2891_ = l_Lean_Syntax_getAtomVal(v___x_2890_);
lean_dec(v___x_2890_);
return v___x_2891_;
}
}
LEAN_EXPORT lean_object* l_Lean_TSyntax_getVersoDelimiter___boxed(lean_object* v_delim_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_Lean_TSyntax_getVersoDelimiter(v_delim_2892_);
lean_dec(v_delim_2892_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoDocument_view(lean_object* v_doc_2894_){
_start:
{
lean_object* v___x_2895_; 
v___x_2895_ = l_Lean_TSyntax_getVersoBlocks(v_doc_2894_);
return v___x_2895_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoDocument_view___boxed(lean_object* v_doc_2896_){
_start:
{
lean_object* v_res_2897_; 
v_res_2897_ = l_Lean_Doc_VersoDocument_view(v_doc_2896_);
lean_dec(v_doc_2896_);
return v_res_2897_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoDelimiter_view(lean_object* v_delim_2898_){
_start:
{
lean_object* v___x_2899_; 
v___x_2899_ = l_Lean_TSyntax_getVersoDelimiter(v_delim_2898_);
return v___x_2899_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_VersoDelimiter_view___boxed(lean_object* v_delim_2900_){
_start:
{
lean_object* v_res_2901_; 
v_res_2901_ = l_Lean_Doc_VersoDelimiter_view(v_delim_2900_);
lean_dec(v_delim_2900_);
return v_res_2901_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___lam__0(lean_object* v_s_2904_){
_start:
{
lean_inc(v_s_2904_);
return v_s_2904_;
}
}
LEAN_EXPORT lean_object* l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___lam__0___boxed(lean_object* v_s_2905_){
_start:
{
lean_object* v_res_2906_; 
v_res_2906_ = l_Lean_Doc_instCoeTSyntaxConsSyntaxNodeKindMkStr5NilMkStr4__lean___lam__0(v_s_2905_);
lean_dec(v_s_2905_);
return v_res_2906_;
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
