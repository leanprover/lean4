// Lean compiler output
// Module: Lake.Toml.Grammar
// Imports: import Lake.Toml.ParserUtil import Lean.Parser public import Lean.PrettyPrinter.Formatter public import Lean.PrettyPrinter.Parenthesizer
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
lean_object* lean_string_push(lean_object*, uint32_t);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Parser_takeWhileFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_trailing(lean_object*);
lean_object* l_Lake_Toml_skipFn___boxed(lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lake_Toml_chAtom(uint32_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_chFn(uint32_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_instBEqError_beq(lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_mkUnexpectedCharError(lean_object*, uint32_t, lean_object*, uint8_t);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_litWithAntiquot(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Parser_atomicFn(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object*, lean_object*);
lean_object* l_Lean_Parser_hexDigitFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_setExpected(lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lake_Toml_strFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_lit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_pushLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
lean_object* l_Lake_Toml_sepByChar1Fn(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_sepByChar1AuxFn(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_digitPairFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_takeWhile1Fn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_stackSize(lean_object*);
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_isHexDigit___boxed(lean_object*);
lean_object* l_Lake_Toml_isOctDigit___boxed(lean_object*);
lean_object* l_Lake_Toml_isBinDigit___boxed(lean_object*);
lean_object* l_Lake_Toml_dynamicNode(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
lean_object* l_Lean_Parser_takeUntilFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_chAtom_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_recNodeWithAntiquot(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg();
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeWithAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_setExpected_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_epsilon_formatter___redArg();
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Parser_checkStackTop(lean_object*, lean_object*);
lean_object* l_Lake_Toml_digitFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_chAtom_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeWithAntiquot_formatter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_setExpected_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_atomic(lean_object*);
lean_object* l_Lean_Parser_atomic_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_sepByLinebreak_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_notFollowedBy(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Parser_symbol(lean_object*);
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Parser_pushNone;
lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
lean_object* l_Lean_Parser_sepByNoAntiquot(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_isControlChar(uint32_t);
LEAN_EXPORT lean_object* l_Lake_Toml_isControlChar___boxed(lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_wsFn___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lake_Toml_wsFn___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_Toml_wsFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_wsFn___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_wsFn___closed__0 = (const lean_object*)&l_Lake_Toml_wsFn___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_wsFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_wsFn___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 32, .m_capacity = 32, .m_length = 31, .m_data = "invalid newline; no LF after CR"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_newlineFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "newline"};
static const lean_object* l_Lake_Toml_newlineFn___closed__0 = (const lean_object*)&l_Lake_Toml_newlineFn___closed__0_value;
static const lean_ctor_object l_Lake_Toml_newlineFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_newlineFn___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_newlineFn___closed__1 = (const lean_object*)&l_Lake_Toml_newlineFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Toml_newlineFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_newlineFn___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_isControlChar___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_commentFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "comment"};
static const lean_object* l_Lake_Toml_commentFn___closed__0 = (const lean_object*)&l_Lake_Toml_commentFn___closed__0_value;
static const lean_ctor_object l_Lake_Toml_commentFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_commentFn___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_commentFn___closed__1 = (const lean_object*)&l_Lake_Toml_commentFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Toml_commentFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_commentFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_wsNewlineFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_wsNewlineFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailingFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailingFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_isEscapeChar(uint32_t);
LEAN_EXPORT lean_object* l_Lake_Toml_isEscapeChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "escape sequence"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__1 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__1_value;
static const lean_closure_object l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__2 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__2_value;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "string gap is forbidden here"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__3 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__3_value;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "invalid escape sequence"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__4 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__4_value;
static const lean_closure_object l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__5 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__5_value;
static const lean_closure_object l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_wsNewlineFn___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__6 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__6_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "unterminated basic string"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_basicStringFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "basic string"};
static const lean_object* l_Lake_Toml_basicStringFn___closed__0 = (const lean_object*)&l_Lake_Toml_basicStringFn___closed__0_value;
static const lean_ctor_object l_Lake_Toml_basicStringFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_basicStringFn___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_basicStringFn___closed__1 = (const lean_object*)&l_Lake_Toml_basicStringFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Toml_basicStringFn(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "unterminated literal string"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_literalStringFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "literal string"};
static const lean_object* l_Lake_Toml_literalStringFn___closed__0 = (const lean_object*)&l_Lake_Toml_literalStringFn___closed__0_value;
static const lean_ctor_object l_Lake_Toml_literalStringFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_literalStringFn___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_literalStringFn___closed__1 = (const lean_object*)&l_Lake_Toml_literalStringFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Toml_literalStringFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_literalStringFn___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "too many quotes"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "unterminated multi-line literal string"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__1 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "multi-line literal string"};
static const lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__0 = (const lean_object*)&l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__1 = (const lean_object*)&l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralStringFn___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralStringFn___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_mlLiteralStringFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_mlLiteralStringFn___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))} };
static const lean_object* l_Lake_Toml_mlLiteralStringFn___closed__0 = (const lean_object*)&l_Lake_Toml_mlLiteralStringFn___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralStringFn(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 37, .m_capacity = 37, .m_length = 36, .m_data = "unterminated multi-line basic string"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "multi-line basic string"};
static const lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__0 = (const lean_object*)&l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__1 = (const lean_object*)&l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicStringFn___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicStringFn___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_mlBasicStringFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_mlBasicStringFn___lam__0___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(3) << 1) | 1))} };
static const lean_object* l_Lake_Toml_mlBasicStringFn___closed__0 = (const lean_object*)&l_Lake_Toml_mlBasicStringFn___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicStringFn(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "hour digit"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__1 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2_value;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "minute digit"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__8 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__8_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__8_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "time offset is forbidden here"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn(uint8_t, uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0(uint32_t);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0___boxed(lean_object*);
static const lean_closure_object l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "millisecond"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__1 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__1_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__2 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "second digit"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__1 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_timeFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hour"};
static const lean_object* l_Lake_Toml_timeFn___closed__0 = (const lean_object*)&l_Lake_Toml_timeFn___closed__0_value;
static const lean_ctor_object l_Lake_Toml_timeFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_timeFn___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_timeFn___closed__1 = (const lean_object*)&l_Lake_Toml_timeFn___closed__1_value;
LEAN_EXPORT lean_object* l_Lake_Toml_timeFn(uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_timeFn___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "month digit"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__1 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__1_value;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "day digit"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__6 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__6_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__7 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__7_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "year digit"};
static const lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__0 = (const lean_object*)&l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__1 = (const lean_object*)&l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dateTimeFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dateTimeFn___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "decimal exponent"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__1 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__1_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lake"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Toml"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "float"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3_value_aux_1),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2_value),LEAN_SCALAR_PTR_LITERAL(104, 154, 151, 104, 68, 255, 246, 246)}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3_value;
static const lean_closure_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_skipFn___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4_value;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "decInt"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6_value_aux_1),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5_value),LEAN_SCALAR_PTR_LITERAL(146, 5, 249, 175, 125, 238, 54, 100)}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6_value;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "decimal fraction"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__7 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__7_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__7_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__8 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__8_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailFn(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__1 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "decimal integer"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0_value),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__1_value)}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "nf"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "'inf'"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__1 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__1_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__2 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "an"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__0_value;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "'nan'"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__1 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__1_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__2 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__2_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decimalFn(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "dateTime"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(100, 234, 1, 129, 172, 254, 231, 202)}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "date-time"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__3 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__3_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2_value),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__3_value)}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__4 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__4_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0_value),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__4_value)}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__5 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__5_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_numeralFn___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "integer"};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__0 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__0_value;
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__0_value),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__4_value)}};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__1 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__1_value;
static const lean_string_object l_Lake_Toml_numeralFn___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "unexpected '"};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__2 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__2_value;
static const lean_closure_object l_Lake_Toml_numeralFn___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_isHexDigit___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__3 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__3_value;
static const lean_string_object l_Lake_Toml_numeralFn___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "hexadecimal integer"};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__4 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__4_value;
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__5 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__5_value;
static const lean_string_object l_Lake_Toml_numeralFn___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexNum"};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__6 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__6_value;
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__7_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__7_value_aux_1),((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__6_value),LEAN_SCALAR_PTR_LITERAL(93, 174, 95, 211, 123, 63, 171, 252)}};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__7 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__7_value;
static const lean_closure_object l_Lake_Toml_numeralFn___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_isOctDigit___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__8 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__8_value;
static const lean_string_object l_Lake_Toml_numeralFn___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "octal integer"};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__9 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__9_value;
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__10 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__10_value;
static const lean_string_object l_Lake_Toml_numeralFn___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "octNum"};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__11 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__11_value;
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__12_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__12_value_aux_1),((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__11_value),LEAN_SCALAR_PTR_LITERAL(93, 70, 221, 168, 145, 119, 144, 197)}};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__12 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__12_value;
static const lean_closure_object l_Lake_Toml_numeralFn___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_isBinDigit___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__13 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__13_value;
static const lean_string_object l_Lake_Toml_numeralFn___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "binary integer"};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__14 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__14_value;
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__14_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__15 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__15_value;
static const lean_string_object l_Lake_Toml_numeralFn___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "binNum"};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__16 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__16_value;
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__17_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__17_value_aux_1),((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__16_value),LEAN_SCALAR_PTR_LITERAL(59, 60, 170, 39, 77, 137, 193, 6)}};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__17 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__17_value;
LEAN_EXPORT lean_object* l_Lake_Toml_numeralFn___lam__0(lean_object*, lean_object*);
static const lean_closure_object l_Lake_Toml_numeralFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_numeralFn___lam__0, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_numeralFn___closed__0 = (const lean_object*)&l_Lake_Toml_numeralFn___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_numeralFn(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Toml_trailingWs___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_trailingWs___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs;
static const lean_closure_object l_Lake_Toml_trailingSep___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_trailingFn___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_trailingSep___closed__0 = (const lean_object*)&l_Lake_Toml_trailingSep___closed__0_value;
static lean_once_cell_t l_Lake_Toml_trailingSep___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_trailingSep___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep;
LEAN_EXPORT uint8_t l_Lake_Toml_unquotedKeyFn___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lake_Toml_unquotedKeyFn___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_unquotedKeyFn___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_unquotedKeyFn___closed__0 = (const lean_object*)&l_Lake_Toml_unquotedKeyFn___closed__0_value;
static const lean_string_object l_Lake_Toml_unquotedKeyFn___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "unquoted key"};
static const lean_object* l_Lake_Toml_unquotedKeyFn___closed__1 = (const lean_object*)&l_Lake_Toml_unquotedKeyFn___closed__1_value;
static const lean_ctor_object l_Lake_Toml_unquotedKeyFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_unquotedKeyFn___closed__1_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_unquotedKeyFn___closed__2 = (const lean_object*)&l_Lake_Toml_unquotedKeyFn___closed__2_value;
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_unquotedKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "unquotedKey"};
static const lean_object* l_Lake_Toml_unquotedKey___closed__0 = (const lean_object*)&l_Lake_Toml_unquotedKey___closed__0_value;
static const lean_ctor_object l_Lake_Toml_unquotedKey___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_unquotedKey___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_unquotedKey___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_unquotedKey___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_unquotedKey___closed__1_value_aux_1),((lean_object*)&l_Lake_Toml_unquotedKey___closed__0_value),LEAN_SCALAR_PTR_LITERAL(56, 43, 232, 206, 44, 188, 39, 241)}};
static const lean_object* l_Lake_Toml_unquotedKey___closed__1 = (const lean_object*)&l_Lake_Toml_unquotedKey___closed__1_value;
static lean_once_cell_t l_Lake_Toml_unquotedKey___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_unquotedKey___closed__2;
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey;
static const lean_string_object l_Lake_Toml_basicString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "basicString"};
static const lean_object* l_Lake_Toml_basicString___closed__0 = (const lean_object*)&l_Lake_Toml_basicString___closed__0_value;
static const lean_ctor_object l_Lake_Toml_basicString___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_basicString___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_basicString___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_basicString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_basicString___closed__1_value_aux_1),((lean_object*)&l_Lake_Toml_basicString___closed__0_value),LEAN_SCALAR_PTR_LITERAL(164, 34, 208, 112, 75, 114, 213, 233)}};
static const lean_object* l_Lake_Toml_basicString___closed__1 = (const lean_object*)&l_Lake_Toml_basicString___closed__1_value;
static lean_once_cell_t l_Lake_Toml_basicString___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_basicString___closed__2;
LEAN_EXPORT lean_object* l_Lake_Toml_basicString;
static const lean_string_object l_Lake_Toml_literalString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "literalString"};
static const lean_object* l_Lake_Toml_literalString___closed__0 = (const lean_object*)&l_Lake_Toml_literalString___closed__0_value;
static const lean_ctor_object l_Lake_Toml_literalString___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_literalString___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_literalString___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_literalString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_literalString___closed__1_value_aux_1),((lean_object*)&l_Lake_Toml_literalString___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 168, 165, 209, 230, 255, 154, 83)}};
static const lean_object* l_Lake_Toml_literalString___closed__1 = (const lean_object*)&l_Lake_Toml_literalString___closed__1_value;
static lean_once_cell_t l_Lake_Toml_literalString___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_literalString___closed__2;
LEAN_EXPORT lean_object* l_Lake_Toml_literalString;
static const lean_string_object l_Lake_Toml_mlBasicString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "mlBasicString"};
static const lean_object* l_Lake_Toml_mlBasicString___closed__0 = (const lean_object*)&l_Lake_Toml_mlBasicString___closed__0_value;
static const lean_ctor_object l_Lake_Toml_mlBasicString___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_mlBasicString___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_mlBasicString___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_mlBasicString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_mlBasicString___closed__1_value_aux_1),((lean_object*)&l_Lake_Toml_mlBasicString___closed__0_value),LEAN_SCALAR_PTR_LITERAL(205, 27, 188, 79, 217, 46, 221, 25)}};
static const lean_object* l_Lake_Toml_mlBasicString___closed__1 = (const lean_object*)&l_Lake_Toml_mlBasicString___closed__1_value;
static lean_once_cell_t l_Lake_Toml_mlBasicString___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_mlBasicString___closed__2;
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicString;
static const lean_string_object l_Lake_Toml_mlLiteralString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "mlLiteralString"};
static const lean_object* l_Lake_Toml_mlLiteralString___closed__0 = (const lean_object*)&l_Lake_Toml_mlLiteralString___closed__0_value;
static const lean_ctor_object l_Lake_Toml_mlLiteralString___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_mlLiteralString___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_mlLiteralString___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_mlLiteralString___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_mlLiteralString___closed__1_value_aux_1),((lean_object*)&l_Lake_Toml_mlLiteralString___closed__0_value),LEAN_SCALAR_PTR_LITERAL(249, 215, 18, 247, 52, 33, 2, 54)}};
static const lean_object* l_Lake_Toml_mlLiteralString___closed__1 = (const lean_object*)&l_Lake_Toml_mlLiteralString___closed__1_value;
static lean_once_cell_t l_Lake_Toml_mlLiteralString___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_mlLiteralString___closed__2;
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralString;
static lean_once_cell_t l_Lake_Toml_quotedKey___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_quotedKey___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey;
static const lean_string_object l_Lake_Toml_simpleKey___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpleKey"};
static const lean_object* l_Lake_Toml_simpleKey___closed__0 = (const lean_object*)&l_Lake_Toml_simpleKey___closed__0_value;
static const lean_ctor_object l_Lake_Toml_simpleKey___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_simpleKey___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_simpleKey___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_simpleKey___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_simpleKey___closed__1_value_aux_1),((lean_object*)&l_Lake_Toml_simpleKey___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 51, 117, 190, 121, 223, 170, 220)}};
static const lean_object* l_Lake_Toml_simpleKey___closed__1 = (const lean_object*)&l_Lake_Toml_simpleKey___closed__1_value;
static lean_once_cell_t l_Lake_Toml_simpleKey___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_simpleKey___closed__2;
static lean_once_cell_t l_Lake_Toml_simpleKey___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_simpleKey___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey;
static const lean_string_object l_Lake_Toml_key___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "key"};
static const lean_object* l_Lake_Toml_key___closed__0 = (const lean_object*)&l_Lake_Toml_key___closed__0_value;
static const lean_ctor_object l_Lake_Toml_key___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_key___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_key___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_key___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_key___closed__1_value_aux_1),((lean_object*)&l_Lake_Toml_key___closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 24, 166, 18, 184, 133, 165, 53)}};
static const lean_object* l_Lake_Toml_key___closed__1 = (const lean_object*)&l_Lake_Toml_key___closed__1_value;
static const lean_ctor_object l_Lake_Toml_key___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_key___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_key___closed__2 = (const lean_object*)&l_Lake_Toml_key___closed__2_value;
static const lean_string_object l_Lake_Toml_key___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lake_Toml_key___closed__3 = (const lean_object*)&l_Lake_Toml_key___closed__3_value;
static lean_once_cell_t l_Lake_Toml_key___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_key___closed__4;
static lean_once_cell_t l_Lake_Toml_key___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_key___closed__5;
static lean_once_cell_t l_Lake_Toml_key___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_key___closed__6;
static lean_once_cell_t l_Lake_Toml_key___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_key___closed__7;
static lean_once_cell_t l_Lake_Toml_key___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_key___closed__8;
static lean_once_cell_t l_Lake_Toml_key___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_key___closed__9;
static lean_once_cell_t l_Lake_Toml_key___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_key___closed__10;
static lean_once_cell_t l_Lake_Toml_key___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_key___closed__11;
static lean_once_cell_t l_Lake_Toml_key___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_key___closed__12;
static lean_once_cell_t l_Lake_Toml_key___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_key___closed__13;
LEAN_EXPORT lean_object* l_Lake_Toml_key;
static const lean_string_object l_Lake_Toml_stdTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "stdTable"};
static const lean_object* l_Lake_Toml_stdTable___closed__0 = (const lean_object*)&l_Lake_Toml_stdTable___closed__0_value;
static const lean_ctor_object l_Lake_Toml_stdTable___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_stdTable___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_stdTable___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_stdTable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_stdTable___closed__1_value_aux_1),((lean_object*)&l_Lake_Toml_stdTable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(204, 45, 156, 80, 41, 178, 181, 196)}};
static const lean_object* l_Lake_Toml_stdTable___closed__1 = (const lean_object*)&l_Lake_Toml_stdTable___closed__1_value;
static const lean_string_object l_Lake_Toml_stdTable___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "table"};
static const lean_object* l_Lake_Toml_stdTable___closed__2 = (const lean_object*)&l_Lake_Toml_stdTable___closed__2_value;
static const lean_ctor_object l_Lake_Toml_stdTable___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_stdTable___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_stdTable___closed__3 = (const lean_object*)&l_Lake_Toml_stdTable___closed__3_value;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__4;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__5;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__6;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__7;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__8;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__9;
static const lean_string_object l_Lake_Toml_stdTable___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "'['"};
static const lean_object* l_Lake_Toml_stdTable___closed__10 = (const lean_object*)&l_Lake_Toml_stdTable___closed__10_value;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__11;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__12;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__13;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__14;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__15;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__16;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__17;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__18;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__19;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__20;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__21;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__22;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__23;
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable;
static const lean_string_object l_Lake_Toml_arrayTable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "arrayTable"};
static const lean_object* l_Lake_Toml_arrayTable___closed__0 = (const lean_object*)&l_Lake_Toml_arrayTable___closed__0_value;
static const lean_ctor_object l_Lake_Toml_arrayTable___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_arrayTable___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_arrayTable___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_arrayTable___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_arrayTable___closed__1_value_aux_1),((lean_object*)&l_Lake_Toml_arrayTable___closed__0_value),LEAN_SCALAR_PTR_LITERAL(199, 220, 56, 86, 146, 203, 81, 19)}};
static const lean_object* l_Lake_Toml_arrayTable___closed__1 = (const lean_object*)&l_Lake_Toml_arrayTable___closed__1_value;
static lean_once_cell_t l_Lake_Toml_arrayTable___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_arrayTable___closed__2;
static lean_once_cell_t l_Lake_Toml_arrayTable___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_arrayTable___closed__3;
static lean_once_cell_t l_Lake_Toml_arrayTable___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_arrayTable___closed__4;
static lean_once_cell_t l_Lake_Toml_arrayTable___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_arrayTable___closed__5;
static lean_once_cell_t l_Lake_Toml_arrayTable___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_arrayTable___closed__6;
static lean_once_cell_t l_Lake_Toml_arrayTable___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_arrayTable___closed__7;
static lean_once_cell_t l_Lake_Toml_arrayTable___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_arrayTable___closed__8;
static lean_once_cell_t l_Lake_Toml_arrayTable___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_arrayTable___closed__9;
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable;
static lean_once_cell_t l_Lake_Toml_table___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_table___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_table;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "keyval"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(105, 46, 78, 232, 161, 211, 209, 25)}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1_value;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(lean_object*);
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "expression"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(106, 203, 126, 0, 105, 98, 19, 240)}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(lean_object*);
static const lean_string_object l_Lake_Toml_header___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "header"};
static const lean_object* l_Lake_Toml_header___closed__0 = (const lean_object*)&l_Lake_Toml_header___closed__0_value;
static const lean_ctor_object l_Lake_Toml_header___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_header___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_header___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_header___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_header___closed__1_value_aux_1),((lean_object*)&l_Lake_Toml_header___closed__0_value),LEAN_SCALAR_PTR_LITERAL(169, 19, 11, 35, 86, 242, 57, 11)}};
static const lean_object* l_Lake_Toml_header___closed__1 = (const lean_object*)&l_Lake_Toml_header___closed__1_value;
static lean_once_cell_t l_Lake_Toml_header___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_header___closed__2;
LEAN_EXPORT lean_object* l_Lake_Toml_header;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "toml"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(241, 110, 132, 157, 201, 185, 149, 61)}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "sepBy"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__2 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__2_value),LEAN_SCALAR_PTR_LITERAL(196, 56, 254, 223, 11, 70, 55, 147)}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__3 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__3_value;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__4 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__4_value;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "line break"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__6 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__6_value;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore(lean_object*);
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "inlineTable"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(160, 125, 46, 131, 161, 142, 50, 23)}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1_value;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "inline-table"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__2 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__3 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5_value;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(lean_object*);
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "array"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1_value_aux_1),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 212, 239, 77, 14, 34, 57, 134)}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__2 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__2_value;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(lean_object*);
static const lean_string_object l_Lake_Toml_string___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "string"};
static const lean_object* l_Lake_Toml_string___closed__0 = (const lean_object*)&l_Lake_Toml_string___closed__0_value;
static const lean_ctor_object l_Lake_Toml_string___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_string___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_string___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_string___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_string___closed__1_value_aux_1),((lean_object*)&l_Lake_Toml_string___closed__0_value),LEAN_SCALAR_PTR_LITERAL(79, 134, 223, 178, 21, 25, 142, 203)}};
static const lean_object* l_Lake_Toml_string___closed__1 = (const lean_object*)&l_Lake_Toml_string___closed__1_value;
static const lean_ctor_object l_Lake_Toml_string___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_string___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_string___closed__2 = (const lean_object*)&l_Lake_Toml_string___closed__2_value;
static lean_once_cell_t l_Lake_Toml_string___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_string___closed__3;
static lean_once_cell_t l_Lake_Toml_string___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_string___closed__4;
static lean_once_cell_t l_Lake_Toml_string___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_string___closed__5;
static lean_once_cell_t l_Lake_Toml_string___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_string___closed__6;
static lean_once_cell_t l_Lake_Toml_string___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_string___closed__7;
LEAN_EXPORT lean_object* l_Lake_Toml_string;
static const lean_string_object l_Lake_Toml_true___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lake_Toml_true___closed__0 = (const lean_object*)&l_Lake_Toml_true___closed__0_value;
static const lean_ctor_object l_Lake_Toml_true___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_true___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_true___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_true___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_true___closed__1_value_aux_1),((lean_object*)&l_Lake_Toml_true___closed__0_value),LEAN_SCALAR_PTR_LITERAL(94, 186, 129, 3, 94, 77, 39, 82)}};
static const lean_object* l_Lake_Toml_true___closed__1 = (const lean_object*)&l_Lake_Toml_true___closed__1_value;
static const lean_string_object l_Lake_Toml_true___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "'true'"};
static const lean_object* l_Lake_Toml_true___closed__2 = (const lean_object*)&l_Lake_Toml_true___closed__2_value;
static const lean_ctor_object l_Lake_Toml_true___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_true___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_true___closed__3 = (const lean_object*)&l_Lake_Toml_true___closed__3_value;
static const lean_closure_object l_Lake_Toml_true___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_strFn, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lake_Toml_true___closed__0_value),((lean_object*)&l_Lake_Toml_true___closed__3_value)} };
static const lean_object* l_Lake_Toml_true___closed__4 = (const lean_object*)&l_Lake_Toml_true___closed__4_value;
static lean_once_cell_t l_Lake_Toml_true___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_true___closed__5;
LEAN_EXPORT lean_object* l_Lake_Toml_true;
static const lean_string_object l_Lake_Toml_false___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lake_Toml_false___closed__0 = (const lean_object*)&l_Lake_Toml_false___closed__0_value;
static const lean_ctor_object l_Lake_Toml_false___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_false___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_false___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_false___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_false___closed__1_value_aux_1),((lean_object*)&l_Lake_Toml_false___closed__0_value),LEAN_SCALAR_PTR_LITERAL(45, 94, 147, 128, 103, 18, 162, 55)}};
static const lean_object* l_Lake_Toml_false___closed__1 = (const lean_object*)&l_Lake_Toml_false___closed__1_value;
static const lean_string_object l_Lake_Toml_false___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "'false'"};
static const lean_object* l_Lake_Toml_false___closed__2 = (const lean_object*)&l_Lake_Toml_false___closed__2_value;
static const lean_ctor_object l_Lake_Toml_false___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_false___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_false___closed__3 = (const lean_object*)&l_Lake_Toml_false___closed__3_value;
static const lean_closure_object l_Lake_Toml_false___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*2, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_strFn, .m_arity = 4, .m_num_fixed = 2, .m_objs = {((lean_object*)&l_Lake_Toml_false___closed__0_value),((lean_object*)&l_Lake_Toml_false___closed__3_value)} };
static const lean_object* l_Lake_Toml_false___closed__4 = (const lean_object*)&l_Lake_Toml_false___closed__4_value;
static lean_once_cell_t l_Lake_Toml_false___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_false___closed__5;
LEAN_EXPORT lean_object* l_Lake_Toml_false;
static const lean_string_object l_Lake_Toml_boolean___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "boolean"};
static const lean_object* l_Lake_Toml_boolean___closed__0 = (const lean_object*)&l_Lake_Toml_boolean___closed__0_value;
static const lean_ctor_object l_Lake_Toml_boolean___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_boolean___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_boolean___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_boolean___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_boolean___closed__1_value_aux_1),((lean_object*)&l_Lake_Toml_boolean___closed__0_value),LEAN_SCALAR_PTR_LITERAL(76, 74, 28, 167, 158, 175, 30, 0)}};
static const lean_object* l_Lake_Toml_boolean___closed__1 = (const lean_object*)&l_Lake_Toml_boolean___closed__1_value;
static lean_once_cell_t l_Lake_Toml_boolean___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_boolean___closed__2;
static lean_once_cell_t l_Lake_Toml_boolean___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_boolean___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_boolean;
static lean_once_cell_t l_Lake_Toml_numeralAntiquot___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_numeralAntiquot___closed__0;
static lean_once_cell_t l_Lake_Toml_numeralAntiquot___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_numeralAntiquot___closed__1;
static lean_once_cell_t l_Lake_Toml_numeralAntiquot___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_numeralAntiquot___closed__2;
static lean_once_cell_t l_Lake_Toml_numeralAntiquot___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_numeralAntiquot___closed__3;
static lean_once_cell_t l_Lake_Toml_numeralAntiquot___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_numeralAntiquot___closed__4;
static lean_once_cell_t l_Lake_Toml_numeralAntiquot___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_numeralAntiquot___closed__5;
static const lean_string_object l_Lake_Toml_numeralAntiquot___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "numeral"};
static const lean_object* l_Lake_Toml_numeralAntiquot___closed__6 = (const lean_object*)&l_Lake_Toml_numeralAntiquot___closed__6_value;
static const lean_ctor_object l_Lake_Toml_numeralAntiquot___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_numeralAntiquot___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_numeralAntiquot___closed__7_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_numeralAntiquot___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_numeralAntiquot___closed__7_value_aux_1),((lean_object*)&l_Lake_Toml_numeralAntiquot___closed__6_value),LEAN_SCALAR_PTR_LITERAL(103, 24, 202, 101, 169, 12, 111, 38)}};
static const lean_object* l_Lake_Toml_numeralAntiquot___closed__7 = (const lean_object*)&l_Lake_Toml_numeralAntiquot___closed__7_value;
static lean_once_cell_t l_Lake_Toml_numeralAntiquot___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_numeralAntiquot___closed__8;
static lean_once_cell_t l_Lake_Toml_numeralAntiquot___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_numeralAntiquot___closed__9;
static lean_once_cell_t l_Lake_Toml_numeralAntiquot___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_numeralAntiquot___closed__10;
static lean_once_cell_t l_Lake_Toml_numeralAntiquot___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_numeralAntiquot___closed__11;
static lean_once_cell_t l_Lake_Toml_numeralAntiquot___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_numeralAntiquot___closed__12;
static lean_once_cell_t l_Lake_Toml_numeralAntiquot___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_numeralAntiquot___closed__13;
static lean_once_cell_t l_Lake_Toml_numeralAntiquot___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_numeralAntiquot___closed__14;
LEAN_EXPORT lean_object* l_Lake_Toml_numeralAntiquot;
static lean_once_cell_t l_Lake_Toml_numeral___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_numeral___closed__0;
static lean_once_cell_t l_Lake_Toml_numeral___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_numeral___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_numeral;
LEAN_EXPORT uint8_t l_Lake_Toml_numeralOfKind___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_numeralOfKind___lam__0___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lake_Toml_numeralOfKind___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "illegal numeral kind"};
static const lean_object* l_Lake_Toml_numeralOfKind___closed__0 = (const lean_object*)&l_Lake_Toml_numeralOfKind___closed__0_value;
LEAN_EXPORT lean_object* l_Lake_Toml_numeralOfKind(lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Toml_float___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_float___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_float;
static lean_once_cell_t l_Lake_Toml_decInt___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_decInt___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_decInt;
static const lean_string_object l_Lake_Toml_binNum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "binary number"};
static const lean_object* l_Lake_Toml_binNum___closed__0 = (const lean_object*)&l_Lake_Toml_binNum___closed__0_value;
static lean_once_cell_t l_Lake_Toml_binNum___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_binNum___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_binNum;
static const lean_string_object l_Lake_Toml_octNum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "octal number"};
static const lean_object* l_Lake_Toml_octNum___closed__0 = (const lean_object*)&l_Lake_Toml_octNum___closed__0_value;
static lean_once_cell_t l_Lake_Toml_octNum___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_octNum___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_octNum;
static const lean_string_object l_Lake_Toml_hexNum___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "hexadecimal number"};
static const lean_object* l_Lake_Toml_hexNum___closed__0 = (const lean_object*)&l_Lake_Toml_hexNum___closed__0_value;
static lean_once_cell_t l_Lake_Toml_hexNum___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_hexNum___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_hexNum;
static lean_once_cell_t l_Lake_Toml_dateTime___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_dateTime___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_dateTime;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_valCore(lean_object*);
static const lean_string_object l_Lake_Toml_val___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "val"};
static const lean_object* l_Lake_Toml_val___closed__0 = (const lean_object*)&l_Lake_Toml_val___closed__0_value;
static const lean_ctor_object l_Lake_Toml_val___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_val___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_val___closed__1_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_val___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_val___closed__1_value_aux_1),((lean_object*)&l_Lake_Toml_val___closed__0_value),LEAN_SCALAR_PTR_LITERAL(209, 33, 214, 61, 136, 139, 92, 226)}};
static const lean_object* l_Lake_Toml_val___closed__1 = (const lean_object*)&l_Lake_Toml_val___closed__1_value;
static const lean_closure_object l_Lake_Toml_val___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lake_Toml_Grammar_0__Lake_Toml_valCore, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_val___closed__2 = (const lean_object*)&l_Lake_Toml_val___closed__2_value;
static lean_once_cell_t l_Lake_Toml_val___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_val___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_val;
static lean_once_cell_t l_Lake_Toml_array___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_array___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_array;
static lean_once_cell_t l_Lake_Toml_inlineTable___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_inlineTable___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_inlineTable;
static lean_once_cell_t l_Lake_Toml_keyval___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_keyval___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_keyval;
static lean_once_cell_t l_Lake_Toml_expression___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_expression___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_expression;
LEAN_EXPORT lean_object* l_Lake_Toml_header_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_header_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Toml_simpleKey_formatter___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_simpleKey_formatter___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter___redArg();
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_key_formatter___closed__0___boxed__const__1;
static lean_once_cell_t l_Lake_Toml_key_formatter___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_key_formatter___closed__0;
static lean_once_cell_t l_Lake_Toml_key_formatter___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_key_formatter___closed__1;
static lean_once_cell_t l_Lake_Toml_key_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_key_formatter___closed__2;
static lean_once_cell_t l_Lake_Toml_key_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_key_formatter___closed__3;
static lean_once_cell_t l_Lake_Toml_key_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_key_formatter___closed__4;
LEAN_EXPORT lean_object* l_Lake_Toml_key_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_key_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
static lean_once_cell_t l_Lake_Toml_stdTable_formatter___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable_formatter___closed__0;
static lean_once_cell_t l_Lake_Toml_stdTable_formatter___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable_formatter___closed__1;
static lean_once_cell_t l_Lake_Toml_stdTable_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable_formatter___closed__2;
static lean_once_cell_t l_Lake_Toml_stdTable_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable_formatter___closed__3;
static lean_once_cell_t l_Lake_Toml_stdTable_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable_formatter___closed__4;
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1;
static lean_once_cell_t l_Lake_Toml_stdTable_formatter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable_formatter___closed__5;
static lean_once_cell_t l_Lake_Toml_stdTable_formatter___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable_formatter___closed__6;
static lean_once_cell_t l_Lake_Toml_stdTable_formatter___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable_formatter___closed__7;
static lean_once_cell_t l_Lake_Toml_stdTable_formatter___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable_formatter___closed__8;
static lean_once_cell_t l_Lake_Toml_stdTable_formatter___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable_formatter___closed__9;
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Toml_arrayTable_formatter___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_arrayTable_formatter___closed__0;
static lean_once_cell_t l_Lake_Toml_arrayTable_formatter___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_arrayTable_formatter___closed__1;
static lean_once_cell_t l_Lake_Toml_arrayTable_formatter___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_arrayTable_formatter___closed__2;
static lean_once_cell_t l_Lake_Toml_arrayTable_formatter___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_arrayTable_formatter___closed__3;
static lean_once_cell_t l_Lake_Toml_arrayTable_formatter___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_arrayTable_formatter___closed__4;
static lean_once_cell_t l_Lake_Toml_arrayTable_formatter___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_arrayTable_formatter___closed__5;
static lean_once_cell_t l_Lake_Toml_arrayTable_formatter___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_arrayTable_formatter___closed__6;
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_table_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_table_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_formatter___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0_value),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter___redArg();
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_val_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_val_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_toml_formatter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_toml_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_header_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_header_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Toml_simpleKey_parenthesizer___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_simpleKey_parenthesizer___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer___redArg();
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Toml_key_parenthesizer___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_key_parenthesizer___closed__0;
static lean_once_cell_t l_Lake_Toml_key_parenthesizer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_key_parenthesizer___closed__1;
static lean_once_cell_t l_Lake_Toml_key_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_key_parenthesizer___closed__2;
static lean_once_cell_t l_Lake_Toml_key_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_key_parenthesizer___closed__3;
static lean_once_cell_t l_Lake_Toml_key_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_key_parenthesizer___closed__4;
LEAN_EXPORT lean_object* l_Lake_Toml_key_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_key_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Toml_stdTable_parenthesizer___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable_parenthesizer___closed__0;
static lean_once_cell_t l_Lake_Toml_stdTable_parenthesizer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable_parenthesizer___closed__1;
static lean_once_cell_t l_Lake_Toml_stdTable_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable_parenthesizer___closed__2;
static lean_once_cell_t l_Lake_Toml_stdTable_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable_parenthesizer___closed__3;
static lean_once_cell_t l_Lake_Toml_stdTable_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable_parenthesizer___closed__4;
static lean_once_cell_t l_Lake_Toml_stdTable_parenthesizer___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable_parenthesizer___closed__5;
static lean_once_cell_t l_Lake_Toml_stdTable_parenthesizer___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable_parenthesizer___closed__6;
static lean_once_cell_t l_Lake_Toml_stdTable_parenthesizer___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable_parenthesizer___closed__7;
static lean_once_cell_t l_Lake_Toml_stdTable_parenthesizer___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable_parenthesizer___closed__8;
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Toml_arrayTable_parenthesizer___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_arrayTable_parenthesizer___closed__0;
static lean_once_cell_t l_Lake_Toml_arrayTable_parenthesizer___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_arrayTable_parenthesizer___closed__1;
static lean_once_cell_t l_Lake_Toml_arrayTable_parenthesizer___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_arrayTable_parenthesizer___closed__2;
static lean_once_cell_t l_Lake_Toml_arrayTable_parenthesizer___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_arrayTable_parenthesizer___closed__3;
static lean_once_cell_t l_Lake_Toml_arrayTable_parenthesizer___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_arrayTable_parenthesizer___closed__4;
static lean_once_cell_t l_Lake_Toml_arrayTable_parenthesizer___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_arrayTable_parenthesizer___closed__5;
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_table_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_table_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*4, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Parser_mkAntiquot_parenthesizer___boxed, .m_arity = 9, .m_num_fixed = 4, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0_value),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1_value),((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___closed__0 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer___redArg();
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_val_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_val_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_toml_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_toml_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lake_Toml_toml___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_toml___closed__0;
static lean_once_cell_t l_Lake_Toml_toml___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_toml___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_toml;
LEAN_EXPORT uint8_t l_Lake_Toml_isControlChar(uint32_t v_c_1_){
_start:
{
uint32_t v___x_2_; uint8_t v___x_3_; 
v___x_2_ = 127;
v___x_3_ = lean_uint32_dec_eq(v_c_1_, v___x_2_);
if (v___x_3_ == 0)
{
uint32_t v___x_4_; uint8_t v___x_5_; 
v___x_4_ = 32;
v___x_5_ = lean_uint32_dec_lt(v_c_1_, v___x_4_);
if (v___x_5_ == 0)
{
return v___x_5_;
}
else
{
uint32_t v___x_6_; uint8_t v___x_7_; 
v___x_6_ = 9;
v___x_7_ = lean_uint32_dec_eq(v_c_1_, v___x_6_);
if (v___x_7_ == 0)
{
return v___x_5_;
}
else
{
return v___x_3_;
}
}
}
else
{
return v___x_3_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_isControlChar___boxed(lean_object* v_c_8_){
_start:
{
uint32_t v_c_boxed_9_; uint8_t v_res_10_; lean_object* v_r_11_; 
v_c_boxed_9_ = lean_unbox_uint32(v_c_8_);
lean_dec(v_c_8_);
v_res_10_ = l_Lake_Toml_isControlChar(v_c_boxed_9_);
v_r_11_ = lean_box(v_res_10_);
return v_r_11_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_wsFn___lam__0(uint32_t v_c_12_){
_start:
{
uint32_t v___x_13_; uint8_t v___x_14_; 
v___x_13_ = 32;
v___x_14_ = lean_uint32_dec_eq(v_c_12_, v___x_13_);
if (v___x_14_ == 0)
{
uint32_t v___x_15_; uint8_t v___x_16_; 
v___x_15_ = 9;
v___x_16_ = lean_uint32_dec_eq(v_c_12_, v___x_15_);
return v___x_16_;
}
else
{
return v___x_14_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_wsFn___lam__0___boxed(lean_object* v_c_17_){
_start:
{
uint32_t v_c_boxed_18_; uint8_t v_res_19_; lean_object* v_r_20_; 
v_c_boxed_18_ = lean_unbox_uint32(v_c_17_);
lean_dec(v_c_17_);
v_res_19_ = l_Lake_Toml_wsFn___lam__0(v_c_boxed_18_);
v_r_20_ = lean_box(v_res_19_);
return v_r_20_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_wsFn(lean_object* v_a_22_, lean_object* v_a_23_){
_start:
{
lean_object* v___f_24_; lean_object* v___x_25_; 
v___f_24_ = ((lean_object*)(l_Lake_Toml_wsFn___closed__0));
v___x_25_ = l_Lean_Parser_takeWhileFn(v___f_24_, v_a_22_, v_a_23_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_wsFn___boxed(lean_object* v_a_26_, lean_object* v_a_27_){
_start:
{
lean_object* v_res_28_; 
v_res_28_ = l_Lake_Toml_wsFn(v_a_26_, v_a_27_);
lean_dec_ref(v_a_26_);
return v_res_28_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(lean_object* v_c_30_, lean_object* v_s_31_){
_start:
{
lean_object* v_toInputContext_32_; lean_object* v_pos_33_; lean_object* v_errMsg_34_; uint8_t v___x_35_; uint8_t v___x_36_; 
v_toInputContext_32_ = lean_ctor_get(v_c_30_, 0);
v_pos_33_ = lean_ctor_get(v_s_31_, 2);
v_errMsg_34_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___closed__0));
v___x_35_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_32_, v_pos_33_);
v___x_36_ = 1;
if (v___x_35_ == 0)
{
lean_object* v_inputString_37_; uint32_t v_curr_38_; uint32_t v___x_39_; uint8_t v___x_40_; 
v_inputString_37_ = lean_ctor_get(v_toInputContext_32_, 0);
v_curr_38_ = lean_string_utf8_get_fast(v_inputString_37_, v_pos_33_);
v___x_39_ = 10;
v___x_40_ = lean_uint32_dec_eq(v_curr_38_, v___x_39_);
if (v___x_40_ == 0)
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_box(0);
v___x_42_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_31_, v_errMsg_34_, v___x_41_, v___x_36_);
return v___x_42_;
}
else
{
lean_object* v___x_43_; 
lean_inc(v_pos_33_);
v___x_43_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_31_, v_c_30_, v_pos_33_);
lean_dec(v_pos_33_);
return v___x_43_;
}
}
else
{
lean_object* v___x_44_; lean_object* v___x_45_; 
v___x_44_ = lean_box(0);
v___x_45_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_31_, v_errMsg_34_, v___x_44_, v___x_36_);
return v___x_45_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___boxed(lean_object* v_c_46_, lean_object* v_s_47_){
_start:
{
lean_object* v_res_48_; 
v_res_48_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_46_, v_s_47_);
lean_dec_ref(v_c_46_);
return v_res_48_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_newlineFn(lean_object* v_c_53_, lean_object* v_s_54_){
_start:
{
lean_object* v_toInputContext_55_; lean_object* v_pos_56_; uint8_t v___x_57_; 
v_toInputContext_55_ = lean_ctor_get(v_c_53_, 0);
v_pos_56_ = lean_ctor_get(v_s_54_, 2);
v___x_57_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_55_, v_pos_56_);
if (v___x_57_ == 0)
{
lean_object* v_inputString_58_; uint32_t v_curr_59_; uint32_t v___x_60_; uint8_t v___x_61_; 
v_inputString_58_ = lean_ctor_get(v_toInputContext_55_, 0);
v_curr_59_ = lean_string_utf8_get_fast(v_inputString_58_, v_pos_56_);
v___x_60_ = 10;
v___x_61_ = lean_uint32_dec_eq(v_curr_59_, v___x_60_);
if (v___x_61_ == 0)
{
uint32_t v___x_62_; uint8_t v___x_63_; 
v___x_62_ = 13;
v___x_63_ = lean_uint32_dec_eq(v_curr_59_, v___x_62_);
if (v___x_63_ == 0)
{
uint8_t v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; 
v___x_64_ = 1;
v___x_65_ = ((lean_object*)(l_Lake_Toml_newlineFn___closed__1));
v___x_66_ = l_Lake_Toml_mkUnexpectedCharError(v_s_54_, v_curr_59_, v___x_65_, v___x_64_);
return v___x_66_;
}
else
{
lean_object* v___x_67_; lean_object* v___x_68_; 
lean_inc(v_pos_56_);
v___x_67_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_54_, v_c_53_, v_pos_56_);
lean_dec(v_pos_56_);
v___x_68_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_53_, v___x_67_);
return v___x_68_;
}
}
else
{
lean_object* v___x_69_; 
lean_inc(v_pos_56_);
v___x_69_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_54_, v_c_53_, v_pos_56_);
lean_dec(v_pos_56_);
return v___x_69_;
}
}
else
{
lean_object* v___x_70_; lean_object* v___x_71_; 
v___x_70_ = ((lean_object*)(l_Lake_Toml_newlineFn___closed__1));
v___x_71_ = l_Lean_Parser_ParserState_mkEOIError(v_s_54_, v___x_70_);
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_newlineFn___boxed(lean_object* v_c_72_, lean_object* v_s_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Lake_Toml_newlineFn(v_c_72_, v_s_73_);
lean_dec_ref(v_c_72_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(lean_object* v_a_76_, lean_object* v_a_77_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___closed__0));
v___x_79_ = l_Lean_Parser_takeUntilFn(v___x_78_, v_a_76_, v_a_77_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___boxed(lean_object* v_a_80_, lean_object* v_a_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(v_a_80_, v_a_81_);
lean_dec_ref(v_a_80_);
return v_res_82_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(lean_object* v_x_83_, lean_object* v_x_84_){
_start:
{
if (lean_obj_tag(v_x_83_) == 0)
{
if (lean_obj_tag(v_x_84_) == 0)
{
uint8_t v___x_85_; 
v___x_85_ = 1;
return v___x_85_;
}
else
{
uint8_t v___x_86_; 
v___x_86_ = 0;
return v___x_86_;
}
}
else
{
if (lean_obj_tag(v_x_84_) == 0)
{
uint8_t v___x_87_; 
v___x_87_ = 0;
return v___x_87_;
}
else
{
lean_object* v_val_88_; lean_object* v_val_89_; uint8_t v___x_90_; 
v_val_88_ = lean_ctor_get(v_x_83_, 0);
v_val_89_ = lean_ctor_get(v_x_84_, 0);
v___x_90_ = l_Lean_Parser_instBEqError_beq(v_val_88_, v_val_89_);
return v___x_90_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0___boxed(lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
uint8_t v_res_93_; lean_object* v_r_94_; 
v_res_93_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_x_91_, v_x_92_);
lean_dec(v_x_92_);
lean_dec(v_x_91_);
v_r_94_ = lean_box(v_res_93_);
return v_r_94_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_commentFn(lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
uint32_t v___x_101_; lean_object* v___x_102_; lean_object* v_s_103_; lean_object* v_errorMsg_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___x_101_ = 35;
v___x_102_ = ((lean_object*)(l_Lake_Toml_commentFn___closed__1));
v_s_103_ = l_Lake_Toml_chFn(v___x_101_, v___x_102_, v_a_99_, v_a_100_);
v_errorMsg_104_ = lean_ctor_get(v_s_103_, 4);
lean_inc(v_errorMsg_104_);
v___x_105_ = lean_box(0);
v___x_106_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_104_, v___x_105_);
lean_dec(v_errorMsg_104_);
if (v___x_106_ == 0)
{
return v_s_103_;
}
else
{
lean_object* v___x_107_; 
v___x_107_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(v_a_99_, v_s_103_);
return v___x_107_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_commentFn___boxed(lean_object* v_a_108_, lean_object* v_a_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_Lake_Toml_commentFn(v_a_108_, v_a_109_);
lean_dec_ref(v_a_108_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_wsNewlineFn(lean_object* v_c_111_, lean_object* v_s_112_){
_start:
{
lean_object* v_toInputContext_113_; lean_object* v_pos_114_; uint8_t v___x_118_; 
v_toInputContext_113_ = lean_ctor_get(v_c_111_, 0);
v_pos_114_ = lean_ctor_get(v_s_112_, 2);
v___x_118_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_113_, v_pos_114_);
if (v___x_118_ == 0)
{
lean_object* v_inputString_119_; uint32_t v_curr_120_; uint32_t v___x_121_; uint8_t v___x_122_; 
v_inputString_119_ = lean_ctor_get(v_toInputContext_113_, 0);
v_curr_120_ = lean_string_utf8_get_fast(v_inputString_119_, v_pos_114_);
v___x_121_ = 32;
v___x_122_ = lean_uint32_dec_eq(v_curr_120_, v___x_121_);
if (v___x_122_ == 0)
{
uint32_t v___x_123_; uint8_t v___x_124_; 
v___x_123_ = 9;
v___x_124_ = lean_uint32_dec_eq(v_curr_120_, v___x_123_);
if (v___x_124_ == 0)
{
uint32_t v___x_125_; uint8_t v___x_126_; 
v___x_125_ = 10;
v___x_126_ = lean_uint32_dec_eq(v_curr_120_, v___x_125_);
if (v___x_126_ == 0)
{
uint32_t v___x_127_; uint8_t v___x_128_; 
v___x_127_ = 13;
v___x_128_ = lean_uint32_dec_eq(v_curr_120_, v___x_127_);
if (v___x_128_ == 0)
{
return v_s_112_;
}
else
{
lean_object* v___x_129_; lean_object* v_s_130_; lean_object* v_errorMsg_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
lean_inc(v_pos_114_);
v___x_129_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_112_, v_c_111_, v_pos_114_);
lean_dec(v_pos_114_);
v_s_130_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_111_, v___x_129_);
v_errorMsg_131_ = lean_ctor_get(v_s_130_, 4);
lean_inc(v_errorMsg_131_);
v___x_132_ = lean_box(0);
v___x_133_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_131_, v___x_132_);
lean_dec(v_errorMsg_131_);
if (v___x_133_ == 0)
{
return v_s_130_;
}
else
{
v_s_112_ = v_s_130_;
goto _start;
}
}
}
else
{
lean_inc(v_pos_114_);
goto v___jp_115_;
}
}
else
{
lean_inc(v_pos_114_);
goto v___jp_115_;
}
}
else
{
lean_inc(v_pos_114_);
goto v___jp_115_;
}
}
else
{
return v_s_112_;
}
v___jp_115_:
{
lean_object* v___x_116_; 
v___x_116_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_112_, v_c_111_, v_pos_114_);
lean_dec(v_pos_114_);
v_s_112_ = v___x_116_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_wsNewlineFn___boxed(lean_object* v_c_135_, lean_object* v_s_136_){
_start:
{
lean_object* v_res_137_; 
v_res_137_ = l_Lake_Toml_wsNewlineFn(v_c_135_, v_s_136_);
lean_dec_ref(v_c_135_);
return v_res_137_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingFn(lean_object* v_c_138_, lean_object* v_s_139_){
_start:
{
lean_object* v_toInputContext_140_; lean_object* v_pos_141_; uint8_t v___x_145_; 
v_toInputContext_140_ = lean_ctor_get(v_c_138_, 0);
v_pos_141_ = lean_ctor_get(v_s_139_, 2);
v___x_145_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_140_, v_pos_141_);
if (v___x_145_ == 0)
{
lean_object* v_inputString_146_; uint32_t v_curr_147_; uint32_t v___x_148_; uint8_t v___x_149_; 
v_inputString_146_ = lean_ctor_get(v_toInputContext_140_, 0);
v_curr_147_ = lean_string_utf8_get_fast(v_inputString_146_, v_pos_141_);
v___x_148_ = 32;
v___x_149_ = lean_uint32_dec_eq(v_curr_147_, v___x_148_);
if (v___x_149_ == 0)
{
uint32_t v___x_150_; uint8_t v___x_151_; 
v___x_150_ = 9;
v___x_151_ = lean_uint32_dec_eq(v_curr_147_, v___x_150_);
if (v___x_151_ == 0)
{
uint32_t v___x_152_; uint8_t v___x_153_; 
v___x_152_ = 10;
v___x_153_ = lean_uint32_dec_eq(v_curr_147_, v___x_152_);
if (v___x_153_ == 0)
{
uint32_t v___x_154_; uint8_t v___x_155_; 
v___x_154_ = 13;
v___x_155_ = lean_uint32_dec_eq(v_curr_147_, v___x_154_);
if (v___x_155_ == 0)
{
uint32_t v___x_156_; uint8_t v___x_157_; 
v___x_156_ = 35;
v___x_157_ = lean_uint32_dec_eq(v_curr_147_, v___x_156_);
if (v___x_157_ == 0)
{
return v_s_139_;
}
else
{
lean_object* v___x_158_; lean_object* v_s_159_; lean_object* v_errorMsg_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
lean_inc(v_pos_141_);
v___x_158_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_139_, v_c_138_, v_pos_141_);
lean_dec(v_pos_141_);
v_s_159_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(v_c_138_, v___x_158_);
v_errorMsg_160_ = lean_ctor_get(v_s_159_, 4);
lean_inc(v_errorMsg_160_);
v___x_161_ = lean_box(0);
v___x_162_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_160_, v___x_161_);
lean_dec(v_errorMsg_160_);
if (v___x_162_ == 0)
{
return v_s_159_;
}
else
{
v_s_139_ = v_s_159_;
goto _start;
}
}
}
else
{
lean_object* v___x_164_; lean_object* v_s_165_; lean_object* v_errorMsg_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
lean_inc(v_pos_141_);
v___x_164_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_139_, v_c_138_, v_pos_141_);
lean_dec(v_pos_141_);
v_s_165_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_138_, v___x_164_);
v_errorMsg_166_ = lean_ctor_get(v_s_165_, 4);
lean_inc(v_errorMsg_166_);
v___x_167_ = lean_box(0);
v___x_168_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_166_, v___x_167_);
lean_dec(v_errorMsg_166_);
if (v___x_168_ == 0)
{
return v_s_165_;
}
else
{
v_s_139_ = v_s_165_;
goto _start;
}
}
}
else
{
lean_inc(v_pos_141_);
goto v___jp_142_;
}
}
else
{
lean_inc(v_pos_141_);
goto v___jp_142_;
}
}
else
{
lean_inc(v_pos_141_);
goto v___jp_142_;
}
}
else
{
return v_s_139_;
}
v___jp_142_:
{
lean_object* v___x_143_; 
v___x_143_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_139_, v_c_138_, v_pos_141_);
lean_dec(v_pos_141_);
v_s_139_ = v___x_143_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingFn___boxed(lean_object* v_c_170_, lean_object* v_s_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lake_Toml_trailingFn(v_c_170_, v_s_171_);
lean_dec_ref(v_c_170_);
return v_res_172_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_isEscapeChar(uint32_t v_c_173_){
_start:
{
uint32_t v___x_174_; uint8_t v___x_175_; 
v___x_174_ = 98;
v___x_175_ = lean_uint32_dec_eq(v_c_173_, v___x_174_);
if (v___x_175_ == 0)
{
uint32_t v___x_176_; uint8_t v___x_177_; 
v___x_176_ = 116;
v___x_177_ = lean_uint32_dec_eq(v_c_173_, v___x_176_);
if (v___x_177_ == 0)
{
uint32_t v___x_178_; uint8_t v___x_179_; 
v___x_178_ = 110;
v___x_179_ = lean_uint32_dec_eq(v_c_173_, v___x_178_);
if (v___x_179_ == 0)
{
uint32_t v___x_180_; uint8_t v___x_181_; 
v___x_180_ = 102;
v___x_181_ = lean_uint32_dec_eq(v_c_173_, v___x_180_);
if (v___x_181_ == 0)
{
uint32_t v___x_182_; uint8_t v___x_183_; 
v___x_182_ = 114;
v___x_183_ = lean_uint32_dec_eq(v_c_173_, v___x_182_);
if (v___x_183_ == 0)
{
uint32_t v___x_184_; uint8_t v___x_185_; 
v___x_184_ = 34;
v___x_185_ = lean_uint32_dec_eq(v_c_173_, v___x_184_);
if (v___x_185_ == 0)
{
uint32_t v___x_186_; uint8_t v___x_187_; 
v___x_186_ = 92;
v___x_187_ = lean_uint32_dec_eq(v_c_173_, v___x_186_);
return v___x_187_;
}
else
{
return v___x_185_;
}
}
else
{
return v___x_183_;
}
}
else
{
return v___x_181_;
}
}
else
{
return v___x_179_;
}
}
else
{
return v___x_177_;
}
}
else
{
return v___x_175_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_isEscapeChar___boxed(lean_object* v_c_188_){
_start:
{
uint32_t v_c_boxed_189_; uint8_t v_res_190_; lean_object* v_r_191_; 
v_c_boxed_189_ = lean_unbox_uint32(v_c_188_);
lean_dec(v_c_188_);
v_res_190_ = l_Lake_Toml_isEscapeChar(v_c_boxed_189_);
v_r_191_ = lean_box(v_res_190_);
return v_r_191_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0(lean_object* v___y_192_, lean_object* v___y_193_){
_start:
{
lean_object* v_s_194_; lean_object* v_errorMsg_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v_s_194_ = l_Lake_Toml_wsFn(v___y_192_, v___y_193_);
v_errorMsg_195_ = lean_ctor_get(v_s_194_, 4);
lean_inc(v_errorMsg_195_);
v___x_196_ = lean_box(0);
v___x_197_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_195_, v___x_196_);
lean_dec(v_errorMsg_195_);
if (v___x_197_ == 0)
{
return v_s_194_;
}
else
{
lean_object* v_s_198_; lean_object* v_errorMsg_199_; uint8_t v___x_200_; 
v_s_198_ = l_Lake_Toml_newlineFn(v___y_192_, v_s_194_);
v_errorMsg_199_ = lean_ctor_get(v_s_198_, 4);
lean_inc(v_errorMsg_199_);
v___x_200_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_199_, v___x_196_);
lean_dec(v_errorMsg_199_);
if (v___x_200_ == 0)
{
return v_s_198_;
}
else
{
lean_object* v___x_201_; 
v___x_201_ = l_Lake_Toml_wsNewlineFn(v___y_192_, v_s_198_);
return v___x_201_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0___boxed(lean_object* v___y_202_, lean_object* v___y_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0(v___y_202_, v___y_203_);
lean_dec_ref(v___y_202_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1(lean_object* v___y_205_, lean_object* v___y_206_){
_start:
{
lean_object* v_s_207_; lean_object* v_errorMsg_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v_s_207_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v___y_205_, v___y_206_);
v_errorMsg_208_ = lean_ctor_get(v_s_207_, 4);
lean_inc(v_errorMsg_208_);
v___x_209_ = lean_box(0);
v___x_210_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_208_, v___x_209_);
lean_dec(v_errorMsg_208_);
if (v___x_210_ == 0)
{
return v_s_207_;
}
else
{
lean_object* v___x_211_; 
v___x_211_ = l_Lake_Toml_wsNewlineFn(v___y_205_, v_s_207_);
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1___boxed(lean_object* v___y_212_, lean_object* v___y_213_){
_start:
{
lean_object* v_res_214_; 
v_res_214_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1(v___y_212_, v___y_213_);
lean_dec_ref(v___y_212_);
return v_res_214_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(lean_object* v_c_215_, lean_object* v_x_216_, lean_object* v_x_217_){
_start:
{
lean_object* v_zero_218_; uint8_t v_isZero_219_; 
v_zero_218_ = lean_unsigned_to_nat(0u);
v_isZero_219_ = lean_nat_dec_eq(v_x_216_, v_zero_218_);
if (v_isZero_219_ == 1)
{
lean_dec(v_x_216_);
return v_x_217_;
}
else
{
lean_object* v_s_220_; lean_object* v_errorMsg_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
v_s_220_ = l_Lean_Parser_hexDigitFn(v_c_215_, v_x_217_);
v_errorMsg_221_ = lean_ctor_get(v_s_220_, 4);
lean_inc(v_errorMsg_221_);
v___x_222_ = lean_box(0);
v___x_223_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_221_, v___x_222_);
lean_dec(v_errorMsg_221_);
if (v___x_223_ == 0)
{
lean_dec(v_x_216_);
return v_s_220_;
}
else
{
lean_object* v_one_224_; lean_object* v_n_225_; 
v_one_224_ = lean_unsigned_to_nat(1u);
v_n_225_ = lean_nat_sub(v_x_216_, v_one_224_);
lean_dec(v_x_216_);
v_x_216_ = v_n_225_;
v_x_217_ = v_s_220_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0___boxed(lean_object* v_c_227_, lean_object* v_x_228_, lean_object* v_x_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(v_c_227_, v_x_228_, v_x_229_);
lean_dec_ref(v_c_227_);
return v_res_230_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(uint8_t v_stringGap_240_, lean_object* v_c_241_, lean_object* v_s_242_){
_start:
{
lean_object* v_toInputContext_243_; lean_object* v_pos_244_; lean_object* v___x_245_; lean_object* v_expected_246_; uint8_t v___x_247_; 
v_toInputContext_243_ = lean_ctor_get(v_c_241_, 0);
v_pos_244_ = lean_ctor_get(v_s_242_, 2);
v___x_245_ = lean_box(0);
v_expected_246_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__1));
v___x_247_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_243_, v_pos_244_);
if (v___x_247_ == 0)
{
lean_object* v_inputString_248_; uint32_t v_curr_249_; uint8_t v___x_250_; 
v_inputString_248_ = lean_ctor_get(v_toInputContext_243_, 0);
v_curr_249_ = lean_string_utf8_get_fast(v_inputString_248_, v_pos_244_);
v___x_250_ = l_Lake_Toml_isEscapeChar(v_curr_249_);
if (v___x_250_ == 0)
{
uint32_t v___x_251_; uint8_t v___x_252_; 
v___x_251_ = 117;
v___x_252_ = lean_uint32_dec_eq(v_curr_249_, v___x_251_);
if (v___x_252_ == 0)
{
uint32_t v___x_253_; uint8_t v___x_254_; 
v___x_253_ = 85;
v___x_254_ = lean_uint32_dec_eq(v_curr_249_, v___x_253_);
if (v___x_254_ == 0)
{
lean_object* v___f_255_; uint8_t v___x_256_; lean_object* v_p_258_; uint32_t v___x_263_; uint8_t v___x_264_; 
v___f_255_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__2));
v___x_256_ = 1;
v___x_263_ = 32;
v___x_264_ = lean_uint32_dec_eq(v_curr_249_, v___x_263_);
if (v___x_264_ == 0)
{
uint32_t v___x_265_; uint8_t v___x_266_; 
v___x_265_ = 9;
v___x_266_ = lean_uint32_dec_eq(v_curr_249_, v___x_265_);
if (v___x_266_ == 0)
{
uint32_t v___x_267_; uint8_t v___x_268_; 
v___x_267_ = 10;
v___x_268_ = lean_uint32_dec_eq(v_curr_249_, v___x_267_);
if (v___x_268_ == 0)
{
uint32_t v___x_269_; uint8_t v___x_270_; 
v___x_269_ = 13;
v___x_270_ = lean_uint32_dec_eq(v_curr_249_, v___x_269_);
if (v___x_270_ == 0)
{
lean_object* v___x_271_; lean_object* v___x_272_; 
lean_dec_ref(v_c_241_);
v___x_271_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__4));
v___x_272_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_242_, v___x_271_, v___x_245_, v___x_256_);
return v___x_272_;
}
else
{
lean_object* v___f_273_; 
v___f_273_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__5));
v_p_258_ = v___f_273_;
goto v___jp_257_;
}
}
else
{
lean_object* v___x_274_; 
v___x_274_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__6));
v_p_258_ = v___x_274_;
goto v___jp_257_;
}
}
else
{
v_p_258_ = v___f_255_;
goto v___jp_257_;
}
}
else
{
v_p_258_ = v___f_255_;
goto v___jp_257_;
}
v___jp_257_:
{
if (v_stringGap_240_ == 0)
{
lean_object* v___x_259_; lean_object* v___x_260_; 
lean_dec_ref(v_c_241_);
v___x_259_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__3));
v___x_260_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_242_, v___x_259_, v_expected_246_, v___x_256_);
return v___x_260_;
}
else
{
lean_object* v___x_261_; lean_object* v___x_262_; 
lean_inc(v_pos_244_);
v___x_261_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_242_, v_c_241_, v_pos_244_);
lean_dec(v_pos_244_);
lean_inc_ref(v_p_258_);
v___x_262_ = lean_apply_2(v_p_258_, v_c_241_, v___x_261_);
return v___x_262_;
}
}
}
else
{
lean_object* v___x_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
lean_inc(v_pos_244_);
v___x_275_ = lean_unsigned_to_nat(8u);
v___x_276_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_242_, v_c_241_, v_pos_244_);
lean_dec(v_pos_244_);
v___x_277_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(v_c_241_, v___x_275_, v___x_276_);
lean_dec_ref(v_c_241_);
return v___x_277_;
}
}
else
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
lean_inc(v_pos_244_);
v___x_278_ = lean_unsigned_to_nat(4u);
v___x_279_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_242_, v_c_241_, v_pos_244_);
lean_dec(v_pos_244_);
v___x_280_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(v_c_241_, v___x_278_, v___x_279_);
lean_dec_ref(v_c_241_);
return v___x_280_;
}
}
else
{
lean_object* v___x_281_; 
lean_inc(v_pos_244_);
v___x_281_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_242_, v_c_241_, v_pos_244_);
lean_dec(v_pos_244_);
lean_dec_ref(v_c_241_);
return v___x_281_;
}
}
else
{
lean_object* v___x_282_; 
lean_dec_ref(v_c_241_);
v___x_282_ = l_Lean_Parser_ParserState_mkEOIError(v_s_242_, v_expected_246_);
return v___x_282_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___boxed(lean_object* v_stringGap_283_, lean_object* v_c_284_, lean_object* v_s_285_){
_start:
{
uint8_t v_stringGap_boxed_286_; lean_object* v_res_287_; 
v_stringGap_boxed_286_ = lean_unbox(v_stringGap_283_);
v_res_287_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(v_stringGap_boxed_286_, v_c_284_, v_s_285_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn(lean_object* v_startPos_289_, lean_object* v_c_290_, lean_object* v_s_291_){
_start:
{
lean_object* v_toInputContext_292_; lean_object* v_pos_293_; uint8_t v___x_294_; 
v_toInputContext_292_ = lean_ctor_get(v_c_290_, 0);
v_pos_293_ = lean_ctor_get(v_s_291_, 2);
v___x_294_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_292_, v_pos_293_);
if (v___x_294_ == 0)
{
lean_object* v_inputString_295_; uint32_t v_curr_296_; uint32_t v___x_297_; uint8_t v___x_298_; 
v_inputString_295_ = lean_ctor_get(v_toInputContext_292_, 0);
v_curr_296_ = lean_string_utf8_get_fast(v_inputString_295_, v_pos_293_);
v___x_297_ = 34;
v___x_298_ = lean_uint32_dec_eq(v_curr_296_, v___x_297_);
if (v___x_298_ == 0)
{
uint32_t v___x_299_; uint8_t v___x_300_; 
v___x_299_ = 92;
v___x_300_ = lean_uint32_dec_eq(v_curr_296_, v___x_299_);
if (v___x_300_ == 0)
{
uint8_t v___x_301_; 
v___x_301_ = l_Lake_Toml_isControlChar(v_curr_296_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; 
lean_inc(v_pos_293_);
v___x_302_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_291_, v_c_290_, v_pos_293_);
lean_dec(v_pos_293_);
v_s_291_ = v___x_302_;
goto _start;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; 
lean_dec_ref(v_c_290_);
lean_dec(v_startPos_289_);
v___x_304_ = lean_box(0);
v___x_305_ = l_Lake_Toml_mkUnexpectedCharError(v_s_291_, v_curr_296_, v___x_304_, v___x_301_);
return v___x_305_;
}
}
else
{
lean_object* v___x_306_; lean_object* v_s_307_; lean_object* v_errorMsg_308_; lean_object* v___x_309_; uint8_t v___x_310_; 
lean_inc(v_pos_293_);
v___x_306_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_291_, v_c_290_, v_pos_293_);
lean_dec(v_pos_293_);
lean_inc_ref(v_c_290_);
v_s_307_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(v___x_298_, v_c_290_, v___x_306_);
v_errorMsg_308_ = lean_ctor_get(v_s_307_, 4);
lean_inc(v_errorMsg_308_);
v___x_309_ = lean_box(0);
v___x_310_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_308_, v___x_309_);
lean_dec(v_errorMsg_308_);
if (v___x_310_ == 0)
{
lean_dec_ref(v_c_290_);
lean_dec(v_startPos_289_);
return v_s_307_;
}
else
{
v_s_291_ = v_s_307_;
goto _start;
}
}
}
else
{
lean_object* v___x_312_; 
lean_inc(v_pos_293_);
lean_dec(v_startPos_289_);
v___x_312_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_291_, v_c_290_, v_pos_293_);
lean_dec(v_pos_293_);
lean_dec_ref(v_c_290_);
return v___x_312_;
}
}
else
{
lean_object* v___x_313_; lean_object* v___x_314_; 
lean_dec_ref(v_c_290_);
v___x_313_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn___closed__0));
v___x_314_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_291_, v___x_313_, v_startPos_289_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicStringFn(lean_object* v_a_319_, lean_object* v_a_320_){
_start:
{
lean_object* v_pos_321_; uint32_t v___x_322_; lean_object* v___x_323_; lean_object* v_s_324_; lean_object* v_errorMsg_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v_pos_321_ = lean_ctor_get(v_a_320_, 2);
lean_inc(v_pos_321_);
v___x_322_ = 34;
v___x_323_ = ((lean_object*)(l_Lake_Toml_basicStringFn___closed__1));
v_s_324_ = l_Lake_Toml_chFn(v___x_322_, v___x_323_, v_a_319_, v_a_320_);
v_errorMsg_325_ = lean_ctor_get(v_s_324_, 4);
lean_inc(v_errorMsg_325_);
v___x_326_ = lean_box(0);
v___x_327_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_325_, v___x_326_);
lean_dec(v_errorMsg_325_);
if (v___x_327_ == 0)
{
lean_dec(v_pos_321_);
lean_dec_ref(v_a_319_);
return v_s_324_;
}
else
{
lean_object* v___x_328_; 
v___x_328_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn(v_pos_321_, v_a_319_, v_s_324_);
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(lean_object* v_startPos_330_, lean_object* v_c_331_, lean_object* v_s_332_){
_start:
{
lean_object* v_toInputContext_333_; lean_object* v_pos_334_; uint8_t v___x_335_; 
v_toInputContext_333_ = lean_ctor_get(v_c_331_, 0);
v_pos_334_ = lean_ctor_get(v_s_332_, 2);
v___x_335_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_333_, v_pos_334_);
if (v___x_335_ == 0)
{
lean_object* v_inputString_336_; uint32_t v_curr_337_; uint32_t v___x_338_; uint8_t v___x_339_; 
v_inputString_336_ = lean_ctor_get(v_toInputContext_333_, 0);
v_curr_337_ = lean_string_utf8_get_fast(v_inputString_336_, v_pos_334_);
v___x_338_ = 39;
v___x_339_ = lean_uint32_dec_eq(v_curr_337_, v___x_338_);
if (v___x_339_ == 0)
{
uint8_t v___x_340_; 
v___x_340_ = l_Lake_Toml_isControlChar(v_curr_337_);
if (v___x_340_ == 0)
{
lean_object* v___x_341_; 
lean_inc(v_pos_334_);
v___x_341_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_332_, v_c_331_, v_pos_334_);
lean_dec(v_pos_334_);
v_s_332_ = v___x_341_;
goto _start;
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; 
lean_dec(v_startPos_330_);
v___x_343_ = lean_box(0);
v___x_344_ = l_Lake_Toml_mkUnexpectedCharError(v_s_332_, v_curr_337_, v___x_343_, v___x_340_);
return v___x_344_;
}
}
else
{
lean_object* v___x_345_; 
lean_inc(v_pos_334_);
lean_dec(v_startPos_330_);
v___x_345_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_332_, v_c_331_, v_pos_334_);
lean_dec(v_pos_334_);
return v___x_345_;
}
}
else
{
lean_object* v___x_346_; lean_object* v___x_347_; 
v___x_346_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___closed__0));
v___x_347_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_332_, v___x_346_, v_startPos_330_);
return v___x_347_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___boxed(lean_object* v_startPos_348_, lean_object* v_c_349_, lean_object* v_s_350_){
_start:
{
lean_object* v_res_351_; 
v_res_351_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(v_startPos_348_, v_c_349_, v_s_350_);
lean_dec_ref(v_c_349_);
return v_res_351_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalStringFn(lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v_pos_358_; uint32_t v___x_359_; lean_object* v___x_360_; lean_object* v_s_361_; lean_object* v_errorMsg_362_; lean_object* v___x_363_; uint8_t v___x_364_; 
v_pos_358_ = lean_ctor_get(v_a_357_, 2);
lean_inc(v_pos_358_);
v___x_359_ = 39;
v___x_360_ = ((lean_object*)(l_Lake_Toml_literalStringFn___closed__1));
v_s_361_ = l_Lake_Toml_chFn(v___x_359_, v___x_360_, v_a_356_, v_a_357_);
v_errorMsg_362_ = lean_ctor_get(v_s_361_, 4);
lean_inc(v_errorMsg_362_);
v___x_363_ = lean_box(0);
v___x_364_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_362_, v___x_363_);
lean_dec(v_errorMsg_362_);
if (v___x_364_ == 0)
{
lean_dec(v_pos_358_);
return v_s_361_;
}
else
{
lean_object* v___x_365_; 
v___x_365_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(v_pos_358_, v_a_356_, v_s_361_);
return v___x_365_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalStringFn___boxed(lean_object* v_a_366_, lean_object* v_a_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_Lake_Toml_literalStringFn(v_a_366_, v_a_367_);
lean_dec_ref(v_a_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(lean_object* v_startPos_371_, lean_object* v_quoteDepth_372_, lean_object* v_c_373_, lean_object* v_s_374_){
_start:
{
lean_object* v_toInputContext_375_; lean_object* v_pos_376_; uint8_t v___x_377_; 
v_toInputContext_375_ = lean_ctor_get(v_c_373_, 0);
v_pos_376_ = lean_ctor_get(v_s_374_, 2);
v___x_377_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_375_, v_pos_376_);
if (v___x_377_ == 0)
{
lean_object* v_inputString_378_; uint8_t v___x_379_; uint32_t v_curr_380_; uint32_t v___x_381_; uint8_t v___x_382_; 
v_inputString_378_ = lean_ctor_get(v_toInputContext_375_, 0);
v___x_379_ = 1;
v_curr_380_ = lean_string_utf8_get_fast(v_inputString_378_, v_pos_376_);
v___x_381_ = 39;
v___x_382_ = lean_uint32_dec_eq(v_curr_380_, v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_383_ = lean_unsigned_to_nat(3u);
v___x_384_ = lean_nat_dec_le(v___x_383_, v_quoteDepth_372_);
lean_dec(v_quoteDepth_372_);
if (v___x_384_ == 0)
{
uint32_t v___x_385_; uint8_t v___x_386_; 
v___x_385_ = 10;
v___x_386_ = lean_uint32_dec_eq(v_curr_380_, v___x_385_);
if (v___x_386_ == 0)
{
uint32_t v___x_387_; uint8_t v___x_388_; 
v___x_387_ = 13;
v___x_388_ = lean_uint32_dec_eq(v_curr_380_, v___x_387_);
if (v___x_388_ == 0)
{
uint8_t v___x_389_; 
v___x_389_ = l_Lake_Toml_isControlChar(v_curr_380_);
if (v___x_389_ == 0)
{
lean_object* v___x_390_; lean_object* v___x_391_; 
lean_inc(v_pos_376_);
v___x_390_ = lean_unsigned_to_nat(0u);
v___x_391_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_374_, v_c_373_, v_pos_376_);
lean_dec(v_pos_376_);
v_quoteDepth_372_ = v___x_390_;
v_s_374_ = v___x_391_;
goto _start;
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; 
lean_dec(v_startPos_371_);
v___x_393_ = lean_box(0);
v___x_394_ = l_Lake_Toml_mkUnexpectedCharError(v_s_374_, v_curr_380_, v___x_393_, v___x_379_);
return v___x_394_;
}
}
else
{
lean_object* v___x_395_; lean_object* v_s_396_; lean_object* v_errorMsg_397_; lean_object* v___x_398_; uint8_t v___x_399_; 
lean_inc(v_pos_376_);
v___x_395_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_374_, v_c_373_, v_pos_376_);
lean_dec(v_pos_376_);
v_s_396_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_373_, v___x_395_);
v_errorMsg_397_ = lean_ctor_get(v_s_396_, 4);
lean_inc(v_errorMsg_397_);
v___x_398_ = lean_box(0);
v___x_399_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_397_, v___x_398_);
lean_dec(v_errorMsg_397_);
if (v___x_399_ == 0)
{
lean_dec(v_startPos_371_);
return v_s_396_;
}
else
{
lean_object* v___x_400_; 
v___x_400_ = lean_unsigned_to_nat(0u);
v_quoteDepth_372_ = v___x_400_;
v_s_374_ = v_s_396_;
goto _start;
}
}
}
else
{
lean_object* v___x_402_; lean_object* v___x_403_; 
lean_inc(v_pos_376_);
v___x_402_ = lean_unsigned_to_nat(0u);
v___x_403_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_374_, v_c_373_, v_pos_376_);
lean_dec(v_pos_376_);
v_quoteDepth_372_ = v___x_402_;
v_s_374_ = v___x_403_;
goto _start;
}
}
else
{
lean_dec(v_startPos_371_);
return v_s_374_;
}
}
else
{
lean_object* v_s_405_; lean_object* v___x_406_; uint8_t v___x_407_; 
lean_inc(v_pos_376_);
v_s_405_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_374_, v_c_373_, v_pos_376_);
lean_dec(v_pos_376_);
v___x_406_ = lean_unsigned_to_nat(5u);
v___x_407_ = lean_nat_dec_le(v___x_406_, v_quoteDepth_372_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = lean_unsigned_to_nat(1u);
v___x_409_ = lean_nat_add(v_quoteDepth_372_, v___x_408_);
lean_dec(v_quoteDepth_372_);
v_quoteDepth_372_ = v___x_409_;
v_s_374_ = v_s_405_;
goto _start;
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; 
lean_dec(v_quoteDepth_372_);
lean_dec(v_startPos_371_);
v___x_411_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0));
v___x_412_ = lean_box(0);
v___x_413_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_405_, v___x_411_, v___x_412_, v___x_379_);
return v___x_413_;
}
}
}
else
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = lean_unsigned_to_nat(3u);
v___x_415_ = lean_nat_dec_le(v___x_414_, v_quoteDepth_372_);
lean_dec(v_quoteDepth_372_);
if (v___x_415_ == 0)
{
lean_object* v___x_416_; lean_object* v___x_417_; 
v___x_416_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__1));
v___x_417_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_374_, v___x_416_, v_startPos_371_);
return v___x_417_;
}
else
{
lean_dec(v_startPos_371_);
return v_s_374_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___boxed(lean_object* v_startPos_418_, lean_object* v_quoteDepth_419_, lean_object* v_c_420_, lean_object* v_s_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(v_startPos_418_, v_quoteDepth_419_, v_c_420_, v_s_421_);
lean_dec_ref(v_c_420_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0(lean_object* v_c_427_, lean_object* v_x_428_, lean_object* v_x_429_){
_start:
{
lean_object* v_zero_430_; uint8_t v_isZero_431_; 
v_zero_430_ = lean_unsigned_to_nat(0u);
v_isZero_431_ = lean_nat_dec_eq(v_x_428_, v_zero_430_);
if (v_isZero_431_ == 1)
{
lean_dec(v_x_428_);
return v_x_429_;
}
else
{
uint32_t v___x_432_; lean_object* v___x_433_; lean_object* v_s_434_; lean_object* v_errorMsg_435_; lean_object* v___x_436_; uint8_t v___x_437_; 
v___x_432_ = 39;
v___x_433_ = ((lean_object*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__1));
v_s_434_ = l_Lake_Toml_chFn(v___x_432_, v___x_433_, v_c_427_, v_x_429_);
v_errorMsg_435_ = lean_ctor_get(v_s_434_, 4);
lean_inc(v_errorMsg_435_);
v___x_436_ = lean_box(0);
v___x_437_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_435_, v___x_436_);
lean_dec(v_errorMsg_435_);
if (v___x_437_ == 0)
{
lean_dec(v_x_428_);
return v_s_434_;
}
else
{
lean_object* v_one_438_; lean_object* v_n_439_; 
v_one_438_ = lean_unsigned_to_nat(1u);
v_n_439_ = lean_nat_sub(v_x_428_, v_one_438_);
lean_dec(v_x_428_);
v_x_428_ = v_n_439_;
v_x_429_ = v_s_434_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___boxed(lean_object* v_c_441_, lean_object* v_x_442_, lean_object* v_x_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0(v_c_441_, v_x_442_, v_x_443_);
lean_dec_ref(v_c_441_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralStringFn___lam__0(lean_object* v___x_445_, lean_object* v___y_446_, lean_object* v___y_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0(v___y_446_, v___x_445_, v___y_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralStringFn___lam__0___boxed(lean_object* v___x_449_, lean_object* v___y_450_, lean_object* v___y_451_){
_start:
{
lean_object* v_res_452_; 
v_res_452_ = l_Lake_Toml_mlLiteralStringFn___lam__0(v___x_449_, v___y_450_, v___y_451_);
lean_dec_ref(v___y_450_);
return v_res_452_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralStringFn(lean_object* v_a_455_, lean_object* v_a_456_){
_start:
{
lean_object* v_pos_457_; lean_object* v___f_458_; lean_object* v_s_459_; lean_object* v_errorMsg_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v_pos_457_ = lean_ctor_get(v_a_456_, 2);
lean_inc(v_pos_457_);
v___f_458_ = ((lean_object*)(l_Lake_Toml_mlLiteralStringFn___closed__0));
lean_inc_ref(v_a_455_);
v_s_459_ = l_Lean_Parser_atomicFn(v___f_458_, v_a_455_, v_a_456_);
v_errorMsg_460_ = lean_ctor_get(v_s_459_, 4);
lean_inc(v_errorMsg_460_);
v___x_461_ = lean_box(0);
v___x_462_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_460_, v___x_461_);
lean_dec(v_errorMsg_460_);
if (v___x_462_ == 0)
{
lean_dec(v_pos_457_);
lean_dec_ref(v_a_455_);
return v_s_459_;
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = lean_unsigned_to_nat(0u);
v___x_464_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(v_pos_457_, v___x_463_, v_a_455_, v_s_459_);
lean_dec_ref(v_a_455_);
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn(lean_object* v_startPos_466_, lean_object* v_quoteDepth_467_, lean_object* v_c_468_, lean_object* v_s_469_){
_start:
{
lean_object* v_toInputContext_470_; lean_object* v_pos_471_; uint8_t v___x_472_; 
v_toInputContext_470_ = lean_ctor_get(v_c_468_, 0);
v_pos_471_ = lean_ctor_get(v_s_469_, 2);
v___x_472_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_470_, v_pos_471_);
if (v___x_472_ == 0)
{
lean_object* v_inputString_473_; uint8_t v___x_474_; uint32_t v_curr_475_; uint32_t v___x_476_; uint8_t v___x_477_; 
v_inputString_473_ = lean_ctor_get(v_toInputContext_470_, 0);
v___x_474_ = 1;
v_curr_475_ = lean_string_utf8_get_fast(v_inputString_473_, v_pos_471_);
v___x_476_ = 34;
v___x_477_ = lean_uint32_dec_eq(v_curr_475_, v___x_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = lean_unsigned_to_nat(3u);
v___x_479_ = lean_nat_dec_le(v___x_478_, v_quoteDepth_467_);
lean_dec(v_quoteDepth_467_);
if (v___x_479_ == 0)
{
uint32_t v___x_480_; uint8_t v___x_481_; 
v___x_480_ = 10;
v___x_481_ = lean_uint32_dec_eq(v_curr_475_, v___x_480_);
if (v___x_481_ == 0)
{
uint32_t v___x_482_; uint8_t v___x_483_; 
v___x_482_ = 13;
v___x_483_ = lean_uint32_dec_eq(v_curr_475_, v___x_482_);
if (v___x_483_ == 0)
{
uint32_t v___x_484_; uint8_t v___x_485_; 
v___x_484_ = 92;
v___x_485_ = lean_uint32_dec_eq(v_curr_475_, v___x_484_);
if (v___x_485_ == 0)
{
uint8_t v___x_486_; 
v___x_486_ = l_Lake_Toml_isControlChar(v_curr_475_);
if (v___x_486_ == 0)
{
lean_object* v___x_487_; lean_object* v___x_488_; 
lean_inc(v_pos_471_);
v___x_487_ = lean_unsigned_to_nat(0u);
v___x_488_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_469_, v_c_468_, v_pos_471_);
lean_dec(v_pos_471_);
v_quoteDepth_467_ = v___x_487_;
v_s_469_ = v___x_488_;
goto _start;
}
else
{
lean_object* v___x_490_; lean_object* v___x_491_; 
lean_dec_ref(v_c_468_);
lean_dec(v_startPos_466_);
v___x_490_ = lean_box(0);
v___x_491_ = l_Lake_Toml_mkUnexpectedCharError(v_s_469_, v_curr_475_, v___x_490_, v___x_474_);
return v___x_491_;
}
}
else
{
lean_object* v___x_492_; lean_object* v_s_493_; lean_object* v_errorMsg_494_; lean_object* v___x_495_; uint8_t v___x_496_; 
lean_inc(v_pos_471_);
v___x_492_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_469_, v_c_468_, v_pos_471_);
lean_dec(v_pos_471_);
lean_inc_ref(v_c_468_);
v_s_493_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(v___x_474_, v_c_468_, v___x_492_);
v_errorMsg_494_ = lean_ctor_get(v_s_493_, 4);
lean_inc(v_errorMsg_494_);
v___x_495_ = lean_box(0);
v___x_496_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_494_, v___x_495_);
lean_dec(v_errorMsg_494_);
if (v___x_496_ == 0)
{
lean_dec_ref(v_c_468_);
lean_dec(v_startPos_466_);
return v_s_493_;
}
else
{
lean_object* v___x_497_; 
v___x_497_ = lean_unsigned_to_nat(0u);
v_quoteDepth_467_ = v___x_497_;
v_s_469_ = v_s_493_;
goto _start;
}
}
}
else
{
lean_object* v___x_499_; lean_object* v_s_500_; lean_object* v_errorMsg_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
lean_inc(v_pos_471_);
v___x_499_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_469_, v_c_468_, v_pos_471_);
lean_dec(v_pos_471_);
v_s_500_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_468_, v___x_499_);
v_errorMsg_501_ = lean_ctor_get(v_s_500_, 4);
lean_inc(v_errorMsg_501_);
v___x_502_ = lean_box(0);
v___x_503_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_501_, v___x_502_);
lean_dec(v_errorMsg_501_);
if (v___x_503_ == 0)
{
lean_dec_ref(v_c_468_);
lean_dec(v_startPos_466_);
return v_s_500_;
}
else
{
lean_object* v___x_504_; 
v___x_504_ = lean_unsigned_to_nat(0u);
v_quoteDepth_467_ = v___x_504_;
v_s_469_ = v_s_500_;
goto _start;
}
}
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; 
lean_inc(v_pos_471_);
v___x_506_ = lean_unsigned_to_nat(0u);
v___x_507_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_469_, v_c_468_, v_pos_471_);
lean_dec(v_pos_471_);
v_quoteDepth_467_ = v___x_506_;
v_s_469_ = v___x_507_;
goto _start;
}
}
else
{
lean_dec_ref(v_c_468_);
lean_dec(v_startPos_466_);
return v_s_469_;
}
}
else
{
lean_object* v_s_509_; lean_object* v___x_510_; uint8_t v___x_511_; 
lean_inc(v_pos_471_);
v_s_509_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_469_, v_c_468_, v_pos_471_);
lean_dec(v_pos_471_);
v___x_510_ = lean_unsigned_to_nat(5u);
v___x_511_ = lean_nat_dec_le(v___x_510_, v_quoteDepth_467_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
v___x_512_ = lean_unsigned_to_nat(1u);
v___x_513_ = lean_nat_add(v_quoteDepth_467_, v___x_512_);
lean_dec(v_quoteDepth_467_);
v_quoteDepth_467_ = v___x_513_;
v_s_469_ = v_s_509_;
goto _start;
}
else
{
lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
lean_dec_ref(v_c_468_);
lean_dec(v_quoteDepth_467_);
lean_dec(v_startPos_466_);
v___x_515_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0));
v___x_516_ = lean_box(0);
v___x_517_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_509_, v___x_515_, v___x_516_, v___x_474_);
return v___x_517_;
}
}
}
else
{
lean_object* v___x_518_; uint8_t v___x_519_; 
lean_dec_ref(v_c_468_);
v___x_518_ = lean_unsigned_to_nat(3u);
v___x_519_ = lean_nat_dec_le(v___x_518_, v_quoteDepth_467_);
lean_dec(v_quoteDepth_467_);
if (v___x_519_ == 0)
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn___closed__0));
v___x_521_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_469_, v___x_520_, v_startPos_466_);
return v___x_521_;
}
else
{
lean_dec(v_startPos_466_);
return v_s_469_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0(lean_object* v_c_526_, lean_object* v_x_527_, lean_object* v_x_528_){
_start:
{
lean_object* v_zero_529_; uint8_t v_isZero_530_; 
v_zero_529_ = lean_unsigned_to_nat(0u);
v_isZero_530_ = lean_nat_dec_eq(v_x_527_, v_zero_529_);
if (v_isZero_530_ == 1)
{
lean_dec(v_x_527_);
return v_x_528_;
}
else
{
uint32_t v___x_531_; lean_object* v___x_532_; lean_object* v_s_533_; lean_object* v_errorMsg_534_; lean_object* v___x_535_; uint8_t v___x_536_; 
v___x_531_ = 34;
v___x_532_ = ((lean_object*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__1));
v_s_533_ = l_Lake_Toml_chFn(v___x_531_, v___x_532_, v_c_526_, v_x_528_);
v_errorMsg_534_ = lean_ctor_get(v_s_533_, 4);
lean_inc(v_errorMsg_534_);
v___x_535_ = lean_box(0);
v___x_536_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_534_, v___x_535_);
lean_dec(v_errorMsg_534_);
if (v___x_536_ == 0)
{
lean_dec(v_x_527_);
return v_s_533_;
}
else
{
lean_object* v_one_537_; lean_object* v_n_538_; 
v_one_537_ = lean_unsigned_to_nat(1u);
v_n_538_ = lean_nat_sub(v_x_527_, v_one_537_);
lean_dec(v_x_527_);
v_x_527_ = v_n_538_;
v_x_528_ = v_s_533_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___boxed(lean_object* v_c_540_, lean_object* v_x_541_, lean_object* v_x_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0(v_c_540_, v_x_541_, v_x_542_);
lean_dec_ref(v_c_540_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicStringFn___lam__0(lean_object* v___x_544_, lean_object* v___y_545_, lean_object* v___y_546_){
_start:
{
lean_object* v___x_547_; 
v___x_547_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0(v___y_545_, v___x_544_, v___y_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicStringFn___lam__0___boxed(lean_object* v___x_548_, lean_object* v___y_549_, lean_object* v___y_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l_Lake_Toml_mlBasicStringFn___lam__0(v___x_548_, v___y_549_, v___y_550_);
lean_dec_ref(v___y_549_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicStringFn(lean_object* v_a_554_, lean_object* v_a_555_){
_start:
{
lean_object* v_pos_556_; lean_object* v___f_557_; lean_object* v_s_558_; lean_object* v_errorMsg_559_; lean_object* v___x_560_; uint8_t v___x_561_; 
v_pos_556_ = lean_ctor_get(v_a_555_, 2);
lean_inc(v_pos_556_);
v___f_557_ = ((lean_object*)(l_Lake_Toml_mlBasicStringFn___closed__0));
lean_inc_ref(v_a_554_);
v_s_558_ = l_Lean_Parser_atomicFn(v___f_557_, v_a_554_, v_a_555_);
v_errorMsg_559_ = lean_ctor_get(v_s_558_, 4);
lean_inc(v_errorMsg_559_);
v___x_560_ = lean_box(0);
v___x_561_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_559_, v___x_560_);
lean_dec(v_errorMsg_559_);
if (v___x_561_ == 0)
{
lean_dec(v_pos_556_);
lean_dec_ref(v_a_554_);
return v_s_558_;
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; 
v___x_562_ = lean_unsigned_to_nat(0u);
v___x_563_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn(v_pos_556_, v___x_562_, v_a_554_, v_s_558_);
return v___x_563_;
}
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4(void){
_start:
{
uint32_t v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; 
v___x_570_ = 58;
v___x_571_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_572_ = lean_string_push(v___x_571_, v___x_570_);
return v___x_572_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5(void){
_start:
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4, &l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4);
v___x_574_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_575_ = lean_string_append(v___x_574_, v___x_573_);
return v___x_575_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6(void){
_start:
{
lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_576_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_577_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5);
v___x_578_ = lean_string_append(v___x_577_, v___x_576_);
return v___x_578_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_579_ = lean_box(0);
v___x_580_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6, &l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6);
v___x_581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_581_, 0, v___x_580_);
lean_ctor_set(v___x_581_, 1, v___x_579_);
return v___x_581_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(lean_object* v_a_586_, lean_object* v_a_587_){
_start:
{
lean_object* v___x_588_; lean_object* v_s_589_; lean_object* v_errorMsg_590_; lean_object* v___x_591_; uint8_t v___x_592_; 
v___x_588_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__1));
v_s_589_ = l_Lake_Toml_digitPairFn(v___x_588_, v_a_586_, v_a_587_);
v_errorMsg_590_ = lean_ctor_get(v_s_589_, 4);
lean_inc(v_errorMsg_590_);
v___x_591_ = lean_box(0);
v___x_592_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_590_, v___x_591_);
lean_dec(v_errorMsg_590_);
if (v___x_592_ == 0)
{
return v_s_589_;
}
else
{
uint32_t v___x_593_; lean_object* v___x_594_; lean_object* v_s_595_; lean_object* v_errorMsg_596_; uint8_t v___x_597_; 
v___x_593_ = 58;
v___x_594_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7, &l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7);
v_s_595_ = l_Lake_Toml_chFn(v___x_593_, v___x_594_, v_a_586_, v_s_589_);
v_errorMsg_596_ = lean_ctor_get(v_s_595_, 4);
lean_inc(v_errorMsg_596_);
v___x_597_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_596_, v___x_591_);
lean_dec(v_errorMsg_596_);
if (v___x_597_ == 0)
{
return v_s_595_;
}
else
{
lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_598_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9));
v___x_599_ = l_Lake_Toml_digitPairFn(v___x_598_, v_a_586_, v_s_595_);
return v___x_599_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___boxed(lean_object* v_a_600_, lean_object* v_a_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(v_a_600_, v_a_601_);
lean_dec_ref(v_a_600_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn(uint8_t v_allowOffset_604_, uint32_t v_curr_605_, lean_object* v_nextPos_606_, lean_object* v_c_607_, lean_object* v_s_608_){
_start:
{
uint32_t v___x_615_; uint8_t v___x_616_; 
v___x_615_ = 90;
v___x_616_ = lean_uint32_dec_eq(v_curr_605_, v___x_615_);
if (v___x_616_ == 0)
{
uint32_t v___x_617_; uint8_t v___x_618_; 
v___x_617_ = 122;
v___x_618_ = lean_uint32_dec_eq(v_curr_605_, v___x_617_);
if (v___x_618_ == 0)
{
uint8_t v___x_619_; uint32_t v___x_626_; uint8_t v___x_627_; 
v___x_619_ = 1;
v___x_626_ = 43;
v___x_627_ = lean_uint32_dec_eq(v_curr_605_, v___x_626_);
if (v___x_627_ == 0)
{
uint32_t v___x_628_; uint8_t v___x_629_; 
v___x_628_ = 45;
v___x_629_ = lean_uint32_dec_eq(v_curr_605_, v___x_628_);
if (v___x_629_ == 0)
{
lean_dec(v_nextPos_606_);
return v_s_608_;
}
else
{
goto v___jp_620_;
}
}
else
{
goto v___jp_620_;
}
v___jp_620_:
{
if (v_allowOffset_604_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; 
lean_dec(v_nextPos_606_);
v___x_621_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_622_ = lean_box(0);
v___x_623_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_608_, v___x_621_, v___x_622_, v___x_619_);
return v___x_623_;
}
else
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = l_Lean_Parser_ParserState_setPos(v_s_608_, v_nextPos_606_);
v___x_625_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(v_c_607_, v___x_624_);
return v___x_625_;
}
}
}
else
{
goto v___jp_609_;
}
}
else
{
goto v___jp_609_;
}
v___jp_609_:
{
if (v_allowOffset_604_ == 0)
{
uint8_t v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
lean_dec(v_nextPos_606_);
v___x_610_ = 1;
v___x_611_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_612_ = lean_box(0);
v___x_613_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_608_, v___x_611_, v___x_612_, v___x_610_);
return v___x_613_;
}
else
{
lean_object* v___x_614_; 
v___x_614_ = l_Lean_Parser_ParserState_setPos(v_s_608_, v_nextPos_606_);
return v___x_614_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___boxed(lean_object* v_allowOffset_630_, lean_object* v_curr_631_, lean_object* v_nextPos_632_, lean_object* v_c_633_, lean_object* v_s_634_){
_start:
{
uint8_t v_allowOffset_boxed_635_; uint32_t v_curr_boxed_636_; lean_object* v_res_637_; 
v_allowOffset_boxed_635_ = lean_unbox(v_allowOffset_630_);
v_curr_boxed_636_ = lean_unbox_uint32(v_curr_631_);
lean_dec(v_curr_631_);
v_res_637_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn(v_allowOffset_boxed_635_, v_curr_boxed_636_, v_nextPos_632_, v_c_633_, v_s_634_);
lean_dec_ref(v_c_633_);
return v_res_637_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0(uint32_t v_x_638_){
_start:
{
uint32_t v___x_639_; uint8_t v___x_640_; 
v___x_639_ = 48;
v___x_640_ = lean_uint32_dec_le(v___x_639_, v_x_638_);
if (v___x_640_ == 0)
{
return v___x_640_;
}
else
{
uint32_t v___x_641_; uint8_t v___x_642_; 
v___x_641_ = 57;
v___x_642_ = lean_uint32_dec_le(v_x_638_, v___x_641_);
return v___x_642_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0___boxed(lean_object* v_x_643_){
_start:
{
uint32_t v_x_255__boxed_644_; uint8_t v_res_645_; lean_object* v_r_646_; 
v_x_255__boxed_644_ = lean_unbox_uint32(v_x_643_);
lean_dec(v_x_643_);
v_res_645_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0(v_x_255__boxed_644_);
v_r_646_ = lean_box(v_res_645_);
return v_r_646_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(uint8_t v_allowOffset_652_, lean_object* v_c_653_, lean_object* v_s_654_){
_start:
{
lean_object* v_toInputContext_655_; lean_object* v_pos_656_; uint8_t v___x_657_; 
v_toInputContext_655_ = lean_ctor_get(v_c_653_, 0);
v_pos_656_ = lean_ctor_get(v_s_654_, 2);
v___x_657_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_655_, v_pos_656_);
if (v___x_657_ == 0)
{
lean_object* v_inputString_658_; uint32_t v_curr_659_; uint32_t v___x_660_; uint8_t v___x_661_; 
v_inputString_658_ = lean_ctor_get(v_toInputContext_655_, 0);
v_curr_659_ = lean_string_utf8_get_fast(v_inputString_658_, v_pos_656_);
v___x_660_ = 46;
v___x_661_ = lean_uint32_dec_eq(v_curr_659_, v___x_660_);
if (v___x_661_ == 0)
{
lean_object* v___x_662_; uint32_t v___x_669_; uint8_t v___x_670_; 
v___x_662_ = lean_string_utf8_next_fast(v_inputString_658_, v_pos_656_);
v___x_669_ = 90;
v___x_670_ = lean_uint32_dec_eq(v_curr_659_, v___x_669_);
if (v___x_670_ == 0)
{
uint32_t v___x_671_; uint8_t v___x_672_; 
v___x_671_ = 122;
v___x_672_ = lean_uint32_dec_eq(v_curr_659_, v___x_671_);
if (v___x_672_ == 0)
{
uint8_t v___x_673_; uint32_t v___x_680_; uint8_t v___x_681_; 
v___x_673_ = 1;
v___x_680_ = 43;
v___x_681_ = lean_uint32_dec_eq(v_curr_659_, v___x_680_);
if (v___x_681_ == 0)
{
uint32_t v___x_682_; uint8_t v___x_683_; 
v___x_682_ = 45;
v___x_683_ = lean_uint32_dec_eq(v_curr_659_, v___x_682_);
if (v___x_683_ == 0)
{
return v_s_654_;
}
else
{
goto v___jp_674_;
}
}
else
{
goto v___jp_674_;
}
v___jp_674_:
{
if (v_allowOffset_652_ == 0)
{
lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; 
v___x_675_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_676_ = lean_box(0);
v___x_677_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_654_, v___x_675_, v___x_676_, v___x_673_);
return v___x_677_;
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; 
v___x_678_ = l_Lean_Parser_ParserState_setPos(v_s_654_, v___x_662_);
v___x_679_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(v_c_653_, v___x_678_);
return v___x_679_;
}
}
}
else
{
goto v___jp_663_;
}
}
else
{
goto v___jp_663_;
}
v___jp_663_:
{
if (v_allowOffset_652_ == 0)
{
uint8_t v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_664_ = 1;
v___x_665_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_666_ = lean_box(0);
v___x_667_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_654_, v___x_665_, v___x_666_, v___x_664_);
return v___x_667_;
}
else
{
lean_object* v___x_668_; 
v___x_668_ = l_Lean_Parser_ParserState_setPos(v_s_654_, v___x_662_);
return v___x_668_;
}
}
}
else
{
lean_object* v___f_684_; lean_object* v_s_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v_s_688_; lean_object* v_pos_689_; lean_object* v_errorMsg_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
lean_inc(v_pos_656_);
v___f_684_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0));
v_s_685_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_654_, v_c_653_, v_pos_656_);
lean_dec(v_pos_656_);
v___x_686_ = lean_box(0);
v___x_687_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__2));
v_s_688_ = l_Lake_Toml_takeWhile1Fn(v___f_684_, v___x_687_, v_c_653_, v_s_685_);
v_pos_689_ = lean_ctor_get(v_s_688_, 2);
lean_inc(v_pos_689_);
v_errorMsg_690_ = lean_ctor_get(v_s_688_, 4);
lean_inc(v_errorMsg_690_);
v___x_691_ = lean_box(0);
v___x_692_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_690_, v___x_691_);
lean_dec(v_errorMsg_690_);
if (v___x_692_ == 0)
{
lean_dec(v_pos_689_);
return v_s_688_;
}
else
{
if (v___x_657_ == 0)
{
uint8_t v___x_693_; 
v___x_693_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_655_, v_pos_689_);
if (v___x_693_ == 0)
{
uint32_t v___x_694_; lean_object* v___x_695_; uint32_t v___x_705_; uint8_t v___x_706_; 
v___x_694_ = lean_string_utf8_get_fast(v_inputString_658_, v_pos_689_);
v___x_695_ = lean_string_utf8_next_fast(v_inputString_658_, v_pos_689_);
lean_dec(v_pos_689_);
v___x_705_ = 90;
v___x_706_ = lean_uint32_dec_eq(v___x_694_, v___x_705_);
if (v___x_706_ == 0)
{
uint32_t v___x_707_; uint8_t v___x_708_; 
v___x_707_ = 122;
v___x_708_ = lean_uint32_dec_eq(v___x_694_, v___x_707_);
if (v___x_708_ == 0)
{
uint32_t v___x_709_; uint8_t v___x_710_; 
v___x_709_ = 43;
v___x_710_ = lean_uint32_dec_eq(v___x_694_, v___x_709_);
if (v___x_710_ == 0)
{
uint32_t v___x_711_; uint8_t v___x_712_; 
v___x_711_ = 45;
v___x_712_ = lean_uint32_dec_eq(v___x_694_, v___x_711_);
if (v___x_712_ == 0)
{
return v_s_688_;
}
else
{
goto v___jp_696_;
}
}
else
{
goto v___jp_696_;
}
}
else
{
goto v___jp_701_;
}
}
else
{
goto v___jp_701_;
}
v___jp_696_:
{
if (v_allowOffset_652_ == 0)
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_698_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_688_, v___x_697_, v___x_686_, v___x_661_);
return v___x_698_;
}
else
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = l_Lean_Parser_ParserState_setPos(v_s_688_, v___x_695_);
v___x_700_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(v_c_653_, v___x_699_);
return v___x_700_;
}
}
v___jp_701_:
{
if (v_allowOffset_652_ == 0)
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_703_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_688_, v___x_702_, v___x_686_, v___x_661_);
return v___x_703_;
}
else
{
lean_object* v___x_704_; 
v___x_704_ = l_Lean_Parser_ParserState_setPos(v_s_688_, v___x_695_);
return v___x_704_;
}
}
}
else
{
lean_dec(v_pos_689_);
return v_s_688_;
}
}
else
{
lean_dec(v_pos_689_);
return v_s_688_;
}
}
}
}
else
{
return v_s_654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___boxed(lean_object* v_allowOffset_713_, lean_object* v_c_714_, lean_object* v_s_715_){
_start:
{
uint8_t v_allowOffset_boxed_716_; lean_object* v_res_717_; 
v_allowOffset_boxed_716_ = lean_unbox(v_allowOffset_713_);
v_res_717_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(v_allowOffset_boxed_716_, v_c_714_, v_s_715_);
lean_dec_ref(v_c_714_);
return v_res_717_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(uint8_t v_allowOffset_722_, lean_object* v_a_723_, lean_object* v_a_724_){
_start:
{
lean_object* v___x_725_; lean_object* v_s_726_; lean_object* v_errorMsg_727_; lean_object* v___x_728_; uint8_t v___x_729_; 
v___x_725_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9));
v_s_726_ = l_Lake_Toml_digitPairFn(v___x_725_, v_a_723_, v_a_724_);
v_errorMsg_727_ = lean_ctor_get(v_s_726_, 4);
lean_inc(v_errorMsg_727_);
v___x_728_ = lean_box(0);
v___x_729_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_727_, v___x_728_);
lean_dec(v_errorMsg_727_);
if (v___x_729_ == 0)
{
return v_s_726_;
}
else
{
uint32_t v___x_730_; lean_object* v___x_731_; lean_object* v_s_732_; lean_object* v_errorMsg_733_; uint8_t v___x_734_; 
v___x_730_ = 58;
v___x_731_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7, &l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7);
v_s_732_ = l_Lake_Toml_chFn(v___x_730_, v___x_731_, v_a_723_, v_s_726_);
v_errorMsg_733_ = lean_ctor_get(v_s_732_, 4);
lean_inc(v_errorMsg_733_);
v___x_734_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_733_, v___x_728_);
lean_dec(v_errorMsg_733_);
if (v___x_734_ == 0)
{
return v_s_732_;
}
else
{
lean_object* v___x_735_; lean_object* v_s_736_; lean_object* v_errorMsg_737_; uint8_t v___x_738_; 
v___x_735_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__1));
v_s_736_ = l_Lake_Toml_digitPairFn(v___x_735_, v_a_723_, v_s_732_);
v_errorMsg_737_ = lean_ctor_get(v_s_736_, 4);
lean_inc(v_errorMsg_737_);
v___x_738_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_737_, v___x_728_);
lean_dec(v_errorMsg_737_);
if (v___x_738_ == 0)
{
return v_s_736_;
}
else
{
lean_object* v___x_739_; 
v___x_739_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(v_allowOffset_722_, v_a_723_, v_s_736_);
return v___x_739_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___boxed(lean_object* v_allowOffset_740_, lean_object* v_a_741_, lean_object* v_a_742_){
_start:
{
uint8_t v_allowOffset_boxed_743_; lean_object* v_res_744_; 
v_allowOffset_boxed_743_ = lean_unbox(v_allowOffset_740_);
v_res_744_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(v_allowOffset_boxed_743_, v_a_741_, v_a_742_);
lean_dec_ref(v_a_741_);
return v_res_744_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_timeFn(uint8_t v_allowOffset_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v___x_752_; lean_object* v_s_753_; lean_object* v_errorMsg_754_; lean_object* v___x_755_; uint8_t v___x_756_; 
v___x_752_ = ((lean_object*)(l_Lake_Toml_timeFn___closed__1));
v_s_753_ = l_Lake_Toml_digitPairFn(v___x_752_, v_a_750_, v_a_751_);
v_errorMsg_754_ = lean_ctor_get(v_s_753_, 4);
lean_inc(v_errorMsg_754_);
v___x_755_ = lean_box(0);
v___x_756_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_754_, v___x_755_);
lean_dec(v_errorMsg_754_);
if (v___x_756_ == 0)
{
return v_s_753_;
}
else
{
uint32_t v___x_757_; lean_object* v___x_758_; lean_object* v_s_759_; lean_object* v_errorMsg_760_; uint8_t v___x_761_; 
v___x_757_ = 58;
v___x_758_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7, &l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7);
v_s_759_ = l_Lake_Toml_chFn(v___x_757_, v___x_758_, v_a_750_, v_s_753_);
v_errorMsg_760_ = lean_ctor_get(v_s_759_, 4);
lean_inc(v_errorMsg_760_);
v___x_761_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_760_, v___x_755_);
lean_dec(v_errorMsg_760_);
if (v___x_761_ == 0)
{
return v_s_759_;
}
else
{
lean_object* v___x_762_; 
v___x_762_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(v_allowOffset_749_, v_a_750_, v_s_759_);
return v___x_762_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_timeFn___boxed(lean_object* v_allowOffset_763_, lean_object* v_a_764_, lean_object* v_a_765_){
_start:
{
uint8_t v_allowOffset_boxed_766_; lean_object* v_res_767_; 
v_allowOffset_boxed_766_ = lean_unbox(v_allowOffset_763_);
v_res_767_ = l_Lake_Toml_timeFn(v_allowOffset_boxed_766_, v_a_764_, v_a_765_);
lean_dec_ref(v_a_764_);
return v_res_767_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(lean_object* v_c_768_, lean_object* v_s_769_){
_start:
{
lean_object* v_pos_770_; lean_object* v_toInputContext_771_; uint8_t v___x_772_; 
v_pos_770_ = lean_ctor_get(v_s_769_, 2);
v_toInputContext_771_ = lean_ctor_get(v_c_768_, 0);
v___x_772_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_771_, v_pos_770_);
if (v___x_772_ == 0)
{
lean_object* v_inputString_773_; uint8_t v___x_774_; uint32_t v_curr_778_; uint32_t v___x_779_; uint8_t v___x_780_; 
v_inputString_773_ = lean_ctor_get(v_toInputContext_771_, 0);
v___x_774_ = 1;
v_curr_778_ = lean_string_utf8_get_fast(v_inputString_773_, v_pos_770_);
v___x_779_ = 84;
v___x_780_ = lean_uint32_dec_eq(v_curr_778_, v___x_779_);
if (v___x_780_ == 0)
{
uint32_t v___x_781_; uint8_t v___x_782_; 
v___x_781_ = 116;
v___x_782_ = lean_uint32_dec_eq(v_curr_778_, v___x_781_);
if (v___x_782_ == 0)
{
uint32_t v___x_783_; uint8_t v___x_784_; 
v___x_783_ = 32;
v___x_784_ = lean_uint32_dec_eq(v_curr_778_, v___x_783_);
if (v___x_784_ == 0)
{
return v_s_769_;
}
else
{
lean_object* v_tPos_785_; lean_object* v___x_786_; lean_object* v_s_787_; lean_object* v_pos_788_; lean_object* v_errorMsg_789_; lean_object* v___x_790_; uint8_t v___x_791_; 
lean_inc(v_pos_770_);
v_tPos_785_ = lean_string_utf8_next_fast(v_inputString_773_, v_pos_770_);
v___x_786_ = l_Lean_Parser_ParserState_setPos(v_s_769_, v_tPos_785_);
v_s_787_ = l_Lake_Toml_timeFn(v___x_774_, v_c_768_, v___x_786_);
v_pos_788_ = lean_ctor_get(v_s_787_, 2);
lean_inc(v_pos_788_);
v_errorMsg_789_ = lean_ctor_get(v_s_787_, 4);
lean_inc(v_errorMsg_789_);
v___x_790_ = lean_box(0);
v___x_791_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_789_, v___x_790_);
lean_dec(v_errorMsg_789_);
if (v___x_791_ == 0)
{
uint8_t v_decide_792_; 
v_decide_792_ = lean_nat_dec_eq(v_pos_788_, v_tPos_785_);
lean_dec(v_pos_788_);
if (v_decide_792_ == 0)
{
lean_dec(v_pos_770_);
return v_s_787_;
}
else
{
lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_793_ = l_Lean_Parser_ParserState_stackSize(v_s_787_);
v___x_794_ = lean_unsigned_to_nat(1u);
v___x_795_ = lean_nat_sub(v___x_793_, v___x_794_);
lean_dec(v___x_793_);
v___x_796_ = l_Lean_Parser_ParserState_restore(v_s_787_, v___x_795_, v_pos_770_);
lean_dec(v___x_795_);
return v___x_796_;
}
}
else
{
lean_dec(v_pos_788_);
lean_dec(v_pos_770_);
return v_s_787_;
}
}
}
else
{
lean_inc(v_pos_770_);
goto v___jp_775_;
}
}
else
{
lean_inc(v_pos_770_);
goto v___jp_775_;
}
v___jp_775_:
{
lean_object* v___x_776_; lean_object* v___x_777_; 
v___x_776_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_769_, v_c_768_, v_pos_770_);
lean_dec(v_pos_770_);
v___x_777_ = l_Lake_Toml_timeFn(v___x_774_, v_c_768_, v___x_776_);
return v___x_777_;
}
}
else
{
return v_s_769_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn___boxed(lean_object* v_c_797_, lean_object* v_s_798_){
_start:
{
lean_object* v_res_799_; 
v_res_799_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(v_c_797_, v_s_798_);
lean_dec_ref(v_c_797_);
return v_res_799_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2(void){
_start:
{
uint32_t v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_804_ = 45;
v___x_805_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_806_ = lean_string_push(v___x_805_, v___x_804_);
return v___x_806_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3(void){
_start:
{
lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; 
v___x_807_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2, &l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2);
v___x_808_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_809_ = lean_string_append(v___x_808_, v___x_807_);
return v___x_809_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4(void){
_start:
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; 
v___x_810_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_811_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3, &l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3);
v___x_812_ = lean_string_append(v___x_811_, v___x_810_);
return v___x_812_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5(void){
_start:
{
lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; 
v___x_813_ = lean_box(0);
v___x_814_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4, &l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4);
v___x_815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
lean_ctor_set(v___x_815_, 1, v___x_813_);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(lean_object* v_a_820_, lean_object* v_a_821_){
_start:
{
lean_object* v___x_822_; lean_object* v_s_823_; lean_object* v_errorMsg_824_; lean_object* v___x_825_; uint8_t v___x_826_; 
v___x_822_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__1));
v_s_823_ = l_Lake_Toml_digitPairFn(v___x_822_, v_a_820_, v_a_821_);
v_errorMsg_824_ = lean_ctor_get(v_s_823_, 4);
lean_inc(v_errorMsg_824_);
v___x_825_ = lean_box(0);
v___x_826_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_824_, v___x_825_);
lean_dec(v_errorMsg_824_);
if (v___x_826_ == 0)
{
return v_s_823_;
}
else
{
uint32_t v___x_827_; lean_object* v___x_828_; lean_object* v_s_829_; lean_object* v_errorMsg_830_; uint8_t v___x_831_; 
v___x_827_ = 45;
v___x_828_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5);
v_s_829_ = l_Lake_Toml_chFn(v___x_827_, v___x_828_, v_a_820_, v_s_823_);
v_errorMsg_830_ = lean_ctor_get(v_s_829_, 4);
lean_inc(v_errorMsg_830_);
v___x_831_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_830_, v___x_825_);
lean_dec(v_errorMsg_830_);
if (v___x_831_ == 0)
{
return v_s_829_;
}
else
{
lean_object* v___x_832_; lean_object* v_s_833_; lean_object* v_errorMsg_834_; uint8_t v___x_835_; 
v___x_832_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__7));
v_s_833_ = l_Lake_Toml_digitPairFn(v___x_832_, v_a_820_, v_s_829_);
v_errorMsg_834_ = lean_ctor_get(v_s_833_, 4);
lean_inc(v_errorMsg_834_);
v___x_835_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_834_, v___x_825_);
lean_dec(v_errorMsg_834_);
if (v___x_835_ == 0)
{
return v_s_833_;
}
else
{
lean_object* v___x_836_; 
v___x_836_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(v_a_820_, v_s_833_);
return v___x_836_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___boxed(lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(v_a_837_, v_a_838_);
lean_dec_ref(v_a_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0(lean_object* v_c_844_, lean_object* v_x_845_, lean_object* v_x_846_){
_start:
{
lean_object* v_zero_847_; uint8_t v_isZero_848_; 
v_zero_847_ = lean_unsigned_to_nat(0u);
v_isZero_848_ = lean_nat_dec_eq(v_x_845_, v_zero_847_);
if (v_isZero_848_ == 1)
{
lean_dec(v_x_845_);
return v_x_846_;
}
else
{
lean_object* v___x_849_; lean_object* v_s_850_; lean_object* v_errorMsg_851_; lean_object* v___x_852_; uint8_t v___x_853_; 
v___x_849_ = ((lean_object*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__1));
v_s_850_ = l_Lake_Toml_digitFn(v___x_849_, v_c_844_, v_x_846_);
v_errorMsg_851_ = lean_ctor_get(v_s_850_, 4);
lean_inc(v_errorMsg_851_);
v___x_852_ = lean_box(0);
v___x_853_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_851_, v___x_852_);
lean_dec(v_errorMsg_851_);
if (v___x_853_ == 0)
{
lean_dec(v_x_845_);
return v_s_850_;
}
else
{
lean_object* v_one_854_; lean_object* v_n_855_; 
v_one_854_ = lean_unsigned_to_nat(1u);
v_n_855_ = lean_nat_sub(v_x_845_, v_one_854_);
lean_dec(v_x_845_);
v_x_845_ = v_n_855_;
v_x_846_ = v_s_850_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___boxed(lean_object* v_c_857_, lean_object* v_x_858_, lean_object* v_x_859_){
_start:
{
lean_object* v_res_860_; 
v_res_860_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0(v_c_857_, v_x_858_, v_x_859_);
lean_dec_ref(v_c_857_);
return v_res_860_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dateTimeFn(lean_object* v_a_861_, lean_object* v_a_862_){
_start:
{
lean_object* v___x_863_; lean_object* v_s_864_; lean_object* v_errorMsg_865_; lean_object* v___x_866_; uint8_t v___x_867_; 
v___x_863_ = lean_unsigned_to_nat(4u);
v_s_864_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0(v_a_861_, v___x_863_, v_a_862_);
v_errorMsg_865_ = lean_ctor_get(v_s_864_, 4);
lean_inc(v_errorMsg_865_);
v___x_866_ = lean_box(0);
v___x_867_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_865_, v___x_866_);
lean_dec(v_errorMsg_865_);
if (v___x_867_ == 0)
{
return v_s_864_;
}
else
{
uint32_t v___x_868_; lean_object* v___x_869_; lean_object* v_s_870_; lean_object* v_errorMsg_871_; uint8_t v___x_872_; 
v___x_868_ = 45;
v___x_869_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5);
v_s_870_ = l_Lake_Toml_chFn(v___x_868_, v___x_869_, v_a_861_, v_s_864_);
v_errorMsg_871_ = lean_ctor_get(v_s_870_, 4);
lean_inc(v_errorMsg_871_);
v___x_872_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_871_, v___x_866_);
lean_dec(v_errorMsg_871_);
if (v___x_872_ == 0)
{
return v_s_870_;
}
else
{
lean_object* v___x_873_; 
v___x_873_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(v_a_861_, v_s_870_);
return v___x_873_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dateTimeFn___boxed(lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v_res_876_; 
v_res_876_ = l_Lake_Toml_dateTimeFn(v_a_874_, v_a_875_);
lean_dec_ref(v_a_874_);
return v_res_876_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(lean_object* v_c_881_, lean_object* v_s_882_){
_start:
{
lean_object* v_toInputContext_883_; lean_object* v_pos_884_; lean_object* v_expected_885_; uint8_t v___x_886_; 
v_toInputContext_883_ = lean_ctor_get(v_c_881_, 0);
v_pos_884_ = lean_ctor_get(v_s_882_, 2);
v_expected_885_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__1));
v___x_886_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_883_, v_pos_884_);
if (v___x_886_ == 0)
{
lean_object* v_inputString_887_; lean_object* v___f_888_; uint32_t v_curr_893_; uint32_t v___x_894_; uint8_t v___x_895_; 
v_inputString_887_ = lean_ctor_get(v_toInputContext_883_, 0);
v___f_888_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0));
v_curr_893_ = lean_string_utf8_get_fast(v_inputString_887_, v_pos_884_);
v___x_894_ = 45;
v___x_895_ = lean_uint32_dec_eq(v_curr_893_, v___x_894_);
if (v___x_895_ == 0)
{
uint32_t v___x_896_; uint8_t v___x_897_; 
v___x_896_ = 43;
v___x_897_ = lean_uint32_dec_eq(v_curr_893_, v___x_896_);
if (v___x_897_ == 0)
{
uint8_t v___x_898_; uint32_t v___x_899_; uint8_t v___x_900_; 
v___x_898_ = 1;
v___x_899_ = 48;
v___x_900_ = lean_uint32_dec_le(v___x_899_, v_curr_893_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; 
v___x_901_ = l_Lake_Toml_mkUnexpectedCharError(v_s_882_, v_curr_893_, v_expected_885_, v___x_898_);
return v___x_901_;
}
else
{
uint32_t v___x_902_; uint8_t v___x_903_; 
v___x_902_ = 57;
v___x_903_ = lean_uint32_dec_le(v_curr_893_, v___x_902_);
if (v___x_903_ == 0)
{
lean_object* v___x_904_; 
v___x_904_ = l_Lake_Toml_mkUnexpectedCharError(v_s_882_, v_curr_893_, v_expected_885_, v___x_898_);
return v___x_904_;
}
else
{
lean_object* v_s_905_; uint32_t v___x_906_; lean_object* v___x_907_; 
lean_inc(v_pos_884_);
v_s_905_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_882_, v_c_881_, v_pos_884_);
lean_dec(v_pos_884_);
v___x_906_ = 95;
v___x_907_ = l_Lake_Toml_sepByChar1AuxFn(v___f_888_, v___x_906_, v_expected_885_, v_c_881_, v_s_905_);
return v___x_907_;
}
}
}
else
{
lean_inc(v_pos_884_);
goto v___jp_889_;
}
}
else
{
lean_inc(v_pos_884_);
goto v___jp_889_;
}
v___jp_889_:
{
lean_object* v_s_890_; uint32_t v___x_891_; lean_object* v___x_892_; 
v_s_890_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_882_, v_c_881_, v_pos_884_);
lean_dec(v_pos_884_);
v___x_891_ = 95;
v___x_892_ = l_Lake_Toml_sepByChar1Fn(v___f_888_, v___x_891_, v_expected_885_, v_c_881_, v_s_890_);
return v___x_892_;
}
}
else
{
lean_object* v___x_908_; 
v___x_908_ = l_Lean_Parser_ParserState_mkEOIError(v_s_882_, v_expected_885_);
return v___x_908_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___boxed(lean_object* v_c_909_, lean_object* v_s_910_){
_start:
{
lean_object* v_res_911_; 
v_res_911_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(v_c_909_, v_s_910_);
lean_dec_ref(v_c_909_);
return v_res_911_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(lean_object* v_c_912_, lean_object* v_s_913_){
_start:
{
lean_object* v_toInputContext_914_; lean_object* v_pos_915_; uint8_t v___x_919_; 
v_toInputContext_914_ = lean_ctor_get(v_c_912_, 0);
v_pos_915_ = lean_ctor_get(v_s_913_, 2);
v___x_919_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_914_, v_pos_915_);
if (v___x_919_ == 0)
{
lean_object* v_inputString_920_; uint32_t v_curr_921_; uint32_t v___x_922_; uint8_t v___x_923_; 
v_inputString_920_ = lean_ctor_get(v_toInputContext_914_, 0);
v_curr_921_ = lean_string_utf8_get_fast(v_inputString_920_, v_pos_915_);
v___x_922_ = 101;
v___x_923_ = lean_uint32_dec_eq(v_curr_921_, v___x_922_);
if (v___x_923_ == 0)
{
uint32_t v___x_924_; uint8_t v___x_925_; 
v___x_924_ = 69;
v___x_925_ = lean_uint32_dec_eq(v_curr_921_, v___x_924_);
if (v___x_925_ == 0)
{
return v_s_913_;
}
else
{
lean_inc(v_pos_915_);
goto v___jp_916_;
}
}
else
{
lean_inc(v_pos_915_);
goto v___jp_916_;
}
}
else
{
return v_s_913_;
}
v___jp_916_:
{
lean_object* v___x_917_; lean_object* v___x_918_; 
v___x_917_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_913_, v_c_912_, v_pos_915_);
lean_dec(v_pos_915_);
v___x_918_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(v_c_912_, v___x_917_);
return v___x_918_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn___boxed(lean_object* v_c_926_, lean_object* v_s_927_){
_start:
{
lean_object* v_res_928_; 
v_res_928_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(v_c_926_, v_s_927_);
lean_dec_ref(v_c_926_);
return v_res_928_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(lean_object* v_startPos_946_, uint32_t v_curr_947_, lean_object* v_nextPos_948_, lean_object* v_c_949_, lean_object* v_s_950_){
_start:
{
uint32_t v___x_960_; uint8_t v___x_961_; 
v___x_960_ = 46;
v___x_961_ = lean_uint32_dec_eq(v_curr_947_, v___x_960_);
if (v___x_961_ == 0)
{
uint32_t v___x_962_; uint8_t v___x_963_; 
v___x_962_ = 101;
v___x_963_ = lean_uint32_dec_eq(v_curr_947_, v___x_962_);
if (v___x_963_ == 0)
{
uint32_t v___x_964_; uint8_t v___x_965_; 
v___x_964_ = 69;
v___x_965_ = lean_uint32_dec_eq(v_curr_947_, v___x_964_);
if (v___x_965_ == 0)
{
lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; 
lean_dec(v_nextPos_948_);
v___x_966_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_967_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_968_ = l_Lake_Toml_pushLit(v___x_966_, v_startPos_946_, v___x_967_, v_c_949_, v_s_950_);
return v___x_968_;
}
else
{
goto v___jp_951_;
}
}
else
{
goto v___jp_951_;
}
}
else
{
lean_object* v___f_969_; lean_object* v_s_970_; uint32_t v___x_971_; lean_object* v___x_972_; lean_object* v_s_973_; lean_object* v_errorMsg_974_; lean_object* v___x_975_; uint8_t v___x_976_; 
v___f_969_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0));
v_s_970_ = l_Lean_Parser_ParserState_setPos(v_s_950_, v_nextPos_948_);
v___x_971_ = 95;
v___x_972_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__8));
v_s_973_ = l_Lake_Toml_sepByChar1Fn(v___f_969_, v___x_971_, v___x_972_, v_c_949_, v_s_970_);
v_errorMsg_974_ = lean_ctor_get(v_s_973_, 4);
lean_inc(v_errorMsg_974_);
v___x_975_ = lean_box(0);
v___x_976_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_974_, v___x_975_);
lean_dec(v_errorMsg_974_);
if (v___x_976_ == 0)
{
lean_dec_ref(v_c_949_);
lean_dec(v_startPos_946_);
return v_s_973_;
}
else
{
lean_object* v_s_977_; lean_object* v_errorMsg_978_; uint8_t v___x_979_; 
v_s_977_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(v_c_949_, v_s_973_);
v_errorMsg_978_ = lean_ctor_get(v_s_977_, 4);
lean_inc(v_errorMsg_978_);
v___x_979_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_978_, v___x_975_);
lean_dec(v_errorMsg_978_);
if (v___x_979_ == 0)
{
lean_dec_ref(v_c_949_);
lean_dec(v_startPos_946_);
return v_s_977_;
}
else
{
lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_980_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_981_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_982_ = l_Lake_Toml_pushLit(v___x_980_, v_startPos_946_, v___x_981_, v_c_949_, v_s_977_);
return v___x_982_;
}
}
}
v___jp_951_:
{
lean_object* v_s_952_; lean_object* v_s_953_; lean_object* v_errorMsg_954_; lean_object* v___x_955_; uint8_t v___x_956_; 
v_s_952_ = l_Lean_Parser_ParserState_setPos(v_s_950_, v_nextPos_948_);
v_s_953_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(v_c_949_, v_s_952_);
v_errorMsg_954_ = lean_ctor_get(v_s_953_, 4);
lean_inc(v_errorMsg_954_);
v___x_955_ = lean_box(0);
v___x_956_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_954_, v___x_955_);
lean_dec(v_errorMsg_954_);
if (v___x_956_ == 0)
{
lean_dec_ref(v_c_949_);
lean_dec(v_startPos_946_);
return v_s_953_;
}
else
{
lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; 
v___x_957_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_958_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_959_ = l_Lake_Toml_pushLit(v___x_957_, v_startPos_946_, v___x_958_, v_c_949_, v_s_953_);
return v___x_959_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___boxed(lean_object* v_startPos_983_, lean_object* v_curr_984_, lean_object* v_nextPos_985_, lean_object* v_c_986_, lean_object* v_s_987_){
_start:
{
uint32_t v_curr_boxed_988_; lean_object* v_res_989_; 
v_curr_boxed_988_ = lean_unbox_uint32(v_curr_984_);
lean_dec(v_curr_984_);
v_res_989_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(v_startPos_983_, v_curr_boxed_988_, v_nextPos_985_, v_c_986_, v_s_987_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailFn(lean_object* v_startPos_990_, lean_object* v_c_991_, lean_object* v_s_992_){
_start:
{
lean_object* v_toInputContext_993_; lean_object* v_pos_994_; uint8_t v___x_995_; 
v_toInputContext_993_ = lean_ctor_get(v_c_991_, 0);
v_pos_994_ = lean_ctor_get(v_s_992_, 2);
v___x_995_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_993_, v_pos_994_);
if (v___x_995_ == 0)
{
lean_object* v_inputString_996_; uint32_t v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; 
v_inputString_996_ = lean_ctor_get(v_toInputContext_993_, 0);
v___x_997_ = lean_string_utf8_get_fast(v_inputString_996_, v_pos_994_);
v___x_998_ = lean_string_utf8_next_fast(v_inputString_996_, v_pos_994_);
v___x_999_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(v_startPos_990_, v___x_997_, v___x_998_, v_c_991_, v_s_992_);
return v___x_999_;
}
else
{
lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1000_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1001_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1002_ = l_Lake_Toml_pushLit(v___x_1000_, v_startPos_990_, v___x_1001_, v_c_991_, v_s_992_);
return v___x_1002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(lean_object* v_startPos_1010_, lean_object* v_c_1011_, lean_object* v_s_1012_){
_start:
{
lean_object* v_toInputContext_1013_; lean_object* v_pos_1014_; uint8_t v___x_1015_; 
v_toInputContext_1013_ = lean_ctor_get(v_c_1011_, 0);
v_pos_1014_ = lean_ctor_get(v_s_1012_, 2);
v___x_1015_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1013_, v_pos_1014_);
if (v___x_1015_ == 0)
{
lean_object* v_inputString_1016_; uint32_t v_curr_1017_; uint32_t v___x_1021_; uint8_t v___x_1022_; 
v_inputString_1016_ = lean_ctor_get(v_toInputContext_1013_, 0);
v_curr_1017_ = lean_string_utf8_get_fast(v_inputString_1016_, v_pos_1014_);
v___x_1021_ = 48;
v___x_1022_ = lean_uint32_dec_le(v___x_1021_, v_curr_1017_);
if (v___x_1022_ == 0)
{
goto v___jp_1018_;
}
else
{
uint32_t v___x_1023_; uint8_t v___x_1024_; 
v___x_1023_ = 57;
v___x_1024_ = lean_uint32_dec_le(v_curr_1017_, v___x_1023_);
if (v___x_1024_ == 0)
{
goto v___jp_1018_;
}
else
{
lean_object* v_s_1025_; 
lean_inc(v_pos_1014_);
v_s_1025_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1012_, v_c_1011_, v_pos_1014_);
lean_dec(v_pos_1014_);
v_s_1012_ = v_s_1025_;
goto _start;
}
}
v___jp_1018_:
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1019_ = lean_string_utf8_next_fast(v_inputString_1016_, v_pos_1014_);
v___x_1020_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1010_, v_curr_1017_, v___x_1019_, v_c_1011_, v_s_1012_);
return v___x_1020_;
}
}
else
{
lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; 
v___x_1027_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1028_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1029_ = l_Lake_Toml_pushLit(v___x_1027_, v_startPos_1010_, v___x_1028_, v_c_1011_, v_s_1012_);
return v___x_1029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn(lean_object* v_startPos_1030_, lean_object* v_c_1031_, lean_object* v_s_1032_){
_start:
{
lean_object* v_pos_1033_; lean_object* v_toInputContext_1034_; lean_object* v_expected_1035_; uint8_t v___x_1036_; 
v_pos_1033_ = lean_ctor_get(v_s_1032_, 2);
v_toInputContext_1034_ = lean_ctor_get(v_c_1031_, 0);
v_expected_1035_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2));
v___x_1036_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1034_, v_pos_1033_);
if (v___x_1036_ == 0)
{
lean_object* v_inputString_1037_; uint8_t v___x_1038_; uint32_t v_curr_1039_; uint32_t v___x_1040_; uint8_t v___x_1041_; 
v_inputString_1037_ = lean_ctor_get(v_toInputContext_1034_, 0);
v___x_1038_ = 1;
v_curr_1039_ = lean_string_utf8_get_fast(v_inputString_1037_, v_pos_1033_);
v___x_1040_ = 48;
v___x_1041_ = lean_uint32_dec_le(v___x_1040_, v_curr_1039_);
if (v___x_1041_ == 0)
{
lean_object* v___x_1042_; 
lean_dec_ref(v_c_1031_);
lean_dec(v_startPos_1030_);
v___x_1042_ = l_Lake_Toml_mkUnexpectedCharError(v_s_1032_, v_curr_1039_, v_expected_1035_, v___x_1038_);
return v___x_1042_;
}
else
{
uint32_t v___x_1043_; uint8_t v___x_1044_; 
v___x_1043_ = 57;
v___x_1044_ = lean_uint32_dec_le(v_curr_1039_, v___x_1043_);
if (v___x_1044_ == 0)
{
lean_object* v___x_1045_; 
lean_dec_ref(v_c_1031_);
lean_dec(v_startPos_1030_);
v___x_1045_ = l_Lake_Toml_mkUnexpectedCharError(v_s_1032_, v_curr_1039_, v_expected_1035_, v___x_1038_);
return v___x_1045_;
}
else
{
lean_object* v_s_1046_; lean_object* v___x_1047_; 
lean_inc(v_pos_1033_);
v_s_1046_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1032_, v_c_1031_, v_pos_1033_);
lean_dec(v_pos_1033_);
v___x_1047_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(v_startPos_1030_, v_c_1031_, v_s_1046_);
return v___x_1047_;
}
}
}
else
{
lean_object* v___x_1048_; 
lean_dec_ref(v_c_1031_);
lean_dec(v_startPos_1030_);
v___x_1048_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1032_, v_expected_1035_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(lean_object* v_startPos_1049_, uint32_t v_curr_1050_, lean_object* v_nextPos_1051_, lean_object* v_c_1052_, lean_object* v_s_1053_){
_start:
{
uint32_t v___x_1054_; uint8_t v___x_1055_; 
v___x_1054_ = 95;
v___x_1055_ = lean_uint32_dec_eq(v_curr_1050_, v___x_1054_);
if (v___x_1055_ == 0)
{
lean_object* v___x_1056_; 
v___x_1056_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(v_startPos_1049_, v_curr_1050_, v_nextPos_1051_, v_c_1052_, v_s_1053_);
return v___x_1056_;
}
else
{
lean_object* v_s_1057_; lean_object* v___x_1058_; 
v_s_1057_ = l_Lean_Parser_ParserState_setPos(v_s_1053_, v_nextPos_1051_);
v___x_1058_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn(v_startPos_1049_, v_c_1052_, v_s_1057_);
return v___x_1058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn___boxed(lean_object* v_startPos_1059_, lean_object* v_curr_1060_, lean_object* v_nextPos_1061_, lean_object* v_c_1062_, lean_object* v_s_1063_){
_start:
{
uint32_t v_curr_boxed_1064_; lean_object* v_res_1065_; 
v_curr_boxed_1064_ = lean_unbox_uint32(v_curr_1060_);
lean_dec(v_curr_1060_);
v_res_1065_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1059_, v_curr_boxed_1064_, v_nextPos_1061_, v_c_1062_, v_s_1063_);
return v_res_1065_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(lean_object* v_startPos_1071_, lean_object* v_a_1072_, lean_object* v_a_1073_){
_start:
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v_s_1076_; lean_object* v_errorMsg_1077_; lean_object* v___x_1078_; uint8_t v___x_1079_; 
v___x_1074_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__0));
v___x_1075_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__2));
lean_inc_ref(v_a_1072_);
v_s_1076_ = l_Lake_Toml_strFn(v___x_1074_, v___x_1075_, v_a_1072_, v_a_1073_);
v_errorMsg_1077_ = lean_ctor_get(v_s_1076_, 4);
lean_inc(v_errorMsg_1077_);
v___x_1078_ = lean_box(0);
v___x_1079_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1077_, v___x_1078_);
lean_dec(v_errorMsg_1077_);
if (v___x_1079_ == 0)
{
lean_dec_ref(v_a_1072_);
lean_dec(v_startPos_1071_);
return v_s_1076_;
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1080_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_1081_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1082_ = l_Lake_Toml_pushLit(v___x_1080_, v_startPos_1071_, v___x_1081_, v_a_1072_, v_s_1076_);
return v___x_1082_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(lean_object* v_startPos_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v_s_1093_; lean_object* v_errorMsg_1094_; lean_object* v___x_1095_; uint8_t v___x_1096_; 
v___x_1091_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__0));
v___x_1092_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__2));
lean_inc_ref(v_a_1089_);
v_s_1093_ = l_Lake_Toml_strFn(v___x_1091_, v___x_1092_, v_a_1089_, v_a_1090_);
v_errorMsg_1094_ = lean_ctor_get(v_s_1093_, 4);
lean_inc(v_errorMsg_1094_);
v___x_1095_ = lean_box(0);
v___x_1096_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1094_, v___x_1095_);
lean_dec(v_errorMsg_1094_);
if (v___x_1096_ == 0)
{
lean_dec_ref(v_a_1089_);
lean_dec(v_startPos_1088_);
return v_s_1093_;
}
else
{
lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1097_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_1098_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1099_ = l_Lake_Toml_pushLit(v___x_1097_, v_startPos_1088_, v___x_1098_, v_a_1089_, v_s_1093_);
return v___x_1099_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decimalFn(lean_object* v_startPos_1100_, lean_object* v_c_1101_, lean_object* v_s_1102_){
_start:
{
lean_object* v_toInputContext_1103_; lean_object* v_pos_1104_; lean_object* v_expected_1105_; uint8_t v___x_1106_; 
v_toInputContext_1103_ = lean_ctor_get(v_c_1101_, 0);
v_pos_1104_ = lean_ctor_get(v_s_1102_, 2);
v_expected_1105_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2));
v___x_1106_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1103_, v_pos_1104_);
if (v___x_1106_ == 0)
{
lean_object* v_inputString_1107_; uint32_t v_curr_1108_; uint32_t v___x_1109_; uint8_t v___x_1110_; 
v_inputString_1107_ = lean_ctor_get(v_toInputContext_1103_, 0);
v_curr_1108_ = lean_string_utf8_get_fast(v_inputString_1107_, v_pos_1104_);
v___x_1109_ = 48;
v___x_1110_ = lean_uint32_dec_eq(v_curr_1108_, v___x_1109_);
if (v___x_1110_ == 0)
{
uint8_t v___x_1111_; uint8_t v___x_1122_; 
v___x_1111_ = 1;
v___x_1122_ = lean_uint32_dec_le(v___x_1109_, v_curr_1108_);
if (v___x_1122_ == 0)
{
goto v___jp_1112_;
}
else
{
uint32_t v___x_1123_; uint8_t v___x_1124_; 
v___x_1123_ = 57;
v___x_1124_ = lean_uint32_dec_le(v_curr_1108_, v___x_1123_);
if (v___x_1124_ == 0)
{
goto v___jp_1112_;
}
else
{
lean_object* v___x_1125_; lean_object* v___x_1126_; 
lean_inc(v_pos_1104_);
v___x_1125_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1102_, v_c_1101_, v_pos_1104_);
lean_dec(v_pos_1104_);
v___x_1126_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(v_startPos_1100_, v_c_1101_, v___x_1125_);
return v___x_1126_;
}
}
v___jp_1112_:
{
uint32_t v___x_1113_; uint8_t v___x_1114_; 
v___x_1113_ = 105;
v___x_1114_ = lean_uint32_dec_eq(v_curr_1108_, v___x_1113_);
if (v___x_1114_ == 0)
{
uint32_t v___x_1115_; uint8_t v___x_1116_; 
v___x_1115_ = 110;
v___x_1116_ = lean_uint32_dec_eq(v_curr_1108_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_object* v___x_1117_; 
lean_dec_ref(v_c_1101_);
lean_dec(v_startPos_1100_);
v___x_1117_ = l_Lake_Toml_mkUnexpectedCharError(v_s_1102_, v_curr_1108_, v_expected_1105_, v___x_1111_);
return v___x_1117_;
}
else
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
lean_inc(v_pos_1104_);
v___x_1118_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1102_, v_c_1101_, v_pos_1104_);
lean_dec(v_pos_1104_);
v___x_1119_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(v_startPos_1100_, v_c_1101_, v___x_1118_);
return v___x_1119_;
}
}
else
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
lean_inc(v_pos_1104_);
v___x_1120_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1102_, v_c_1101_, v_pos_1104_);
lean_dec(v_pos_1104_);
v___x_1121_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(v_startPos_1100_, v_c_1101_, v___x_1120_);
return v___x_1121_;
}
}
}
else
{
lean_object* v___x_1127_; lean_object* v___x_1128_; 
lean_inc(v_pos_1104_);
v___x_1127_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1102_, v_c_1101_, v_pos_1104_);
lean_dec(v_pos_1104_);
v___x_1128_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailFn(v_startPos_1100_, v_c_1101_, v___x_1127_);
return v___x_1128_;
}
}
else
{
lean_object* v___x_1129_; 
lean_dec_ref(v_c_1101_);
lean_dec(v_startPos_1100_);
v___x_1129_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1102_, v_expected_1105_);
return v___x_1129_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn(lean_object* v_startPos_1145_, lean_object* v_c_1146_, lean_object* v_s_1147_){
_start:
{
lean_object* v_toInputContext_1148_; lean_object* v_pos_1149_; uint8_t v___x_1150_; 
v_toInputContext_1148_ = lean_ctor_get(v_c_1146_, 0);
v_pos_1149_ = lean_ctor_get(v_s_1147_, 2);
v___x_1150_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1148_, v_pos_1149_);
if (v___x_1150_ == 0)
{
lean_object* v_inputString_1151_; uint32_t v_curr_1152_; lean_object* v_nextPos_1153_; uint32_t v___x_1154_; uint8_t v___x_1155_; 
v_inputString_1151_ = lean_ctor_get(v_toInputContext_1148_, 0);
v_curr_1152_ = lean_string_utf8_get_fast(v_inputString_1151_, v_pos_1149_);
v_nextPos_1153_ = lean_string_utf8_next_fast(v_inputString_1151_, v_pos_1149_);
v___x_1154_ = 48;
v___x_1155_ = lean_uint32_dec_le(v___x_1154_, v_curr_1152_);
if (v___x_1155_ == 0)
{
lean_object* v___x_1156_; 
v___x_1156_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1145_, v_curr_1152_, v_nextPos_1153_, v_c_1146_, v_s_1147_);
return v___x_1156_;
}
else
{
uint32_t v___x_1157_; uint8_t v___x_1158_; 
v___x_1157_ = 57;
v___x_1158_ = lean_uint32_dec_le(v_curr_1152_, v___x_1157_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; 
v___x_1159_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1145_, v_curr_1152_, v_nextPos_1153_, v_c_1146_, v_s_1147_);
return v___x_1159_;
}
else
{
lean_object* v_s_1160_; lean_object* v_pos_1161_; uint8_t v___x_1162_; 
v_s_1160_ = l_Lean_Parser_ParserState_setPos(v_s_1147_, v_nextPos_1153_);
v_pos_1161_ = lean_ctor_get(v_s_1160_, 2);
lean_inc(v_pos_1161_);
v___x_1162_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1148_, v_pos_1161_);
if (v___x_1162_ == 0)
{
uint32_t v_curr_1163_; lean_object* v_nextPos_1164_; uint32_t v___x_1165_; uint8_t v___x_1166_; 
v_curr_1163_ = lean_string_utf8_get_fast(v_inputString_1151_, v_pos_1161_);
v_nextPos_1164_ = lean_string_utf8_next_fast(v_inputString_1151_, v_pos_1161_);
lean_dec(v_pos_1161_);
v___x_1165_ = 58;
v___x_1166_ = lean_uint32_dec_eq(v_curr_1163_, v___x_1165_);
if (v___x_1166_ == 0)
{
uint8_t v___x_1167_; 
v___x_1167_ = lean_uint32_dec_le(v___x_1154_, v_curr_1163_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; 
v___x_1168_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1145_, v_curr_1163_, v_nextPos_1164_, v_c_1146_, v_s_1160_);
return v___x_1168_;
}
else
{
uint8_t v___x_1169_; 
v___x_1169_ = lean_uint32_dec_le(v_curr_1163_, v___x_1157_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; 
v___x_1170_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1145_, v_curr_1163_, v_nextPos_1164_, v_c_1146_, v_s_1160_);
return v___x_1170_;
}
else
{
lean_object* v_s_1171_; lean_object* v_pos_1172_; uint8_t v___x_1173_; 
v_s_1171_ = l_Lean_Parser_ParserState_setPos(v_s_1160_, v_nextPos_1164_);
v_pos_1172_ = lean_ctor_get(v_s_1171_, 2);
lean_inc(v_pos_1172_);
v___x_1173_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1148_, v_pos_1172_);
if (v___x_1173_ == 0)
{
uint32_t v_curr_1174_; lean_object* v_nextPos_1175_; uint8_t v___x_1176_; 
v_curr_1174_ = lean_string_utf8_get_fast(v_inputString_1151_, v_pos_1172_);
v_nextPos_1175_ = lean_string_utf8_next_fast(v_inputString_1151_, v_pos_1172_);
lean_dec(v_pos_1172_);
v___x_1176_ = lean_uint32_dec_le(v___x_1154_, v_curr_1174_);
if (v___x_1176_ == 0)
{
lean_object* v___x_1177_; 
v___x_1177_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1145_, v_curr_1174_, v_nextPos_1175_, v_c_1146_, v_s_1171_);
return v___x_1177_;
}
else
{
uint8_t v___x_1178_; 
v___x_1178_ = lean_uint32_dec_le(v_curr_1174_, v___x_1157_);
if (v___x_1178_ == 0)
{
lean_object* v___x_1179_; 
v___x_1179_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1145_, v_curr_1174_, v_nextPos_1175_, v_c_1146_, v_s_1171_);
return v___x_1179_;
}
else
{
lean_object* v_s_1180_; uint8_t v___x_1181_; 
v_s_1180_ = l_Lean_Parser_ParserState_setPos(v_s_1171_, v_nextPos_1175_);
v___x_1181_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1148_, v_nextPos_1175_);
if (v___x_1181_ == 0)
{
lean_object* v_pos_1182_; uint32_t v_curr_1183_; lean_object* v_nextPos_1184_; uint32_t v___x_1185_; uint8_t v___x_1186_; 
v_pos_1182_ = lean_ctor_get(v_s_1180_, 2);
lean_inc(v_pos_1182_);
v_curr_1183_ = lean_string_utf8_get_fast(v_inputString_1151_, v_pos_1182_);
v_nextPos_1184_ = lean_string_utf8_next_fast(v_inputString_1151_, v_pos_1182_);
lean_dec(v_pos_1182_);
v___x_1185_ = 45;
v___x_1186_ = lean_uint32_dec_eq(v_curr_1183_, v___x_1185_);
if (v___x_1186_ == 0)
{
uint8_t v___x_1187_; 
v___x_1187_ = lean_uint32_dec_le(v___x_1154_, v_curr_1183_);
if (v___x_1187_ == 0)
{
lean_object* v___x_1188_; 
v___x_1188_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1145_, v_curr_1183_, v_nextPos_1184_, v_c_1146_, v_s_1180_);
return v___x_1188_;
}
else
{
uint8_t v___x_1189_; 
v___x_1189_ = lean_uint32_dec_le(v_curr_1183_, v___x_1157_);
if (v___x_1189_ == 0)
{
lean_object* v___x_1190_; 
v___x_1190_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1145_, v_curr_1183_, v_nextPos_1184_, v_c_1146_, v_s_1180_);
return v___x_1190_;
}
else
{
lean_object* v_s_1191_; lean_object* v___x_1192_; 
v_s_1191_ = l_Lean_Parser_ParserState_setPos(v_s_1180_, v_nextPos_1184_);
v___x_1192_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(v_startPos_1145_, v_c_1146_, v_s_1191_);
return v___x_1192_;
}
}
}
else
{
lean_object* v_s_1193_; lean_object* v_s_1194_; lean_object* v_errorMsg_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v_s_1193_ = l_Lean_Parser_ParserState_setPos(v_s_1180_, v_nextPos_1184_);
v_s_1194_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(v_c_1146_, v_s_1193_);
v_errorMsg_1195_ = lean_ctor_get(v_s_1194_, 4);
lean_inc(v_errorMsg_1195_);
v___x_1196_ = lean_box(0);
v___x_1197_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1195_, v___x_1196_);
lean_dec(v_errorMsg_1195_);
if (v___x_1197_ == 0)
{
lean_dec_ref(v_c_1146_);
lean_dec(v_startPos_1145_);
return v_s_1194_;
}
else
{
if (v___x_1181_ == 0)
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1198_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_1199_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1200_ = l_Lake_Toml_pushLit(v___x_1198_, v_startPos_1145_, v___x_1199_, v_c_1146_, v_s_1194_);
return v___x_1200_;
}
else
{
lean_dec_ref(v_c_1146_);
lean_dec(v_startPos_1145_);
return v_s_1194_;
}
}
}
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; 
v___x_1201_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1202_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1203_ = l_Lake_Toml_pushLit(v___x_1201_, v_startPos_1145_, v___x_1202_, v_c_1146_, v_s_1180_);
return v___x_1203_;
}
}
}
}
else
{
lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
lean_dec(v_pos_1172_);
v___x_1204_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1205_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1206_ = l_Lake_Toml_pushLit(v___x_1204_, v_startPos_1145_, v___x_1205_, v_c_1146_, v_s_1171_);
return v___x_1206_;
}
}
}
}
else
{
lean_object* v_s_1207_; lean_object* v_s_1208_; lean_object* v_errorMsg_1209_; lean_object* v___x_1210_; uint8_t v___x_1211_; 
v_s_1207_ = l_Lean_Parser_ParserState_setPos(v_s_1160_, v_nextPos_1164_);
v_s_1208_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(v___x_1162_, v_c_1146_, v_s_1207_);
v_errorMsg_1209_ = lean_ctor_get(v_s_1208_, 4);
lean_inc(v_errorMsg_1209_);
v___x_1210_ = lean_box(0);
v___x_1211_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1209_, v___x_1210_);
lean_dec(v_errorMsg_1209_);
if (v___x_1211_ == 0)
{
lean_dec_ref(v_c_1146_);
lean_dec(v_startPos_1145_);
return v_s_1208_;
}
else
{
if (v___x_1162_ == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; 
v___x_1212_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_1213_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1214_ = l_Lake_Toml_pushLit(v___x_1212_, v_startPos_1145_, v___x_1213_, v_c_1146_, v_s_1208_);
return v___x_1214_;
}
else
{
lean_dec_ref(v_c_1146_);
lean_dec(v_startPos_1145_);
return v_s_1208_;
}
}
}
}
else
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
lean_dec(v_pos_1161_);
v___x_1215_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1216_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1217_ = l_Lake_Toml_pushLit(v___x_1215_, v_startPos_1145_, v___x_1216_, v_c_1146_, v_s_1160_);
return v___x_1217_;
}
}
}
}
else
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_dec_ref(v_c_1146_);
lean_dec(v_startPos_1145_);
v___x_1218_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__5));
v___x_1219_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1147_, v___x_1218_);
return v___x_1219_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralFn___lam__0(lean_object* v_c_1255_, lean_object* v_s_1256_){
_start:
{
lean_object* v_pos_1257_; lean_object* v___y_1262_; lean_object* v_toInputContext_1269_; lean_object* v_expected_1270_; uint8_t v___x_1271_; 
v_pos_1257_ = lean_ctor_get(v_s_1256_, 2);
v_toInputContext_1269_ = lean_ctor_get(v_c_1255_, 0);
v_expected_1270_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__1));
v___x_1271_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1269_, v_pos_1257_);
if (v___x_1271_ == 0)
{
lean_object* v_inputString_1272_; uint32_t v_curr_1273_; uint32_t v___x_1274_; uint8_t v___x_1275_; 
v_inputString_1272_ = lean_ctor_get(v_toInputContext_1269_, 0);
v_curr_1273_ = lean_string_utf8_get_fast(v_inputString_1272_, v_pos_1257_);
v___x_1274_ = 48;
v___x_1275_ = lean_uint32_dec_eq(v_curr_1273_, v___x_1274_);
if (v___x_1275_ == 0)
{
uint8_t v___x_1276_; uint8_t v___x_1297_; 
v___x_1276_ = 1;
v___x_1297_ = lean_uint32_dec_le(v___x_1274_, v_curr_1273_);
if (v___x_1297_ == 0)
{
goto v___jp_1277_;
}
else
{
uint32_t v___x_1298_; uint8_t v___x_1299_; 
v___x_1298_ = 57;
v___x_1299_ = lean_uint32_dec_le(v_curr_1273_, v___x_1298_);
if (v___x_1299_ == 0)
{
goto v___jp_1277_;
}
else
{
lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_inc(v_pos_1257_);
v___x_1300_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1256_, v_c_1255_, v_pos_1257_);
v___x_1301_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn(v_pos_1257_, v_c_1255_, v___x_1300_);
return v___x_1301_;
}
}
v___jp_1277_:
{
uint32_t v___x_1278_; uint8_t v___x_1279_; 
v___x_1278_ = 43;
v___x_1279_ = lean_uint32_dec_eq(v_curr_1273_, v___x_1278_);
if (v___x_1279_ == 0)
{
uint32_t v___x_1280_; uint8_t v___x_1281_; 
v___x_1280_ = 45;
v___x_1281_ = lean_uint32_dec_eq(v_curr_1273_, v___x_1280_);
if (v___x_1281_ == 0)
{
uint32_t v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = 105;
v___x_1283_ = lean_uint32_dec_eq(v_curr_1273_, v___x_1282_);
if (v___x_1283_ == 0)
{
uint32_t v___x_1284_; uint8_t v___x_1285_; 
v___x_1284_ = 110;
v___x_1285_ = lean_uint32_dec_eq(v_curr_1273_, v___x_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; 
lean_dec_ref(v_c_1255_);
v___x_1286_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__2));
v___x_1287_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_1288_ = lean_string_push(v___x_1287_, v_curr_1273_);
v___x_1289_ = lean_string_append(v___x_1286_, v___x_1288_);
lean_dec_ref(v___x_1288_);
v___x_1290_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1291_ = lean_string_append(v___x_1289_, v___x_1290_);
v___x_1292_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1256_, v___x_1291_, v_expected_1270_, v___x_1276_);
return v___x_1292_;
}
else
{
lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_inc(v_pos_1257_);
v___x_1293_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1256_, v_c_1255_, v_pos_1257_);
v___x_1294_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(v_pos_1257_, v_c_1255_, v___x_1293_);
return v___x_1294_;
}
}
else
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
lean_inc(v_pos_1257_);
v___x_1295_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1256_, v_c_1255_, v_pos_1257_);
v___x_1296_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(v_pos_1257_, v_c_1255_, v___x_1295_);
return v___x_1296_;
}
}
else
{
lean_inc(v_pos_1257_);
goto v___jp_1258_;
}
}
else
{
lean_inc(v_pos_1257_);
goto v___jp_1258_;
}
}
}
else
{
lean_object* v_s_1302_; lean_object* v_pos_1303_; uint8_t v___x_1304_; 
lean_inc(v_pos_1257_);
v_s_1302_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1256_, v_c_1255_, v_pos_1257_);
v_pos_1303_ = lean_ctor_get(v_s_1302_, 2);
lean_inc(v_pos_1303_);
v___x_1304_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1269_, v_pos_1303_);
if (v___x_1304_ == 0)
{
uint32_t v_curr_1305_; uint32_t v___x_1309_; uint8_t v___x_1310_; 
v_curr_1305_ = lean_string_utf8_get_fast(v_inputString_1272_, v_pos_1303_);
v___x_1309_ = 98;
v___x_1310_ = lean_uint32_dec_eq(v_curr_1305_, v___x_1309_);
if (v___x_1310_ == 0)
{
uint32_t v___x_1311_; uint8_t v___x_1312_; 
v___x_1311_ = 111;
v___x_1312_ = lean_uint32_dec_eq(v_curr_1305_, v___x_1311_);
if (v___x_1312_ == 0)
{
uint32_t v___x_1313_; uint8_t v___x_1314_; 
v___x_1313_ = 120;
v___x_1314_ = lean_uint32_dec_eq(v_curr_1305_, v___x_1313_);
if (v___x_1314_ == 0)
{
uint8_t v___x_1315_; 
v___x_1315_ = lean_uint32_dec_le(v___x_1274_, v_curr_1305_);
if (v___x_1315_ == 0)
{
goto v___jp_1306_;
}
else
{
uint32_t v___x_1316_; uint8_t v___x_1317_; 
v___x_1316_ = 57;
v___x_1317_ = lean_uint32_dec_le(v_curr_1305_, v___x_1316_);
if (v___x_1317_ == 0)
{
goto v___jp_1306_;
}
else
{
lean_object* v_s_1318_; uint32_t v___x_1319_; lean_object* v___x_1320_; lean_object* v_s_1321_; lean_object* v_errorMsg_1322_; lean_object* v___x_1323_; uint8_t v___x_1324_; 
v_s_1318_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1302_, v_c_1255_, v_pos_1303_);
lean_dec(v_pos_1303_);
v___x_1319_ = 58;
v___x_1320_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7, &l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7);
v_s_1321_ = l_Lake_Toml_chFn(v___x_1319_, v___x_1320_, v_c_1255_, v_s_1318_);
v_errorMsg_1322_ = lean_ctor_get(v_s_1321_, 4);
lean_inc(v_errorMsg_1322_);
v___x_1323_ = lean_box(0);
v___x_1324_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1322_, v___x_1323_);
lean_dec(v_errorMsg_1322_);
if (v___x_1324_ == 0)
{
v___y_1262_ = v_s_1321_;
goto v___jp_1261_;
}
else
{
lean_object* v___x_1325_; 
v___x_1325_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(v___x_1314_, v_c_1255_, v_s_1321_);
v___y_1262_ = v___x_1325_;
goto v___jp_1261_;
}
}
}
}
else
{
lean_object* v_s_1326_; lean_object* v___x_1327_; uint32_t v___x_1328_; lean_object* v___x_1329_; lean_object* v_s_1330_; lean_object* v_errorMsg_1331_; lean_object* v___x_1332_; uint8_t v___x_1333_; 
v_s_1326_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1302_, v_c_1255_, v_pos_1303_);
lean_dec(v_pos_1303_);
v___x_1327_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__3));
v___x_1328_ = 95;
v___x_1329_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__5));
v_s_1330_ = l_Lake_Toml_sepByChar1Fn(v___x_1327_, v___x_1328_, v___x_1329_, v_c_1255_, v_s_1326_);
v_errorMsg_1331_ = lean_ctor_get(v_s_1330_, 4);
lean_inc(v_errorMsg_1331_);
v___x_1332_ = lean_box(0);
v___x_1333_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1331_, v___x_1332_);
lean_dec(v_errorMsg_1331_);
if (v___x_1333_ == 0)
{
lean_dec(v_pos_1257_);
lean_dec_ref(v_c_1255_);
return v_s_1330_;
}
else
{
lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; 
v___x_1334_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__7));
v___x_1335_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1336_ = l_Lake_Toml_pushLit(v___x_1334_, v_pos_1257_, v___x_1335_, v_c_1255_, v_s_1330_);
return v___x_1336_;
}
}
}
else
{
lean_object* v_s_1337_; lean_object* v___x_1338_; uint32_t v___x_1339_; lean_object* v___x_1340_; lean_object* v_s_1341_; lean_object* v_errorMsg_1342_; lean_object* v___x_1343_; uint8_t v___x_1344_; 
v_s_1337_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1302_, v_c_1255_, v_pos_1303_);
lean_dec(v_pos_1303_);
v___x_1338_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__8));
v___x_1339_ = 95;
v___x_1340_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__10));
v_s_1341_ = l_Lake_Toml_sepByChar1Fn(v___x_1338_, v___x_1339_, v___x_1340_, v_c_1255_, v_s_1337_);
v_errorMsg_1342_ = lean_ctor_get(v_s_1341_, 4);
lean_inc(v_errorMsg_1342_);
v___x_1343_ = lean_box(0);
v___x_1344_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1342_, v___x_1343_);
lean_dec(v_errorMsg_1342_);
if (v___x_1344_ == 0)
{
lean_dec(v_pos_1257_);
lean_dec_ref(v_c_1255_);
return v_s_1341_;
}
else
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1345_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__12));
v___x_1346_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1347_ = l_Lake_Toml_pushLit(v___x_1345_, v_pos_1257_, v___x_1346_, v_c_1255_, v_s_1341_);
return v___x_1347_;
}
}
}
else
{
lean_object* v_s_1348_; lean_object* v___x_1349_; uint32_t v___x_1350_; lean_object* v___x_1351_; lean_object* v_s_1352_; lean_object* v_errorMsg_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v_s_1348_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1302_, v_c_1255_, v_pos_1303_);
lean_dec(v_pos_1303_);
v___x_1349_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__13));
v___x_1350_ = 95;
v___x_1351_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__15));
v_s_1352_ = l_Lake_Toml_sepByChar1Fn(v___x_1349_, v___x_1350_, v___x_1351_, v_c_1255_, v_s_1348_);
v_errorMsg_1353_ = lean_ctor_get(v_s_1352_, 4);
lean_inc(v_errorMsg_1353_);
v___x_1354_ = lean_box(0);
v___x_1355_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1353_, v___x_1354_);
lean_dec(v_errorMsg_1353_);
if (v___x_1355_ == 0)
{
lean_dec(v_pos_1257_);
lean_dec_ref(v_c_1255_);
return v_s_1352_;
}
else
{
if (v___x_1304_ == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1356_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__17));
v___x_1357_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1358_ = l_Lake_Toml_pushLit(v___x_1356_, v_pos_1257_, v___x_1357_, v_c_1255_, v_s_1352_);
return v___x_1358_;
}
else
{
lean_dec(v_pos_1257_);
lean_dec_ref(v_c_1255_);
return v_s_1352_;
}
}
}
v___jp_1306_:
{
lean_object* v___x_1307_; lean_object* v___x_1308_; 
v___x_1307_ = lean_string_utf8_next_fast(v_inputString_1272_, v_pos_1303_);
lean_dec(v_pos_1303_);
v___x_1308_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(v_pos_1257_, v_curr_1305_, v___x_1307_, v_c_1255_, v_s_1302_);
return v___x_1308_;
}
}
else
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; 
lean_dec(v_pos_1303_);
v___x_1359_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1360_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1361_ = l_Lake_Toml_pushLit(v___x_1359_, v_pos_1257_, v___x_1360_, v_c_1255_, v_s_1302_);
return v___x_1361_;
}
}
}
else
{
lean_object* v___x_1362_; 
lean_dec_ref(v_c_1255_);
v___x_1362_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1256_, v_expected_1270_);
return v___x_1362_;
}
v___jp_1258_:
{
lean_object* v___x_1259_; lean_object* v___x_1260_; 
v___x_1259_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1256_, v_c_1255_, v_pos_1257_);
v___x_1260_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decimalFn(v_pos_1257_, v_c_1255_, v___x_1259_);
return v___x_1260_;
}
v___jp_1261_:
{
lean_object* v_errorMsg_1263_; lean_object* v___x_1264_; uint8_t v___x_1265_; 
v_errorMsg_1263_ = lean_ctor_get(v___y_1262_, 4);
v___x_1264_ = lean_box(0);
v___x_1265_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1263_, v___x_1264_);
if (v___x_1265_ == 0)
{
lean_dec(v_pos_1257_);
lean_dec_ref(v_c_1255_);
return v___y_1262_;
}
else
{
lean_object* v___x_1266_; lean_object* v___x_1267_; lean_object* v___x_1268_; 
v___x_1266_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_1267_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1268_ = l_Lake_Toml_pushLit(v___x_1266_, v_pos_1257_, v___x_1267_, v_c_1255_, v___y_1262_);
return v___x_1268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralFn(lean_object* v_a_1364_, lean_object* v_a_1365_){
_start:
{
lean_object* v___f_1366_; lean_object* v___x_1367_; 
v___f_1366_ = ((lean_object*)(l_Lake_Toml_numeralFn___closed__0));
v___x_1367_ = l_Lean_Parser_atomicFn(v___f_1366_, v_a_1364_, v_a_1365_);
return v___x_1367_;
}
}
static lean_object* _init_l_Lake_Toml_trailingWs___closed__0(void){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_alloc_closure((void*)(l_Lake_Toml_wsFn___boxed), 2, 0);
v___x_1369_ = l_Lake_Toml_trailing(v___x_1368_);
return v___x_1369_;
}
}
static lean_object* _init_l_Lake_Toml_trailingWs(void){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_obj_once(&l_Lake_Toml_trailingWs___closed__0, &l_Lake_Toml_trailingWs___closed__0_once, _init_l_Lake_Toml_trailingWs___closed__0);
return v___x_1370_;
}
}
static lean_object* _init_l_Lake_Toml_trailingSep___closed__1(void){
_start:
{
lean_object* v___x_1372_; lean_object* v___x_1373_; 
v___x_1372_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1373_ = l_Lake_Toml_trailing(v___x_1372_);
return v___x_1373_;
}
}
static lean_object* _init_l_Lake_Toml_trailingSep(void){
_start:
{
lean_object* v___x_1374_; 
v___x_1374_ = lean_obj_once(&l_Lake_Toml_trailingSep___closed__1, &l_Lake_Toml_trailingSep___closed__1_once, _init_l_Lake_Toml_trailingSep___closed__1);
return v___x_1374_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_unquotedKeyFn___lam__0(uint32_t v_c_1375_){
_start:
{
uint8_t v___y_1387_; uint32_t v___x_1392_; uint8_t v___x_1393_; 
v___x_1392_ = 65;
v___x_1393_ = lean_uint32_dec_le(v___x_1392_, v_c_1375_);
if (v___x_1393_ == 0)
{
v___y_1387_ = v___x_1393_;
goto v___jp_1386_;
}
else
{
uint32_t v___x_1394_; uint8_t v___x_1395_; 
v___x_1394_ = 90;
v___x_1395_ = lean_uint32_dec_le(v_c_1375_, v___x_1394_);
v___y_1387_ = v___x_1395_;
goto v___jp_1386_;
}
v___jp_1376_:
{
uint32_t v___x_1377_; uint8_t v___x_1378_; 
v___x_1377_ = 95;
v___x_1378_ = lean_uint32_dec_eq(v_c_1375_, v___x_1377_);
if (v___x_1378_ == 0)
{
uint32_t v___x_1379_; uint8_t v___x_1380_; 
v___x_1379_ = 45;
v___x_1380_ = lean_uint32_dec_eq(v_c_1375_, v___x_1379_);
return v___x_1380_;
}
else
{
return v___x_1378_;
}
}
v___jp_1381_:
{
uint32_t v___x_1382_; uint8_t v___x_1383_; 
v___x_1382_ = 48;
v___x_1383_ = lean_uint32_dec_le(v___x_1382_, v_c_1375_);
if (v___x_1383_ == 0)
{
goto v___jp_1376_;
}
else
{
uint32_t v___x_1384_; uint8_t v___x_1385_; 
v___x_1384_ = 57;
v___x_1385_ = lean_uint32_dec_le(v_c_1375_, v___x_1384_);
if (v___x_1385_ == 0)
{
goto v___jp_1376_;
}
else
{
return v___x_1385_;
}
}
}
v___jp_1386_:
{
if (v___y_1387_ == 0)
{
uint32_t v___x_1388_; uint8_t v___x_1389_; 
v___x_1388_ = 97;
v___x_1389_ = lean_uint32_dec_le(v___x_1388_, v_c_1375_);
if (v___x_1389_ == 0)
{
goto v___jp_1381_;
}
else
{
uint32_t v___x_1390_; uint8_t v___x_1391_; 
v___x_1390_ = 122;
v___x_1391_ = lean_uint32_dec_le(v_c_1375_, v___x_1390_);
if (v___x_1391_ == 0)
{
goto v___jp_1381_;
}
else
{
return v___x_1391_;
}
}
}
else
{
return v___y_1387_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn___lam__0___boxed(lean_object* v_c_1396_){
_start:
{
uint32_t v_c_boxed_1397_; uint8_t v_res_1398_; lean_object* v_r_1399_; 
v_c_boxed_1397_ = lean_unbox_uint32(v_c_1396_);
lean_dec(v_c_1396_);
v_res_1398_ = l_Lake_Toml_unquotedKeyFn___lam__0(v_c_boxed_1397_);
v_r_1399_ = lean_box(v_res_1398_);
return v_r_1399_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn(lean_object* v_a_1405_, lean_object* v_a_1406_){
_start:
{
lean_object* v___f_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___f_1407_ = ((lean_object*)(l_Lake_Toml_unquotedKeyFn___closed__0));
v___x_1408_ = ((lean_object*)(l_Lake_Toml_unquotedKeyFn___closed__2));
v___x_1409_ = l_Lake_Toml_takeWhile1Fn(v___f_1407_, v___x_1408_, v_a_1405_, v_a_1406_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn___boxed(lean_object* v_a_1410_, lean_object* v_a_1411_){
_start:
{
lean_object* v_res_1412_; 
v_res_1412_ = l_Lake_Toml_unquotedKeyFn(v_a_1410_, v_a_1411_);
lean_dec_ref(v_a_1410_);
return v_res_1412_;
}
}
static lean_object* _init_l_Lake_Toml_unquotedKey___closed__2(void){
_start:
{
uint8_t v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1418_ = 0;
v___x_1419_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1420_ = lean_alloc_closure((void*)(l_Lake_Toml_unquotedKeyFn___boxed), 2, 0);
v___x_1421_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__1));
v___x_1422_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__0));
v___x_1423_ = l_Lake_Toml_litWithAntiquot(v___x_1422_, v___x_1421_, v___x_1420_, v___x_1419_, v___x_1418_);
return v___x_1423_;
}
}
static lean_object* _init_l_Lake_Toml_unquotedKey(void){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_obj_once(&l_Lake_Toml_unquotedKey___closed__2, &l_Lake_Toml_unquotedKey___closed__2_once, _init_l_Lake_Toml_unquotedKey___closed__2);
return v___x_1424_;
}
}
static lean_object* _init_l_Lake_Toml_basicString___closed__2(void){
_start:
{
uint8_t v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___x_1430_ = 0;
v___x_1431_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1432_ = lean_alloc_closure((void*)(l_Lake_Toml_basicStringFn), 2, 0);
v___x_1433_ = ((lean_object*)(l_Lake_Toml_basicString___closed__1));
v___x_1434_ = ((lean_object*)(l_Lake_Toml_basicString___closed__0));
v___x_1435_ = l_Lake_Toml_litWithAntiquot(v___x_1434_, v___x_1433_, v___x_1432_, v___x_1431_, v___x_1430_);
return v___x_1435_;
}
}
static lean_object* _init_l_Lake_Toml_basicString(void){
_start:
{
lean_object* v___x_1436_; 
v___x_1436_ = lean_obj_once(&l_Lake_Toml_basicString___closed__2, &l_Lake_Toml_basicString___closed__2_once, _init_l_Lake_Toml_basicString___closed__2);
return v___x_1436_;
}
}
static lean_object* _init_l_Lake_Toml_literalString___closed__2(void){
_start:
{
uint8_t v___x_1442_; lean_object* v___x_1443_; lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; lean_object* v___x_1447_; 
v___x_1442_ = 0;
v___x_1443_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1444_ = lean_alloc_closure((void*)(l_Lake_Toml_literalStringFn___boxed), 2, 0);
v___x_1445_ = ((lean_object*)(l_Lake_Toml_literalString___closed__1));
v___x_1446_ = ((lean_object*)(l_Lake_Toml_literalString___closed__0));
v___x_1447_ = l_Lake_Toml_litWithAntiquot(v___x_1446_, v___x_1445_, v___x_1444_, v___x_1443_, v___x_1442_);
return v___x_1447_;
}
}
static lean_object* _init_l_Lake_Toml_literalString(void){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = lean_obj_once(&l_Lake_Toml_literalString___closed__2, &l_Lake_Toml_literalString___closed__2_once, _init_l_Lake_Toml_literalString___closed__2);
return v___x_1448_;
}
}
static lean_object* _init_l_Lake_Toml_mlBasicString___closed__2(void){
_start:
{
uint8_t v___x_1454_; lean_object* v___x_1455_; lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1454_ = 0;
v___x_1455_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1456_ = lean_alloc_closure((void*)(l_Lake_Toml_mlBasicStringFn), 2, 0);
v___x_1457_ = ((lean_object*)(l_Lake_Toml_mlBasicString___closed__1));
v___x_1458_ = ((lean_object*)(l_Lake_Toml_mlBasicString___closed__0));
v___x_1459_ = l_Lake_Toml_litWithAntiquot(v___x_1458_, v___x_1457_, v___x_1456_, v___x_1455_, v___x_1454_);
return v___x_1459_;
}
}
static lean_object* _init_l_Lake_Toml_mlBasicString(void){
_start:
{
lean_object* v___x_1460_; 
v___x_1460_ = lean_obj_once(&l_Lake_Toml_mlBasicString___closed__2, &l_Lake_Toml_mlBasicString___closed__2_once, _init_l_Lake_Toml_mlBasicString___closed__2);
return v___x_1460_;
}
}
static lean_object* _init_l_Lake_Toml_mlLiteralString___closed__2(void){
_start:
{
uint8_t v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1466_ = 0;
v___x_1467_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1468_ = lean_alloc_closure((void*)(l_Lake_Toml_mlLiteralStringFn), 2, 0);
v___x_1469_ = ((lean_object*)(l_Lake_Toml_mlLiteralString___closed__1));
v___x_1470_ = ((lean_object*)(l_Lake_Toml_mlLiteralString___closed__0));
v___x_1471_ = l_Lake_Toml_litWithAntiquot(v___x_1470_, v___x_1469_, v___x_1468_, v___x_1467_, v___x_1466_);
return v___x_1471_;
}
}
static lean_object* _init_l_Lake_Toml_mlLiteralString(void){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_obj_once(&l_Lake_Toml_mlLiteralString___closed__2, &l_Lake_Toml_mlLiteralString___closed__2_once, _init_l_Lake_Toml_mlLiteralString___closed__2);
return v___x_1472_;
}
}
static lean_object* _init_l_Lake_Toml_quotedKey___closed__0(void){
_start:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; 
v___x_1473_ = l_Lake_Toml_literalString;
v___x_1474_ = l_Lake_Toml_basicString;
v___x_1475_ = l_Lean_Parser_orelse(v___x_1474_, v___x_1473_);
return v___x_1475_;
}
}
static lean_object* _init_l_Lake_Toml_quotedKey(void){
_start:
{
lean_object* v___x_1476_; 
v___x_1476_ = lean_obj_once(&l_Lake_Toml_quotedKey___closed__0, &l_Lake_Toml_quotedKey___closed__0_once, _init_l_Lake_Toml_quotedKey___closed__0);
return v___x_1476_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey___closed__2(void){
_start:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; 
v___x_1482_ = l_Lake_Toml_quotedKey;
v___x_1483_ = l_Lake_Toml_unquotedKey;
v___x_1484_ = l_Lean_Parser_orelse(v___x_1483_, v___x_1482_);
return v___x_1484_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey___closed__3(void){
_start:
{
uint8_t v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; 
v___x_1485_ = 1;
v___x_1486_ = lean_obj_once(&l_Lake_Toml_simpleKey___closed__2, &l_Lake_Toml_simpleKey___closed__2_once, _init_l_Lake_Toml_simpleKey___closed__2);
v___x_1487_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__1));
v___x_1488_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__0));
v___x_1489_ = l_Lean_Parser_nodeWithAntiquot(v___x_1488_, v___x_1487_, v___x_1486_, v___x_1485_);
return v___x_1489_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey(void){
_start:
{
lean_object* v___x_1490_; 
v___x_1490_ = lean_obj_once(&l_Lake_Toml_simpleKey___closed__3, &l_Lake_Toml_simpleKey___closed__3_once, _init_l_Lake_Toml_simpleKey___closed__3);
return v___x_1490_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__4(void){
_start:
{
uint32_t v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1500_ = 46;
v___x_1501_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_1502_ = lean_string_push(v___x_1501_, v___x_1500_);
return v___x_1502_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__5(void){
_start:
{
lean_object* v___x_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; 
v___x_1503_ = lean_obj_once(&l_Lake_Toml_key___closed__4, &l_Lake_Toml_key___closed__4_once, _init_l_Lake_Toml_key___closed__4);
v___x_1504_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1505_ = lean_string_append(v___x_1504_, v___x_1503_);
return v___x_1505_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__6(void){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; 
v___x_1506_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1507_ = lean_obj_once(&l_Lake_Toml_key___closed__5, &l_Lake_Toml_key___closed__5_once, _init_l_Lake_Toml_key___closed__5);
v___x_1508_ = lean_string_append(v___x_1507_, v___x_1506_);
return v___x_1508_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__7(void){
_start:
{
lean_object* v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; 
v___x_1509_ = lean_box(0);
v___x_1510_ = lean_obj_once(&l_Lake_Toml_key___closed__6, &l_Lake_Toml_key___closed__6_once, _init_l_Lake_Toml_key___closed__6);
v___x_1511_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1511_, 0, v___x_1510_);
lean_ctor_set(v___x_1511_, 1, v___x_1509_);
return v___x_1511_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__8(void){
_start:
{
lean_object* v___x_1512_; lean_object* v___x_1513_; uint32_t v___x_1514_; lean_object* v___x_1515_; 
v___x_1512_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1513_ = lean_obj_once(&l_Lake_Toml_key___closed__7, &l_Lake_Toml_key___closed__7_once, _init_l_Lake_Toml_key___closed__7);
v___x_1514_ = 46;
v___x_1515_ = l_Lake_Toml_chAtom(v___x_1514_, v___x_1513_, v___x_1512_);
return v___x_1515_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__9(void){
_start:
{
lean_object* v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; 
v___x_1516_ = l_Lake_Toml_trailingWs;
v___x_1517_ = lean_obj_once(&l_Lake_Toml_key___closed__8, &l_Lake_Toml_key___closed__8_once, _init_l_Lake_Toml_key___closed__8);
v___x_1518_ = l_Lean_Parser_andthen(v___x_1517_, v___x_1516_);
return v___x_1518_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__10(void){
_start:
{
lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1519_ = lean_obj_once(&l_Lake_Toml_key___closed__9, &l_Lake_Toml_key___closed__9_once, _init_l_Lake_Toml_key___closed__9);
v___x_1520_ = l_Lake_Toml_trailingWs;
v___x_1521_ = l_Lean_Parser_andthen(v___x_1520_, v___x_1519_);
return v___x_1521_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__11(void){
_start:
{
uint8_t v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1522_ = 0;
v___x_1523_ = lean_obj_once(&l_Lake_Toml_key___closed__10, &l_Lake_Toml_key___closed__10_once, _init_l_Lake_Toml_key___closed__10);
v___x_1524_ = ((lean_object*)(l_Lake_Toml_key___closed__3));
v___x_1525_ = l_Lake_Toml_simpleKey;
v___x_1526_ = l_Lean_Parser_sepBy1(v___x_1525_, v___x_1524_, v___x_1523_, v___x_1522_);
return v___x_1526_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__12(void){
_start:
{
lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1529_; 
v___x_1527_ = lean_obj_once(&l_Lake_Toml_key___closed__11, &l_Lake_Toml_key___closed__11_once, _init_l_Lake_Toml_key___closed__11);
v___x_1528_ = ((lean_object*)(l_Lake_Toml_key___closed__2));
v___x_1529_ = l_Lean_Parser_setExpected(v___x_1528_, v___x_1527_);
return v___x_1529_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__13(void){
_start:
{
uint8_t v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1530_ = 1;
v___x_1531_ = lean_obj_once(&l_Lake_Toml_key___closed__12, &l_Lake_Toml_key___closed__12_once, _init_l_Lake_Toml_key___closed__12);
v___x_1532_ = ((lean_object*)(l_Lake_Toml_key___closed__1));
v___x_1533_ = ((lean_object*)(l_Lake_Toml_key___closed__0));
v___x_1534_ = l_Lean_Parser_nodeWithAntiquot(v___x_1533_, v___x_1532_, v___x_1531_, v___x_1530_);
return v___x_1534_;
}
}
static lean_object* _init_l_Lake_Toml_key(void){
_start:
{
lean_object* v___x_1535_; 
v___x_1535_ = lean_obj_once(&l_Lake_Toml_key___closed__13, &l_Lake_Toml_key___closed__13_once, _init_l_Lake_Toml_key___closed__13);
return v___x_1535_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__4(void){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; uint32_t v___x_1547_; lean_object* v___x_1548_; 
v___x_1545_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1546_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__3));
v___x_1547_ = 91;
v___x_1548_ = l_Lake_Toml_chAtom(v___x_1547_, v___x_1546_, v___x_1545_);
return v___x_1548_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__5(void){
_start:
{
uint32_t v___x_1549_; lean_object* v___x_1550_; lean_object* v___x_1551_; 
v___x_1549_ = 91;
v___x_1550_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_1551_ = lean_string_push(v___x_1550_, v___x_1549_);
return v___x_1551_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__6(void){
_start:
{
lean_object* v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1552_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__5, &l_Lake_Toml_stdTable___closed__5_once, _init_l_Lake_Toml_stdTable___closed__5);
v___x_1553_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1554_ = lean_string_append(v___x_1553_, v___x_1552_);
return v___x_1554_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__7(void){
_start:
{
lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1556_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__6, &l_Lake_Toml_stdTable___closed__6_once, _init_l_Lake_Toml_stdTable___closed__6);
v___x_1557_ = lean_string_append(v___x_1556_, v___x_1555_);
return v___x_1557_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__8(void){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1558_ = lean_box(0);
v___x_1559_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__7, &l_Lake_Toml_stdTable___closed__7_once, _init_l_Lake_Toml_stdTable___closed__7);
v___x_1560_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1560_, 0, v___x_1559_);
lean_ctor_set(v___x_1560_, 1, v___x_1558_);
return v___x_1560_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__9(void){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; uint32_t v___x_1563_; lean_object* v___x_1564_; 
v___x_1561_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1562_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__8, &l_Lake_Toml_stdTable___closed__8_once, _init_l_Lake_Toml_stdTable___closed__8);
v___x_1563_ = 91;
v___x_1564_ = l_Lake_Toml_chAtom(v___x_1563_, v___x_1562_, v___x_1561_);
return v___x_1564_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__11(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1568_; 
v___x_1566_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__10));
v___x_1567_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__9, &l_Lake_Toml_stdTable___closed__9_once, _init_l_Lake_Toml_stdTable___closed__9);
v___x_1568_ = l_Lean_Parser_notFollowedBy(v___x_1567_, v___x_1566_);
return v___x_1568_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__12(void){
_start:
{
lean_object* v___x_1569_; lean_object* v___x_1570_; lean_object* v___x_1571_; 
v___x_1569_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__11, &l_Lake_Toml_stdTable___closed__11_once, _init_l_Lake_Toml_stdTable___closed__11);
v___x_1570_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__4, &l_Lake_Toml_stdTable___closed__4_once, _init_l_Lake_Toml_stdTable___closed__4);
v___x_1571_ = l_Lean_Parser_andthen(v___x_1570_, v___x_1569_);
return v___x_1571_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__13(void){
_start:
{
lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1572_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__12, &l_Lake_Toml_stdTable___closed__12_once, _init_l_Lake_Toml_stdTable___closed__12);
v___x_1573_ = l_Lean_Parser_atomic(v___x_1572_);
return v___x_1573_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__14(void){
_start:
{
uint32_t v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1574_ = 93;
v___x_1575_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_1576_ = lean_string_push(v___x_1575_, v___x_1574_);
return v___x_1576_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__15(void){
_start:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; 
v___x_1577_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__14, &l_Lake_Toml_stdTable___closed__14_once, _init_l_Lake_Toml_stdTable___closed__14);
v___x_1578_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1579_ = lean_string_append(v___x_1578_, v___x_1577_);
return v___x_1579_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__16(void){
_start:
{
lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1580_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1581_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__15, &l_Lake_Toml_stdTable___closed__15_once, _init_l_Lake_Toml_stdTable___closed__15);
v___x_1582_ = lean_string_append(v___x_1581_, v___x_1580_);
return v___x_1582_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__17(void){
_start:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; lean_object* v___x_1585_; 
v___x_1583_ = lean_box(0);
v___x_1584_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__16, &l_Lake_Toml_stdTable___closed__16_once, _init_l_Lake_Toml_stdTable___closed__16);
v___x_1585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1585_, 0, v___x_1584_);
lean_ctor_set(v___x_1585_, 1, v___x_1583_);
return v___x_1585_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__18(void){
_start:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; uint32_t v___x_1588_; lean_object* v___x_1589_; 
v___x_1586_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1587_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__17, &l_Lake_Toml_stdTable___closed__17_once, _init_l_Lake_Toml_stdTable___closed__17);
v___x_1588_ = 93;
v___x_1589_ = l_Lake_Toml_chAtom(v___x_1588_, v___x_1587_, v___x_1586_);
return v___x_1589_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__19(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; 
v___x_1590_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__18, &l_Lake_Toml_stdTable___closed__18_once, _init_l_Lake_Toml_stdTable___closed__18);
v___x_1591_ = l_Lake_Toml_trailingWs;
v___x_1592_ = l_Lean_Parser_andthen(v___x_1591_, v___x_1590_);
return v___x_1592_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__20(void){
_start:
{
lean_object* v___x_1593_; lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1593_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__19, &l_Lake_Toml_stdTable___closed__19_once, _init_l_Lake_Toml_stdTable___closed__19);
v___x_1594_ = l_Lake_Toml_key;
v___x_1595_ = l_Lean_Parser_andthen(v___x_1594_, v___x_1593_);
return v___x_1595_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__21(void){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1596_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__20, &l_Lake_Toml_stdTable___closed__20_once, _init_l_Lake_Toml_stdTable___closed__20);
v___x_1597_ = l_Lake_Toml_trailingWs;
v___x_1598_ = l_Lean_Parser_andthen(v___x_1597_, v___x_1596_);
return v___x_1598_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__22(void){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; 
v___x_1599_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__21, &l_Lake_Toml_stdTable___closed__21_once, _init_l_Lake_Toml_stdTable___closed__21);
v___x_1600_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__13, &l_Lake_Toml_stdTable___closed__13_once, _init_l_Lake_Toml_stdTable___closed__13);
v___x_1601_ = l_Lean_Parser_andthen(v___x_1600_, v___x_1599_);
return v___x_1601_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__23(void){
_start:
{
uint8_t v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1602_ = 0;
v___x_1603_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__22, &l_Lake_Toml_stdTable___closed__22_once, _init_l_Lake_Toml_stdTable___closed__22);
v___x_1604_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__1));
v___x_1605_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__0));
v___x_1606_ = l_Lean_Parser_nodeWithAntiquot(v___x_1605_, v___x_1604_, v___x_1603_, v___x_1602_);
return v___x_1606_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable(void){
_start:
{
lean_object* v___x_1607_; 
v___x_1607_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__23, &l_Lake_Toml_stdTable___closed__23_once, _init_l_Lake_Toml_stdTable___closed__23);
return v___x_1607_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__2(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1613_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__9, &l_Lake_Toml_stdTable___closed__9_once, _init_l_Lake_Toml_stdTable___closed__9);
v___x_1614_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__4, &l_Lake_Toml_stdTable___closed__4_once, _init_l_Lake_Toml_stdTable___closed__4);
v___x_1615_ = l_Lean_Parser_andthen(v___x_1614_, v___x_1613_);
return v___x_1615_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__3(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__2, &l_Lake_Toml_arrayTable___closed__2_once, _init_l_Lake_Toml_arrayTable___closed__2);
v___x_1617_ = l_Lean_Parser_atomic(v___x_1616_);
return v___x_1617_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__4(void){
_start:
{
lean_object* v___x_1618_; lean_object* v___x_1619_; 
v___x_1618_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__18, &l_Lake_Toml_stdTable___closed__18_once, _init_l_Lake_Toml_stdTable___closed__18);
v___x_1619_ = l_Lean_Parser_andthen(v___x_1618_, v___x_1618_);
return v___x_1619_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__5(void){
_start:
{
lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; 
v___x_1620_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__4, &l_Lake_Toml_arrayTable___closed__4_once, _init_l_Lake_Toml_arrayTable___closed__4);
v___x_1621_ = l_Lake_Toml_trailingWs;
v___x_1622_ = l_Lean_Parser_andthen(v___x_1621_, v___x_1620_);
return v___x_1622_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__6(void){
_start:
{
lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1625_; 
v___x_1623_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__5, &l_Lake_Toml_arrayTable___closed__5_once, _init_l_Lake_Toml_arrayTable___closed__5);
v___x_1624_ = l_Lake_Toml_key;
v___x_1625_ = l_Lean_Parser_andthen(v___x_1624_, v___x_1623_);
return v___x_1625_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__7(void){
_start:
{
lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1626_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__6, &l_Lake_Toml_arrayTable___closed__6_once, _init_l_Lake_Toml_arrayTable___closed__6);
v___x_1627_ = l_Lake_Toml_trailingWs;
v___x_1628_ = l_Lean_Parser_andthen(v___x_1627_, v___x_1626_);
return v___x_1628_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__8(void){
_start:
{
lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1629_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__7, &l_Lake_Toml_arrayTable___closed__7_once, _init_l_Lake_Toml_arrayTable___closed__7);
v___x_1630_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__3, &l_Lake_Toml_arrayTable___closed__3_once, _init_l_Lake_Toml_arrayTable___closed__3);
v___x_1631_ = l_Lean_Parser_andthen(v___x_1630_, v___x_1629_);
return v___x_1631_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__9(void){
_start:
{
uint8_t v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1636_; 
v___x_1632_ = 0;
v___x_1633_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__8, &l_Lake_Toml_arrayTable___closed__8_once, _init_l_Lake_Toml_arrayTable___closed__8);
v___x_1634_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__1));
v___x_1635_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__0));
v___x_1636_ = l_Lean_Parser_nodeWithAntiquot(v___x_1635_, v___x_1634_, v___x_1633_, v___x_1632_);
return v___x_1636_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable(void){
_start:
{
lean_object* v___x_1637_; 
v___x_1637_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__9, &l_Lake_Toml_arrayTable___closed__9_once, _init_l_Lake_Toml_arrayTable___closed__9);
return v___x_1637_;
}
}
static lean_object* _init_l_Lake_Toml_table___closed__0(void){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1638_ = l_Lake_Toml_arrayTable;
v___x_1639_ = l_Lake_Toml_stdTable;
v___x_1640_ = l_Lean_Parser_orelse(v___x_1639_, v___x_1638_);
return v___x_1640_;
}
}
static lean_object* _init_l_Lake_Toml_table(void){
_start:
{
lean_object* v___x_1641_; 
v___x_1641_ = lean_obj_once(&l_Lake_Toml_table___closed__0, &l_Lake_Toml_table___closed__0_once, _init_l_Lake_Toml_table___closed__0);
return v___x_1641_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2(void){
_start:
{
uint32_t v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; 
v___x_1647_ = 61;
v___x_1648_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_1649_ = lean_string_push(v___x_1648_, v___x_1647_);
return v___x_1649_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3(void){
_start:
{
lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1650_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2);
v___x_1651_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1652_ = lean_string_append(v___x_1651_, v___x_1650_);
return v___x_1652_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4(void){
_start:
{
lean_object* v___x_1653_; lean_object* v___x_1654_; lean_object* v___x_1655_; 
v___x_1653_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1654_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3);
v___x_1655_ = lean_string_append(v___x_1654_, v___x_1653_);
return v___x_1655_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5(void){
_start:
{
lean_object* v___x_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; 
v___x_1656_ = lean_box(0);
v___x_1657_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4);
v___x_1658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1658_, 0, v___x_1657_);
lean_ctor_set(v___x_1658_, 1, v___x_1656_);
return v___x_1658_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6(void){
_start:
{
lean_object* v___x_1659_; lean_object* v___x_1660_; uint32_t v___x_1661_; lean_object* v___x_1662_; 
v___x_1659_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1660_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5);
v___x_1661_ = 61;
v___x_1662_ = l_Lake_Toml_chAtom(v___x_1661_, v___x_1660_, v___x_1659_);
return v___x_1662_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(lean_object* v_val_1663_){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; uint8_t v___x_1673_; lean_object* v___x_1674_; 
v___x_1664_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0));
v___x_1665_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1));
v___x_1666_ = l_Lake_Toml_key;
v___x_1667_ = l_Lake_Toml_trailingWs;
v___x_1668_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6);
v___x_1669_ = l_Lean_Parser_andthen(v___x_1667_, v_val_1663_);
v___x_1670_ = l_Lean_Parser_andthen(v___x_1668_, v___x_1669_);
v___x_1671_ = l_Lean_Parser_andthen(v___x_1667_, v___x_1670_);
v___x_1672_ = l_Lean_Parser_andthen(v___x_1666_, v___x_1671_);
v___x_1673_ = 1;
v___x_1674_ = l_Lean_Parser_nodeWithAntiquot(v___x_1664_, v___x_1665_, v___x_1672_, v___x_1673_);
return v___x_1674_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2(void){
_start:
{
uint8_t v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1680_ = 1;
v___x_1681_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1));
v___x_1682_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0));
v___x_1683_ = l_Lean_Parser_mkAntiquot(v___x_1682_, v___x_1681_, v___x_1680_, v___x_1680_);
return v___x_1683_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(lean_object* v_val_1684_){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v___x_1685_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2, &l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2);
v___x_1686_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(v_val_1684_);
v___x_1687_ = l_Lake_Toml_table;
v___x_1688_ = l_Lean_Parser_orelse(v___x_1686_, v___x_1687_);
v___x_1689_ = l_Lean_Parser_withAntiquot(v___x_1685_, v___x_1688_);
return v___x_1689_;
}
}
static lean_object* _init_l_Lake_Toml_header___closed__2(void){
_start:
{
uint8_t v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1698_; lean_object* v___x_1699_; lean_object* v___x_1700_; 
v___x_1695_ = 0;
v___x_1696_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1697_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1698_ = ((lean_object*)(l_Lake_Toml_header___closed__1));
v___x_1699_ = ((lean_object*)(l_Lake_Toml_header___closed__0));
v___x_1700_ = l_Lake_Toml_litWithAntiquot(v___x_1699_, v___x_1698_, v___x_1697_, v___x_1696_, v___x_1695_);
return v___x_1700_;
}
}
static lean_object* _init_l_Lake_Toml_header(void){
_start:
{
lean_object* v___x_1701_; 
v___x_1701_ = lean_obj_once(&l_Lake_Toml_header___closed__2, &l_Lake_Toml_header___closed__2_once, _init_l_Lake_Toml_header___closed__2);
return v___x_1701_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5(void){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; 
v___x_1711_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__4));
v___x_1712_ = l_Lean_Parser_symbol(v___x_1711_);
return v___x_1712_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; 
v___x_1714_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__6));
v___x_1715_ = l_Lean_Parser_checkLinebreakBefore(v___x_1714_);
return v___x_1715_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8(void){
_start:
{
lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; 
v___x_1716_ = l_Lean_Parser_pushNone;
v___x_1717_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7, &l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7);
v___x_1718_ = l_Lean_Parser_andthen(v___x_1717_, v___x_1716_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore(lean_object* v_val_1719_){
_start:
{
lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; uint8_t v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; lean_object* v_p_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; 
v___x_1720_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0));
v___x_1721_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1));
v___x_1722_ = l_Lake_Toml_header;
v___x_1723_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(v_val_1719_);
v___x_1724_ = l_Lake_Toml_trailingSep;
v___x_1725_ = l_Lean_Parser_andthen(v___x_1723_, v___x_1724_);
v___x_1726_ = 1;
v___x_1727_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__3));
v___x_1728_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5);
v_p_1729_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1727_, v___x_1725_, v___x_1728_);
v___x_1730_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8, &l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8);
v___x_1731_ = l_Lean_Parser_sepByNoAntiquot(v_p_1729_, v___x_1730_, v___x_1726_);
v___x_1732_ = l_Lean_Parser_andthen(v___x_1722_, v___x_1731_);
v___x_1733_ = l_Lean_Parser_nodeWithAntiquot(v___x_1720_, v___x_1721_, v___x_1732_, v___x_1726_);
return v___x_1733_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4(void){
_start:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; uint32_t v___x_1745_; lean_object* v___x_1746_; 
v___x_1743_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1744_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__3));
v___x_1745_ = 123;
v___x_1746_ = l_Lake_Toml_chAtom(v___x_1745_, v___x_1744_, v___x_1743_);
return v___x_1746_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6(void){
_start:
{
uint32_t v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; 
v___x_1748_ = 44;
v___x_1749_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_1750_ = lean_string_push(v___x_1749_, v___x_1748_);
return v___x_1750_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7(void){
_start:
{
lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; 
v___x_1751_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6);
v___x_1752_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1753_ = lean_string_append(v___x_1752_, v___x_1751_);
return v___x_1753_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1754_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1755_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7);
v___x_1756_ = lean_string_append(v___x_1755_, v___x_1754_);
return v___x_1756_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9(void){
_start:
{
lean_object* v___x_1757_; lean_object* v___x_1758_; lean_object* v___x_1759_; 
v___x_1757_ = lean_box(0);
v___x_1758_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8);
v___x_1759_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1759_, 0, v___x_1758_);
lean_ctor_set(v___x_1759_, 1, v___x_1757_);
return v___x_1759_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10(void){
_start:
{
lean_object* v___x_1760_; lean_object* v___x_1761_; uint32_t v___x_1762_; lean_object* v___x_1763_; 
v___x_1760_ = lean_alloc_closure((void*)(l_Lake_Toml_wsFn___boxed), 2, 0);
v___x_1761_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9);
v___x_1762_ = 44;
v___x_1763_ = l_Lake_Toml_chAtom(v___x_1762_, v___x_1761_, v___x_1760_);
return v___x_1763_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11(void){
_start:
{
uint32_t v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; 
v___x_1764_ = 125;
v___x_1765_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_1766_ = lean_string_push(v___x_1765_, v___x_1764_);
return v___x_1766_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12(void){
_start:
{
lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1767_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11);
v___x_1768_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1769_ = lean_string_append(v___x_1768_, v___x_1767_);
return v___x_1769_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13(void){
_start:
{
lean_object* v___x_1770_; lean_object* v___x_1771_; lean_object* v___x_1772_; 
v___x_1770_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1771_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12);
v___x_1772_ = lean_string_append(v___x_1771_, v___x_1770_);
return v___x_1772_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14(void){
_start:
{
lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1773_ = lean_box(0);
v___x_1774_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13);
v___x_1775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1775_, 0, v___x_1774_);
lean_ctor_set(v___x_1775_, 1, v___x_1773_);
return v___x_1775_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15(void){
_start:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; uint32_t v___x_1778_; lean_object* v___x_1779_; 
v___x_1776_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1777_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14);
v___x_1778_ = 125;
v___x_1779_ = l_Lake_Toml_chAtom(v___x_1778_, v___x_1777_, v___x_1776_);
return v___x_1779_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(lean_object* v_val_1780_){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; uint8_t v___x_1789_; lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v___x_1781_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0));
v___x_1782_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1));
v___x_1783_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4);
v___x_1784_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(v_val_1780_);
v___x_1785_ = l_Lake_Toml_trailingWs;
v___x_1786_ = l_Lean_Parser_andthen(v___x_1784_, v___x_1785_);
v___x_1787_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5));
v___x_1788_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10);
v___x_1789_ = 0;
v___x_1790_ = l_Lean_Parser_sepBy(v___x_1786_, v___x_1787_, v___x_1788_, v___x_1789_);
v___x_1791_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15);
v___x_1792_ = l_Lean_Parser_andthen(v___x_1790_, v___x_1791_);
v___x_1793_ = l_Lean_Parser_andthen(v___x_1783_, v___x_1792_);
v___x_1794_ = l_Lean_Parser_nodeWithAntiquot(v___x_1781_, v___x_1782_, v___x_1793_, v___x_1789_);
return v___x_1794_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3(void){
_start:
{
lean_object* v___x_1803_; lean_object* v___x_1804_; uint32_t v___x_1805_; lean_object* v___x_1806_; 
v___x_1803_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1804_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__2));
v___x_1805_ = 91;
v___x_1806_ = l_Lake_Toml_chAtom(v___x_1805_, v___x_1804_, v___x_1803_);
return v___x_1806_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4(void){
_start:
{
lean_object* v___x_1807_; lean_object* v___x_1808_; uint32_t v___x_1809_; lean_object* v___x_1810_; 
v___x_1807_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1808_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9);
v___x_1809_ = 44;
v___x_1810_ = l_Lake_Toml_chAtom(v___x_1809_, v___x_1808_, v___x_1807_);
return v___x_1810_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(lean_object* v_val_1811_){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; uint8_t v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; lean_object* v___x_1822_; lean_object* v___x_1823_; uint8_t v___x_1824_; lean_object* v___x_1825_; 
v___x_1812_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0));
v___x_1813_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1));
v___x_1814_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3, &l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3);
v___x_1815_ = l_Lake_Toml_trailingSep;
v___x_1816_ = l_Lean_Parser_andthen(v_val_1811_, v___x_1815_);
v___x_1817_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5));
v___x_1818_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4, &l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4);
v___x_1819_ = 1;
v___x_1820_ = l_Lean_Parser_sepBy(v___x_1816_, v___x_1817_, v___x_1818_, v___x_1819_);
v___x_1821_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__18, &l_Lake_Toml_stdTable___closed__18_once, _init_l_Lake_Toml_stdTable___closed__18);
v___x_1822_ = l_Lean_Parser_andthen(v___x_1820_, v___x_1821_);
v___x_1823_ = l_Lean_Parser_andthen(v___x_1814_, v___x_1822_);
v___x_1824_ = 0;
v___x_1825_ = l_Lean_Parser_nodeWithAntiquot(v___x_1812_, v___x_1813_, v___x_1823_, v___x_1824_);
return v___x_1825_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__3(void){
_start:
{
lean_object* v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = l_Lake_Toml_literalString;
v___x_1835_ = l_Lake_Toml_mlLiteralString;
v___x_1836_ = l_Lean_Parser_orelse(v___x_1835_, v___x_1834_);
return v___x_1836_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__4(void){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = lean_obj_once(&l_Lake_Toml_string___closed__3, &l_Lake_Toml_string___closed__3_once, _init_l_Lake_Toml_string___closed__3);
v___x_1838_ = l_Lake_Toml_basicString;
v___x_1839_ = l_Lean_Parser_orelse(v___x_1838_, v___x_1837_);
return v___x_1839_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__5(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = lean_obj_once(&l_Lake_Toml_string___closed__4, &l_Lake_Toml_string___closed__4_once, _init_l_Lake_Toml_string___closed__4);
v___x_1841_ = l_Lake_Toml_mlBasicString;
v___x_1842_ = l_Lean_Parser_orelse(v___x_1841_, v___x_1840_);
return v___x_1842_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__6(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = lean_obj_once(&l_Lake_Toml_string___closed__5, &l_Lake_Toml_string___closed__5_once, _init_l_Lake_Toml_string___closed__5);
v___x_1844_ = ((lean_object*)(l_Lake_Toml_string___closed__2));
v___x_1845_ = l_Lean_Parser_setExpected(v___x_1844_, v___x_1843_);
return v___x_1845_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__7(void){
_start:
{
uint8_t v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1846_ = 0;
v___x_1847_ = lean_obj_once(&l_Lake_Toml_string___closed__6, &l_Lake_Toml_string___closed__6_once, _init_l_Lake_Toml_string___closed__6);
v___x_1848_ = ((lean_object*)(l_Lake_Toml_string___closed__1));
v___x_1849_ = ((lean_object*)(l_Lake_Toml_string___closed__0));
v___x_1850_ = l_Lean_Parser_nodeWithAntiquot(v___x_1849_, v___x_1848_, v___x_1847_, v___x_1846_);
return v___x_1850_;
}
}
static lean_object* _init_l_Lake_Toml_string(void){
_start:
{
lean_object* v___x_1851_; 
v___x_1851_ = lean_obj_once(&l_Lake_Toml_string___closed__7, &l_Lake_Toml_string___closed__7_once, _init_l_Lake_Toml_string___closed__7);
return v___x_1851_;
}
}
static lean_object* _init_l_Lake_Toml_true___closed__5(void){
_start:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; lean_object* v___x_1867_; 
v___x_1864_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1865_ = ((lean_object*)(l_Lake_Toml_true___closed__4));
v___x_1866_ = ((lean_object*)(l_Lake_Toml_true___closed__1));
v___x_1867_ = l_Lake_Toml_lit(v___x_1866_, v___x_1865_, v___x_1864_);
return v___x_1867_;
}
}
static lean_object* _init_l_Lake_Toml_true(void){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = lean_obj_once(&l_Lake_Toml_true___closed__5, &l_Lake_Toml_true___closed__5_once, _init_l_Lake_Toml_true___closed__5);
return v___x_1868_;
}
}
static lean_object* _init_l_Lake_Toml_false___closed__5(void){
_start:
{
lean_object* v___x_1881_; lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1881_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1882_ = ((lean_object*)(l_Lake_Toml_false___closed__4));
v___x_1883_ = ((lean_object*)(l_Lake_Toml_false___closed__1));
v___x_1884_ = l_Lake_Toml_lit(v___x_1883_, v___x_1882_, v___x_1881_);
return v___x_1884_;
}
}
static lean_object* _init_l_Lake_Toml_false(void){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_obj_once(&l_Lake_Toml_false___closed__5, &l_Lake_Toml_false___closed__5_once, _init_l_Lake_Toml_false___closed__5);
return v___x_1885_;
}
}
static lean_object* _init_l_Lake_Toml_boolean___closed__2(void){
_start:
{
lean_object* v___x_1891_; lean_object* v___x_1892_; lean_object* v___x_1893_; 
v___x_1891_ = l_Lake_Toml_false;
v___x_1892_ = l_Lake_Toml_true;
v___x_1893_ = l_Lean_Parser_orelse(v___x_1892_, v___x_1891_);
return v___x_1893_;
}
}
static lean_object* _init_l_Lake_Toml_boolean___closed__3(void){
_start:
{
uint8_t v___x_1894_; lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; lean_object* v___x_1898_; 
v___x_1894_ = 0;
v___x_1895_ = lean_obj_once(&l_Lake_Toml_boolean___closed__2, &l_Lake_Toml_boolean___closed__2_once, _init_l_Lake_Toml_boolean___closed__2);
v___x_1896_ = ((lean_object*)(l_Lake_Toml_boolean___closed__1));
v___x_1897_ = ((lean_object*)(l_Lake_Toml_boolean___closed__0));
v___x_1898_ = l_Lean_Parser_nodeWithAntiquot(v___x_1897_, v___x_1896_, v___x_1895_, v___x_1894_);
return v___x_1898_;
}
}
static lean_object* _init_l_Lake_Toml_boolean(void){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = lean_obj_once(&l_Lake_Toml_boolean___closed__3, &l_Lake_Toml_boolean___closed__3_once, _init_l_Lake_Toml_boolean___closed__3);
return v___x_1899_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__0(void){
_start:
{
uint8_t v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1900_ = 0;
v___x_1901_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_1902_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2));
v___x_1903_ = l_Lean_Parser_mkAntiquot(v___x_1902_, v___x_1901_, v___x_1900_, v___x_1900_);
return v___x_1903_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__1(void){
_start:
{
uint8_t v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1904_ = 0;
v___x_1905_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1906_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5));
v___x_1907_ = l_Lean_Parser_mkAntiquot(v___x_1906_, v___x_1905_, v___x_1904_, v___x_1904_);
return v___x_1907_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__2(void){
_start:
{
uint8_t v___x_1908_; lean_object* v___x_1909_; lean_object* v___x_1910_; lean_object* v___x_1911_; 
v___x_1908_ = 0;
v___x_1909_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__17));
v___x_1910_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__16));
v___x_1911_ = l_Lean_Parser_mkAntiquot(v___x_1910_, v___x_1909_, v___x_1908_, v___x_1908_);
return v___x_1911_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__3(void){
_start:
{
uint8_t v___x_1912_; lean_object* v___x_1913_; lean_object* v___x_1914_; lean_object* v___x_1915_; 
v___x_1912_ = 0;
v___x_1913_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__12));
v___x_1914_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__11));
v___x_1915_ = l_Lean_Parser_mkAntiquot(v___x_1914_, v___x_1913_, v___x_1912_, v___x_1912_);
return v___x_1915_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__4(void){
_start:
{
uint8_t v___x_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; 
v___x_1916_ = 0;
v___x_1917_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__7));
v___x_1918_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__6));
v___x_1919_ = l_Lean_Parser_mkAntiquot(v___x_1918_, v___x_1917_, v___x_1916_, v___x_1916_);
return v___x_1919_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__5(void){
_start:
{
uint8_t v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1920_ = 0;
v___x_1921_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_1922_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0));
v___x_1923_ = l_Lean_Parser_mkAntiquot(v___x_1922_, v___x_1921_, v___x_1920_, v___x_1920_);
return v___x_1923_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__8(void){
_start:
{
uint8_t v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; lean_object* v___x_1932_; 
v___x_1929_ = 1;
v___x_1930_ = ((lean_object*)(l_Lake_Toml_numeralAntiquot___closed__7));
v___x_1931_ = ((lean_object*)(l_Lake_Toml_numeralAntiquot___closed__6));
v___x_1932_ = l_Lean_Parser_mkAntiquot(v___x_1931_, v___x_1930_, v___x_1929_, v___x_1929_);
return v___x_1932_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__9(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1933_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__8, &l_Lake_Toml_numeralAntiquot___closed__8_once, _init_l_Lake_Toml_numeralAntiquot___closed__8);
v___x_1934_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__5, &l_Lake_Toml_numeralAntiquot___closed__5_once, _init_l_Lake_Toml_numeralAntiquot___closed__5);
v___x_1935_ = l_Lean_Parser_orelse(v___x_1934_, v___x_1933_);
return v___x_1935_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__10(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; 
v___x_1936_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__9, &l_Lake_Toml_numeralAntiquot___closed__9_once, _init_l_Lake_Toml_numeralAntiquot___closed__9);
v___x_1937_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__4, &l_Lake_Toml_numeralAntiquot___closed__4_once, _init_l_Lake_Toml_numeralAntiquot___closed__4);
v___x_1938_ = l_Lean_Parser_orelse(v___x_1937_, v___x_1936_);
return v___x_1938_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__11(void){
_start:
{
lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; 
v___x_1939_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__10, &l_Lake_Toml_numeralAntiquot___closed__10_once, _init_l_Lake_Toml_numeralAntiquot___closed__10);
v___x_1940_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__3, &l_Lake_Toml_numeralAntiquot___closed__3_once, _init_l_Lake_Toml_numeralAntiquot___closed__3);
v___x_1941_ = l_Lean_Parser_orelse(v___x_1940_, v___x_1939_);
return v___x_1941_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__12(void){
_start:
{
lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; 
v___x_1942_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__11, &l_Lake_Toml_numeralAntiquot___closed__11_once, _init_l_Lake_Toml_numeralAntiquot___closed__11);
v___x_1943_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__2, &l_Lake_Toml_numeralAntiquot___closed__2_once, _init_l_Lake_Toml_numeralAntiquot___closed__2);
v___x_1944_ = l_Lean_Parser_orelse(v___x_1943_, v___x_1942_);
return v___x_1944_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__13(void){
_start:
{
lean_object* v___x_1945_; lean_object* v___x_1946_; lean_object* v___x_1947_; 
v___x_1945_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__12, &l_Lake_Toml_numeralAntiquot___closed__12_once, _init_l_Lake_Toml_numeralAntiquot___closed__12);
v___x_1946_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__1, &l_Lake_Toml_numeralAntiquot___closed__1_once, _init_l_Lake_Toml_numeralAntiquot___closed__1);
v___x_1947_ = l_Lean_Parser_orelse(v___x_1946_, v___x_1945_);
return v___x_1947_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__14(void){
_start:
{
lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v___x_1948_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__13, &l_Lake_Toml_numeralAntiquot___closed__13_once, _init_l_Lake_Toml_numeralAntiquot___closed__13);
v___x_1949_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__0, &l_Lake_Toml_numeralAntiquot___closed__0_once, _init_l_Lake_Toml_numeralAntiquot___closed__0);
v___x_1950_ = l_Lean_Parser_orelse(v___x_1949_, v___x_1948_);
return v___x_1950_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot(void){
_start:
{
lean_object* v___x_1951_; 
v___x_1951_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__14, &l_Lake_Toml_numeralAntiquot___closed__14_once, _init_l_Lake_Toml_numeralAntiquot___closed__14);
return v___x_1951_;
}
}
static lean_object* _init_l_Lake_Toml_numeral___closed__0(void){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1952_ = lean_alloc_closure((void*)(l_Lake_Toml_numeralFn), 2, 0);
v___x_1953_ = l_Lake_Toml_dynamicNode(v___x_1952_);
return v___x_1953_;
}
}
static lean_object* _init_l_Lake_Toml_numeral___closed__1(void){
_start:
{
lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; 
v___x_1954_ = lean_obj_once(&l_Lake_Toml_numeral___closed__0, &l_Lake_Toml_numeral___closed__0_once, _init_l_Lake_Toml_numeral___closed__0);
v___x_1955_ = l_Lake_Toml_numeralAntiquot;
v___x_1956_ = l_Lean_Parser_withAntiquot(v___x_1955_, v___x_1954_);
return v___x_1956_;
}
}
static lean_object* _init_l_Lake_Toml_numeral(void){
_start:
{
lean_object* v___x_1957_; 
v___x_1957_ = lean_obj_once(&l_Lake_Toml_numeral___closed__1, &l_Lake_Toml_numeral___closed__1_once, _init_l_Lake_Toml_numeral___closed__1);
return v___x_1957_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_numeralOfKind___lam__0(lean_object* v_kind_1958_, lean_object* v_x_1959_){
_start:
{
uint8_t v___x_1960_; 
v___x_1960_ = l_Lean_Syntax_isOfKind(v_x_1959_, v_kind_1958_);
return v___x_1960_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralOfKind___lam__0___boxed(lean_object* v_kind_1961_, lean_object* v_x_1962_){
_start:
{
uint8_t v_res_1963_; lean_object* v_r_1964_; 
v_res_1963_ = l_Lake_Toml_numeralOfKind___lam__0(v_kind_1961_, v_x_1962_);
lean_dec(v_kind_1961_);
v_r_1964_ = lean_box(v_res_1963_);
return v_r_1964_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralOfKind(lean_object* v_name_1966_, lean_object* v_kind_1967_){
_start:
{
lean_object* v___f_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; lean_object* v___x_1975_; 
v___f_1968_ = lean_alloc_closure((void*)(l_Lake_Toml_numeralOfKind___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1968_, 0, v_kind_1967_);
v___x_1969_ = l_Lake_Toml_numeral;
v___x_1970_ = lean_box(0);
v___x_1971_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1971_, 0, v_name_1966_);
lean_ctor_set(v___x_1971_, 1, v___x_1970_);
v___x_1972_ = ((lean_object*)(l_Lake_Toml_numeralOfKind___closed__0));
v___x_1973_ = l_Lean_Parser_checkStackTop(v___f_1968_, v___x_1972_);
v___x_1974_ = l_Lean_Parser_setExpected(v___x_1971_, v___x_1973_);
v___x_1975_ = l_Lean_Parser_andthen(v___x_1969_, v___x_1974_);
return v___x_1975_;
}
}
static lean_object* _init_l_Lake_Toml_float___closed__0(void){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1976_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_1977_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2));
v___x_1978_ = l_Lake_Toml_numeralOfKind(v___x_1977_, v___x_1976_);
return v___x_1978_;
}
}
static lean_object* _init_l_Lake_Toml_float(void){
_start:
{
lean_object* v___x_1979_; 
v___x_1979_ = lean_obj_once(&l_Lake_Toml_float___closed__0, &l_Lake_Toml_float___closed__0_once, _init_l_Lake_Toml_float___closed__0);
return v___x_1979_;
}
}
static lean_object* _init_l_Lake_Toml_decInt___closed__0(void){
_start:
{
lean_object* v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; 
v___x_1980_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1981_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0));
v___x_1982_ = l_Lake_Toml_numeralOfKind(v___x_1981_, v___x_1980_);
return v___x_1982_;
}
}
static lean_object* _init_l_Lake_Toml_decInt(void){
_start:
{
lean_object* v___x_1983_; 
v___x_1983_ = lean_obj_once(&l_Lake_Toml_decInt___closed__0, &l_Lake_Toml_decInt___closed__0_once, _init_l_Lake_Toml_decInt___closed__0);
return v___x_1983_;
}
}
static lean_object* _init_l_Lake_Toml_binNum___closed__1(void){
_start:
{
lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1985_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__17));
v___x_1986_ = ((lean_object*)(l_Lake_Toml_binNum___closed__0));
v___x_1987_ = l_Lake_Toml_numeralOfKind(v___x_1986_, v___x_1985_);
return v___x_1987_;
}
}
static lean_object* _init_l_Lake_Toml_binNum(void){
_start:
{
lean_object* v___x_1988_; 
v___x_1988_ = lean_obj_once(&l_Lake_Toml_binNum___closed__1, &l_Lake_Toml_binNum___closed__1_once, _init_l_Lake_Toml_binNum___closed__1);
return v___x_1988_;
}
}
static lean_object* _init_l_Lake_Toml_octNum___closed__1(void){
_start:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; 
v___x_1990_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__12));
v___x_1991_ = ((lean_object*)(l_Lake_Toml_octNum___closed__0));
v___x_1992_ = l_Lake_Toml_numeralOfKind(v___x_1991_, v___x_1990_);
return v___x_1992_;
}
}
static lean_object* _init_l_Lake_Toml_octNum(void){
_start:
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_obj_once(&l_Lake_Toml_octNum___closed__1, &l_Lake_Toml_octNum___closed__1_once, _init_l_Lake_Toml_octNum___closed__1);
return v___x_1993_;
}
}
static lean_object* _init_l_Lake_Toml_hexNum___closed__1(void){
_start:
{
lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1995_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__7));
v___x_1996_ = ((lean_object*)(l_Lake_Toml_hexNum___closed__0));
v___x_1997_ = l_Lake_Toml_numeralOfKind(v___x_1996_, v___x_1995_);
return v___x_1997_;
}
}
static lean_object* _init_l_Lake_Toml_hexNum(void){
_start:
{
lean_object* v___x_1998_; 
v___x_1998_ = lean_obj_once(&l_Lake_Toml_hexNum___closed__1, &l_Lake_Toml_hexNum___closed__1_once, _init_l_Lake_Toml_hexNum___closed__1);
return v___x_1998_;
}
}
static lean_object* _init_l_Lake_Toml_dateTime___closed__0(void){
_start:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_1999_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_2000_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2));
v___x_2001_ = l_Lake_Toml_numeralOfKind(v___x_2000_, v___x_1999_);
return v___x_2001_;
}
}
static lean_object* _init_l_Lake_Toml_dateTime(void){
_start:
{
lean_object* v___x_2002_; 
v___x_2002_ = lean_obj_once(&l_Lake_Toml_dateTime___closed__0, &l_Lake_Toml_dateTime___closed__0_once, _init_l_Lake_Toml_dateTime___closed__0);
return v___x_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_valCore(lean_object* v_val_2003_){
_start:
{
lean_object* v___x_2004_; lean_object* v___x_2005_; lean_object* v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; lean_object* v___x_2012_; 
v___x_2004_ = l_Lake_Toml_string;
v___x_2005_ = l_Lake_Toml_boolean;
v___x_2006_ = l_Lake_Toml_numeral;
lean_inc_ref(v_val_2003_);
v___x_2007_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(v_val_2003_);
v___x_2008_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(v_val_2003_);
v___x_2009_ = l_Lean_Parser_orelse(v___x_2007_, v___x_2008_);
v___x_2010_ = l_Lean_Parser_orelse(v___x_2006_, v___x_2009_);
v___x_2011_ = l_Lean_Parser_orelse(v___x_2005_, v___x_2010_);
v___x_2012_ = l_Lean_Parser_orelse(v___x_2004_, v___x_2011_);
return v___x_2012_;
}
}
static lean_object* _init_l_Lake_Toml_val___closed__3(void){
_start:
{
uint8_t v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; lean_object* v___x_2022_; lean_object* v___x_2023_; 
v___x_2019_ = 1;
v___x_2020_ = ((lean_object*)(l_Lake_Toml_val___closed__2));
v___x_2021_ = ((lean_object*)(l_Lake_Toml_val___closed__1));
v___x_2022_ = ((lean_object*)(l_Lake_Toml_val___closed__0));
v___x_2023_ = l_Lake_Toml_recNodeWithAntiquot(v___x_2022_, v___x_2021_, v___x_2020_, v___x_2019_);
return v___x_2023_;
}
}
static lean_object* _init_l_Lake_Toml_val(void){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = lean_obj_once(&l_Lake_Toml_val___closed__3, &l_Lake_Toml_val___closed__3_once, _init_l_Lake_Toml_val___closed__3);
return v___x_2024_;
}
}
static lean_object* _init_l_Lake_Toml_array___closed__0(void){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; 
v___x_2025_ = l_Lake_Toml_val;
v___x_2026_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(v___x_2025_);
return v___x_2026_;
}
}
static lean_object* _init_l_Lake_Toml_array(void){
_start:
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_obj_once(&l_Lake_Toml_array___closed__0, &l_Lake_Toml_array___closed__0_once, _init_l_Lake_Toml_array___closed__0);
return v___x_2027_;
}
}
static lean_object* _init_l_Lake_Toml_inlineTable___closed__0(void){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = l_Lake_Toml_val;
v___x_2029_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(v___x_2028_);
return v___x_2029_;
}
}
static lean_object* _init_l_Lake_Toml_inlineTable(void){
_start:
{
lean_object* v___x_2030_; 
v___x_2030_ = lean_obj_once(&l_Lake_Toml_inlineTable___closed__0, &l_Lake_Toml_inlineTable___closed__0_once, _init_l_Lake_Toml_inlineTable___closed__0);
return v___x_2030_;
}
}
static lean_object* _init_l_Lake_Toml_keyval___closed__0(void){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; 
v___x_2031_ = l_Lake_Toml_val;
v___x_2032_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(v___x_2031_);
return v___x_2032_;
}
}
static lean_object* _init_l_Lake_Toml_keyval(void){
_start:
{
lean_object* v___x_2033_; 
v___x_2033_ = lean_obj_once(&l_Lake_Toml_keyval___closed__0, &l_Lake_Toml_keyval___closed__0_once, _init_l_Lake_Toml_keyval___closed__0);
return v___x_2033_;
}
}
static lean_object* _init_l_Lake_Toml_expression___closed__0(void){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; 
v___x_2034_ = l_Lake_Toml_val;
v___x_2035_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(v___x_2034_);
return v___x_2035_;
}
}
static lean_object* _init_l_Lake_Toml_expression(void){
_start:
{
lean_object* v___x_2036_; 
v___x_2036_ = lean_obj_once(&l_Lake_Toml_expression___closed__0, &l_Lake_Toml_expression___closed__0_once, _init_l_Lake_Toml_expression___closed__0);
return v___x_2036_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_header_formatter(lean_object* v_a_2037_, lean_object* v_a_2038_, lean_object* v_a_2039_, lean_object* v_a_2040_){
_start:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; uint8_t v___x_2044_; lean_object* v___x_2045_; 
v___x_2042_ = ((lean_object*)(l_Lake_Toml_header___closed__0));
v___x_2043_ = ((lean_object*)(l_Lake_Toml_header___closed__1));
v___x_2044_ = 0;
v___x_2045_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v___x_2042_, v___x_2043_, v___x_2044_, v_a_2037_, v_a_2038_, v_a_2039_, v_a_2040_);
return v___x_2045_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_header_formatter___boxed(lean_object* v_a_2046_, lean_object* v_a_2047_, lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lake_Toml_header_formatter(v_a_2046_, v_a_2047_, v_a_2048_, v_a_2049_);
lean_dec(v_a_2049_);
lean_dec_ref(v_a_2048_);
lean_dec(v_a_2047_);
lean_dec_ref(v_a_2046_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_formatter(lean_object* v_a_2052_, lean_object* v_a_2053_, lean_object* v_a_2054_, lean_object* v_a_2055_){
_start:
{
lean_object* v___x_2057_; lean_object* v___x_2058_; uint8_t v___x_2059_; lean_object* v___x_2060_; 
v___x_2057_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__0));
v___x_2058_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__1));
v___x_2059_ = 0;
v___x_2060_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v___x_2057_, v___x_2058_, v___x_2059_, v_a_2052_, v_a_2053_, v_a_2054_, v_a_2055_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_formatter___boxed(lean_object* v_a_2061_, lean_object* v_a_2062_, lean_object* v_a_2063_, lean_object* v_a_2064_, lean_object* v_a_2065_){
_start:
{
lean_object* v_res_2066_; 
v_res_2066_ = l_Lake_Toml_unquotedKey_formatter(v_a_2061_, v_a_2062_, v_a_2063_, v_a_2064_);
lean_dec(v_a_2064_);
lean_dec_ref(v_a_2063_);
lean_dec(v_a_2062_);
lean_dec_ref(v_a_2061_);
return v_res_2066_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_formatter(lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; uint8_t v___x_2074_; lean_object* v___x_2075_; 
v___x_2072_ = ((lean_object*)(l_Lake_Toml_basicString___closed__0));
v___x_2073_ = ((lean_object*)(l_Lake_Toml_basicString___closed__1));
v___x_2074_ = 0;
v___x_2075_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v___x_2072_, v___x_2073_, v___x_2074_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
return v___x_2075_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_formatter___boxed(lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_){
_start:
{
lean_object* v_res_2081_; 
v_res_2081_ = l_Lake_Toml_basicString_formatter(v_a_2076_, v_a_2077_, v_a_2078_, v_a_2079_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
return v_res_2081_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_formatter(lean_object* v_a_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_){
_start:
{
lean_object* v___x_2087_; lean_object* v___x_2088_; uint8_t v___x_2089_; lean_object* v___x_2090_; 
v___x_2087_ = ((lean_object*)(l_Lake_Toml_literalString___closed__0));
v___x_2088_ = ((lean_object*)(l_Lake_Toml_literalString___closed__1));
v___x_2089_ = 0;
v___x_2090_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v___x_2087_, v___x_2088_, v___x_2089_, v_a_2082_, v_a_2083_, v_a_2084_, v_a_2085_);
return v___x_2090_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_formatter___boxed(lean_object* v_a_2091_, lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_){
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l_Lake_Toml_literalString_formatter(v_a_2091_, v_a_2092_, v_a_2093_, v_a_2094_);
lean_dec(v_a_2094_);
lean_dec_ref(v_a_2093_);
lean_dec(v_a_2092_);
lean_dec_ref(v_a_2091_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_formatter(lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v___x_2102_; lean_object* v___x_2103_; lean_object* v___x_2104_; 
v___x_2102_ = lean_alloc_closure((void*)(l_Lake_Toml_basicString_formatter___boxed), 5, 0);
v___x_2103_ = lean_alloc_closure((void*)(l_Lake_Toml_literalString_formatter___boxed), 5, 0);
v___x_2104_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2102_, v___x_2103_, v_a_2097_, v_a_2098_, v_a_2099_, v_a_2100_);
return v___x_2104_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_formatter___boxed(lean_object* v_a_2105_, lean_object* v_a_2106_, lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_){
_start:
{
lean_object* v_res_2110_; 
v_res_2110_ = l_Lake_Toml_quotedKey_formatter(v_a_2105_, v_a_2106_, v_a_2107_, v_a_2108_);
lean_dec(v_a_2108_);
lean_dec_ref(v_a_2107_);
lean_dec(v_a_2106_);
lean_dec_ref(v_a_2105_);
return v_res_2110_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey_formatter___closed__0(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2111_ = lean_alloc_closure((void*)(l_Lake_Toml_quotedKey_formatter___boxed), 5, 0);
v___x_2112_ = lean_alloc_closure((void*)(l_Lake_Toml_unquotedKey_formatter___boxed), 5, 0);
v___x_2113_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2113_, 0, v___x_2112_);
lean_closure_set(v___x_2113_, 1, v___x_2111_);
return v___x_2113_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_formatter(lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; uint8_t v___x_2122_; lean_object* v___x_2123_; 
v___x_2119_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__0));
v___x_2120_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__1));
v___x_2121_ = lean_obj_once(&l_Lake_Toml_simpleKey_formatter___closed__0, &l_Lake_Toml_simpleKey_formatter___closed__0_once, _init_l_Lake_Toml_simpleKey_formatter___closed__0);
v___x_2122_ = 1;
v___x_2123_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2119_, v___x_2120_, v___x_2121_, v___x_2122_, v_a_2114_, v_a_2115_, v_a_2116_, v_a_2117_);
return v___x_2123_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_formatter___boxed(lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_, lean_object* v_a_2128_){
_start:
{
lean_object* v_res_2129_; 
v_res_2129_ = l_Lake_Toml_simpleKey_formatter(v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_);
lean_dec(v_a_2127_);
lean_dec_ref(v_a_2126_);
lean_dec(v_a_2125_);
lean_dec_ref(v_a_2124_);
return v_res_2129_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter___redArg(){
_start:
{
lean_object* v___x_2131_; 
v___x_2131_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter___redArg___boxed(lean_object* v_a_2132_){
_start:
{
lean_object* v_res_2133_; 
v_res_2133_ = l_Lake_Toml_trailingWs_formatter___redArg();
return v_res_2133_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter(lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_){
_start:
{
lean_object* v___x_2139_; 
v___x_2139_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter___boxed(lean_object* v_a_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_){
_start:
{
lean_object* v_res_2145_; 
v_res_2145_ = l_Lake_Toml_trailingWs_formatter(v_a_2140_, v_a_2141_, v_a_2142_, v_a_2143_);
lean_dec(v_a_2143_);
lean_dec_ref(v_a_2142_);
lean_dec(v_a_2141_);
lean_dec_ref(v_a_2140_);
return v_res_2145_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_2146_; lean_object* v___x_2147_; 
v___x_2146_ = 46;
v___x_2147_ = lean_box_uint32(v___x_2146_);
return v___x_2147_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__0(void){
_start:
{
lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; 
v___x_2148_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2149_ = lean_obj_once(&l_Lake_Toml_key___closed__7, &l_Lake_Toml_key___closed__7_once, _init_l_Lake_Toml_key___closed__7);
v___x_2150_ = l_Lake_Toml_key_formatter___closed__0___boxed__const__1;
v___x_2151_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2151_, 0, v___x_2150_);
lean_closure_set(v___x_2151_, 1, v___x_2149_);
lean_closure_set(v___x_2151_, 2, v___x_2148_);
return v___x_2151_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__1(void){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; 
v___x_2152_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2153_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__0, &l_Lake_Toml_key_formatter___closed__0_once, _init_l_Lake_Toml_key_formatter___closed__0);
v___x_2154_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2154_, 0, v___x_2153_);
lean_closure_set(v___x_2154_, 1, v___x_2152_);
return v___x_2154_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__2(void){
_start:
{
lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; 
v___x_2155_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__1, &l_Lake_Toml_key_formatter___closed__1_once, _init_l_Lake_Toml_key_formatter___closed__1);
v___x_2156_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2157_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2157_, 0, v___x_2156_);
lean_closure_set(v___x_2157_, 1, v___x_2155_);
return v___x_2157_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__3(void){
_start:
{
uint8_t v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2158_ = 0;
v___x_2159_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__2, &l_Lake_Toml_key_formatter___closed__2_once, _init_l_Lake_Toml_key_formatter___closed__2);
v___x_2160_ = ((lean_object*)(l_Lake_Toml_key___closed__3));
v___x_2161_ = lean_alloc_closure((void*)(l_Lake_Toml_simpleKey_formatter___boxed), 5, 0);
v___x_2162_ = lean_box(v___x_2158_);
v___x_2163_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_formatter___boxed), 9, 4);
lean_closure_set(v___x_2163_, 0, v___x_2161_);
lean_closure_set(v___x_2163_, 1, v___x_2160_);
lean_closure_set(v___x_2163_, 2, v___x_2159_);
lean_closure_set(v___x_2163_, 3, v___x_2162_);
return v___x_2163_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__4(void){
_start:
{
lean_object* v___x_2164_; lean_object* v___x_2165_; lean_object* v___x_2166_; 
v___x_2164_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__3, &l_Lake_Toml_key_formatter___closed__3_once, _init_l_Lake_Toml_key_formatter___closed__3);
v___x_2165_ = ((lean_object*)(l_Lake_Toml_key___closed__2));
v___x_2166_ = lean_alloc_closure((void*)(l_Lean_Parser_setExpected_formatter___boxed), 7, 2);
lean_closure_set(v___x_2166_, 0, v___x_2165_);
lean_closure_set(v___x_2166_, 1, v___x_2164_);
return v___x_2166_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_key_formatter(lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_){
_start:
{
lean_object* v___x_2172_; lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; lean_object* v___x_2176_; 
v___x_2172_ = ((lean_object*)(l_Lake_Toml_key___closed__0));
v___x_2173_ = ((lean_object*)(l_Lake_Toml_key___closed__1));
v___x_2174_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__4, &l_Lake_Toml_key_formatter___closed__4_once, _init_l_Lake_Toml_key_formatter___closed__4);
v___x_2175_ = 1;
v___x_2176_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2172_, v___x_2173_, v___x_2174_, v___x_2175_, v_a_2167_, v_a_2168_, v_a_2169_, v_a_2170_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_key_formatter___boxed(lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lake_Toml_key_formatter(v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
lean_dec(v_a_2178_);
lean_dec_ref(v_a_2177_);
return v_res_2182_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_2183_; lean_object* v___x_2184_; 
v___x_2183_ = 61;
v___x_2184_ = lean_box_uint32(v___x_2183_);
return v___x_2184_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0(void){
_start:
{
lean_object* v___x_2185_; lean_object* v___x_2186_; lean_object* v___x_2187_; lean_object* v___x_2188_; 
v___x_2185_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2186_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5);
v___x_2187_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1;
v___x_2188_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2188_, 0, v___x_2187_);
lean_closure_set(v___x_2188_, 1, v___x_2186_);
lean_closure_set(v___x_2188_, 2, v___x_2185_);
return v___x_2188_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter(lean_object* v_val_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_){
_start:
{
lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; uint8_t v___x_2204_; lean_object* v___x_2205_; 
v___x_2195_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0));
v___x_2196_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1));
v___x_2197_ = lean_alloc_closure((void*)(l_Lake_Toml_key_formatter___boxed), 5, 0);
v___x_2198_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2199_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0);
lean_inc_ref(v___x_2198_);
v___x_2200_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2200_, 0, v___x_2198_);
lean_closure_set(v___x_2200_, 1, v_val_2189_);
v___x_2201_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2201_, 0, v___x_2199_);
lean_closure_set(v___x_2201_, 1, v___x_2200_);
v___x_2202_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2202_, 0, v___x_2198_);
lean_closure_set(v___x_2202_, 1, v___x_2201_);
v___x_2203_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2203_, 0, v___x_2197_);
lean_closure_set(v___x_2203_, 1, v___x_2202_);
v___x_2204_ = 1;
v___x_2205_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2195_, v___x_2196_, v___x_2203_, v___x_2204_, v_a_2190_, v_a_2191_, v_a_2192_, v_a_2193_);
return v___x_2205_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___boxed(lean_object* v_val_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_, lean_object* v_a_2210_, lean_object* v_a_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter(v_val_2206_, v_a_2207_, v_a_2208_, v_a_2209_, v_a_2210_);
lean_dec(v_a_2210_);
lean_dec_ref(v_a_2209_);
lean_dec(v_a_2208_);
lean_dec_ref(v_a_2207_);
return v_res_2212_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_2213_; lean_object* v___x_2214_; 
v___x_2213_ = 91;
v___x_2214_ = lean_box_uint32(v___x_2213_);
return v___x_2214_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__0(void){
_start:
{
lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2215_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2216_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__3));
v___x_2217_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
v___x_2218_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2218_, 0, v___x_2217_);
lean_closure_set(v___x_2218_, 1, v___x_2216_);
lean_closure_set(v___x_2218_, 2, v___x_2215_);
return v___x_2218_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__1(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
v___x_2219_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2220_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__8, &l_Lake_Toml_stdTable___closed__8_once, _init_l_Lake_Toml_stdTable___closed__8);
v___x_2221_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
v___x_2222_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2222_, 0, v___x_2221_);
lean_closure_set(v___x_2222_, 1, v___x_2220_);
lean_closure_set(v___x_2222_, 2, v___x_2219_);
return v___x_2222_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__2(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; 
v___x_2223_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__1, &l_Lake_Toml_stdTable_formatter___closed__1_once, _init_l_Lake_Toml_stdTable_formatter___closed__1);
v___x_2224_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed), 6, 1);
lean_closure_set(v___x_2224_, 0, v___x_2223_);
return v___x_2224_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__3(void){
_start:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2225_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__2, &l_Lake_Toml_stdTable_formatter___closed__2_once, _init_l_Lake_Toml_stdTable_formatter___closed__2);
v___x_2226_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__0, &l_Lake_Toml_stdTable_formatter___closed__0_once, _init_l_Lake_Toml_stdTable_formatter___closed__0);
v___x_2227_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2227_, 0, v___x_2226_);
lean_closure_set(v___x_2227_, 1, v___x_2225_);
return v___x_2227_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__4(void){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__3, &l_Lake_Toml_stdTable_formatter___closed__3_once, _init_l_Lake_Toml_stdTable_formatter___closed__3);
v___x_2229_ = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter___boxed), 6, 1);
lean_closure_set(v___x_2229_, 0, v___x_2228_);
return v___x_2229_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1(void){
_start:
{
uint32_t v___x_2230_; lean_object* v___x_2231_; 
v___x_2230_ = 93;
v___x_2231_ = lean_box_uint32(v___x_2230_);
return v___x_2231_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__5(void){
_start:
{
lean_object* v___x_2232_; lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2232_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2233_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__17, &l_Lake_Toml_stdTable___closed__17_once, _init_l_Lake_Toml_stdTable___closed__17);
v___x_2234_ = l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1;
v___x_2235_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2235_, 0, v___x_2234_);
lean_closure_set(v___x_2235_, 1, v___x_2233_);
lean_closure_set(v___x_2235_, 2, v___x_2232_);
return v___x_2235_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__6(void){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2236_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__5, &l_Lake_Toml_stdTable_formatter___closed__5_once, _init_l_Lake_Toml_stdTable_formatter___closed__5);
v___x_2237_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2238_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2238_, 0, v___x_2237_);
lean_closure_set(v___x_2238_, 1, v___x_2236_);
return v___x_2238_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__7(void){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2239_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__6, &l_Lake_Toml_stdTable_formatter___closed__6_once, _init_l_Lake_Toml_stdTable_formatter___closed__6);
v___x_2240_ = lean_alloc_closure((void*)(l_Lake_Toml_key_formatter___boxed), 5, 0);
v___x_2241_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2241_, 0, v___x_2240_);
lean_closure_set(v___x_2241_, 1, v___x_2239_);
return v___x_2241_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__8(void){
_start:
{
lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; 
v___x_2242_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__7, &l_Lake_Toml_stdTable_formatter___closed__7_once, _init_l_Lake_Toml_stdTable_formatter___closed__7);
v___x_2243_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2244_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2244_, 0, v___x_2243_);
lean_closure_set(v___x_2244_, 1, v___x_2242_);
return v___x_2244_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__9(void){
_start:
{
lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; 
v___x_2245_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__8, &l_Lake_Toml_stdTable_formatter___closed__8_once, _init_l_Lake_Toml_stdTable_formatter___closed__8);
v___x_2246_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__4, &l_Lake_Toml_stdTable_formatter___closed__4_once, _init_l_Lake_Toml_stdTable_formatter___closed__4);
v___x_2247_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2247_, 0, v___x_2246_);
lean_closure_set(v___x_2247_, 1, v___x_2245_);
return v___x_2247_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_formatter(lean_object* v_a_2248_, lean_object* v_a_2249_, lean_object* v_a_2250_, lean_object* v_a_2251_){
_start:
{
lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; uint8_t v___x_2256_; lean_object* v___x_2257_; 
v___x_2253_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__0));
v___x_2254_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__1));
v___x_2255_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__9, &l_Lake_Toml_stdTable_formatter___closed__9_once, _init_l_Lake_Toml_stdTable_formatter___closed__9);
v___x_2256_ = 0;
v___x_2257_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2253_, v___x_2254_, v___x_2255_, v___x_2256_, v_a_2248_, v_a_2249_, v_a_2250_, v_a_2251_);
return v___x_2257_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_formatter___boxed(lean_object* v_a_2258_, lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_){
_start:
{
lean_object* v_res_2263_; 
v_res_2263_ = l_Lake_Toml_stdTable_formatter(v_a_2258_, v_a_2259_, v_a_2260_, v_a_2261_);
lean_dec(v_a_2261_);
lean_dec_ref(v_a_2260_);
lean_dec(v_a_2259_);
lean_dec_ref(v_a_2258_);
return v_res_2263_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__0(void){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2264_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__1, &l_Lake_Toml_stdTable_formatter___closed__1_once, _init_l_Lake_Toml_stdTable_formatter___closed__1);
v___x_2265_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__0, &l_Lake_Toml_stdTable_formatter___closed__0_once, _init_l_Lake_Toml_stdTable_formatter___closed__0);
v___x_2266_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2266_, 0, v___x_2265_);
lean_closure_set(v___x_2266_, 1, v___x_2264_);
return v___x_2266_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__1(void){
_start:
{
lean_object* v___x_2267_; lean_object* v___x_2268_; 
v___x_2267_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__0, &l_Lake_Toml_arrayTable_formatter___closed__0_once, _init_l_Lake_Toml_arrayTable_formatter___closed__0);
v___x_2268_ = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter___boxed), 6, 1);
lean_closure_set(v___x_2268_, 0, v___x_2267_);
return v___x_2268_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__2(void){
_start:
{
lean_object* v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__5, &l_Lake_Toml_stdTable_formatter___closed__5_once, _init_l_Lake_Toml_stdTable_formatter___closed__5);
v___x_2270_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2270_, 0, v___x_2269_);
lean_closure_set(v___x_2270_, 1, v___x_2269_);
return v___x_2270_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__3(void){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2271_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__2, &l_Lake_Toml_arrayTable_formatter___closed__2_once, _init_l_Lake_Toml_arrayTable_formatter___closed__2);
v___x_2272_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2273_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2273_, 0, v___x_2272_);
lean_closure_set(v___x_2273_, 1, v___x_2271_);
return v___x_2273_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__4(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; 
v___x_2274_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__3, &l_Lake_Toml_arrayTable_formatter___closed__3_once, _init_l_Lake_Toml_arrayTable_formatter___closed__3);
v___x_2275_ = lean_alloc_closure((void*)(l_Lake_Toml_key_formatter___boxed), 5, 0);
v___x_2276_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2276_, 0, v___x_2275_);
lean_closure_set(v___x_2276_, 1, v___x_2274_);
return v___x_2276_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__5(void){
_start:
{
lean_object* v___x_2277_; lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2277_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__4, &l_Lake_Toml_arrayTable_formatter___closed__4_once, _init_l_Lake_Toml_arrayTable_formatter___closed__4);
v___x_2278_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2279_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2279_, 0, v___x_2278_);
lean_closure_set(v___x_2279_, 1, v___x_2277_);
return v___x_2279_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__6(void){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__5, &l_Lake_Toml_arrayTable_formatter___closed__5_once, _init_l_Lake_Toml_arrayTable_formatter___closed__5);
v___x_2281_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__1, &l_Lake_Toml_arrayTable_formatter___closed__1_once, _init_l_Lake_Toml_arrayTable_formatter___closed__1);
v___x_2282_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2282_, 0, v___x_2281_);
lean_closure_set(v___x_2282_, 1, v___x_2280_);
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_formatter(lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_, lean_object* v_a_2286_){
_start:
{
lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; uint8_t v___x_2291_; lean_object* v___x_2292_; 
v___x_2288_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__0));
v___x_2289_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__1));
v___x_2290_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__6, &l_Lake_Toml_arrayTable_formatter___closed__6_once, _init_l_Lake_Toml_arrayTable_formatter___closed__6);
v___x_2291_ = 0;
v___x_2292_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2288_, v___x_2289_, v___x_2290_, v___x_2291_, v_a_2283_, v_a_2284_, v_a_2285_, v_a_2286_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_formatter___boxed(lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l_Lake_Toml_arrayTable_formatter(v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
return v_res_2298_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_table_formatter(lean_object* v_a_2299_, lean_object* v_a_2300_, lean_object* v_a_2301_, lean_object* v_a_2302_){
_start:
{
lean_object* v___x_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v___x_2304_ = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_formatter___boxed), 5, 0);
v___x_2305_ = lean_alloc_closure((void*)(l_Lake_Toml_arrayTable_formatter___boxed), 5, 0);
v___x_2306_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2304_, v___x_2305_, v_a_2299_, v_a_2300_, v_a_2301_, v_a_2302_);
return v___x_2306_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_table_formatter___boxed(lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_, lean_object* v_a_2310_, lean_object* v_a_2311_){
_start:
{
lean_object* v_res_2312_; 
v_res_2312_ = l_Lake_Toml_table_formatter(v_a_2307_, v_a_2308_, v_a_2309_, v_a_2310_);
lean_dec(v_a_2310_);
lean_dec_ref(v_a_2309_);
lean_dec(v_a_2308_);
lean_dec_ref(v_a_2307_);
return v_res_2312_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter(lean_object* v_val_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; 
v___x_2325_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___closed__0));
v___x_2326_ = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___boxed), 6, 1);
lean_closure_set(v___x_2326_, 0, v_val_2319_);
v___x_2327_ = lean_alloc_closure((void*)(l_Lake_Toml_table_formatter___boxed), 5, 0);
v___x_2328_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2328_, 0, v___x_2326_);
lean_closure_set(v___x_2328_, 1, v___x_2327_);
v___x_2329_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2325_, v___x_2328_, v_a_2320_, v_a_2321_, v_a_2322_, v_a_2323_);
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___boxed(lean_object* v_val_2330_, lean_object* v_a_2331_, lean_object* v_a_2332_, lean_object* v_a_2333_, lean_object* v_a_2334_, lean_object* v_a_2335_){
_start:
{
lean_object* v_res_2336_; 
v_res_2336_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter(v_val_2330_, v_a_2331_, v_a_2332_, v_a_2333_, v_a_2334_);
lean_dec(v_a_2334_);
lean_dec_ref(v_a_2333_);
lean_dec(v_a_2332_);
lean_dec_ref(v_a_2331_);
return v_res_2336_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter___redArg(){
_start:
{
lean_object* v___x_2338_; 
v___x_2338_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_2338_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter___redArg___boxed(lean_object* v_a_2339_){
_start:
{
lean_object* v_res_2340_; 
v_res_2340_ = l_Lake_Toml_trailingSep_formatter___redArg();
return v_res_2340_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter(lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_){
_start:
{
lean_object* v___x_2346_; 
v___x_2346_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_2346_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter___boxed(lean_object* v_a_2347_, lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_){
_start:
{
lean_object* v_res_2352_; 
v_res_2352_ = l_Lake_Toml_trailingSep_formatter(v_a_2347_, v_a_2348_, v_a_2349_, v_a_2350_);
lean_dec(v_a_2350_);
lean_dec_ref(v_a_2349_);
lean_dec(v_a_2348_);
lean_dec_ref(v_a_2347_);
return v_res_2352_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(lean_object* v_val_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; uint8_t v___x_2365_; lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2359_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0));
v___x_2360_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1));
v___x_2361_ = lean_alloc_closure((void*)(l_Lake_Toml_header_formatter___boxed), 5, 0);
v___x_2362_ = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___boxed), 6, 1);
lean_closure_set(v___x_2362_, 0, v_val_2353_);
v___x_2363_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingSep_formatter___boxed), 5, 0);
v___x_2364_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2364_, 0, v___x_2362_);
lean_closure_set(v___x_2364_, 1, v___x_2363_);
v___x_2365_ = 1;
v___x_2366_ = lean_box(v___x_2365_);
v___x_2367_ = lean_alloc_closure((void*)(l_Lake_Toml_sepByLinebreak_formatter___boxed), 7, 2);
lean_closure_set(v___x_2367_, 0, v___x_2364_);
lean_closure_set(v___x_2367_, 1, v___x_2366_);
v___x_2368_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2368_, 0, v___x_2361_);
lean_closure_set(v___x_2368_, 1, v___x_2367_);
v___x_2369_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2359_, v___x_2360_, v___x_2368_, v___x_2365_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
return v___x_2369_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter___boxed(lean_object* v_val_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_){
_start:
{
lean_object* v_res_2376_; 
v_res_2376_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(v_val_2370_, v_a_2371_, v_a_2372_, v_a_2373_, v_a_2374_);
lean_dec(v_a_2374_);
lean_dec_ref(v_a_2373_);
lean_dec(v_a_2372_);
lean_dec_ref(v_a_2371_);
return v_res_2376_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_val_formatter(lean_object* v_a_2377_, lean_object* v_a_2378_, lean_object* v_a_2379_, lean_object* v_a_2380_){
_start:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; uint8_t v___x_2385_; lean_object* v___x_2386_; 
v___x_2382_ = ((lean_object*)(l_Lake_Toml_val___closed__0));
v___x_2383_ = ((lean_object*)(l_Lake_Toml_val___closed__1));
v___x_2384_ = ((lean_object*)(l_Lake_Toml_val___closed__2));
v___x_2385_ = 1;
v___x_2386_ = l_Lake_Toml_recNodeWithAntiquot_formatter(v___x_2382_, v___x_2383_, v___x_2384_, v___x_2385_, v_a_2377_, v_a_2378_, v_a_2379_, v_a_2380_);
return v___x_2386_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_val_formatter___boxed(lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_Lake_Toml_val_formatter(v_a_2387_, v_a_2388_, v_a_2389_, v_a_2390_);
lean_dec(v_a_2390_);
lean_dec_ref(v_a_2389_);
lean_dec(v_a_2388_);
lean_dec_ref(v_a_2387_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_toml_formatter(lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_){
_start:
{
lean_object* v___x_2398_; lean_object* v___x_2399_; 
v___x_2398_ = lean_alloc_closure((void*)(l_Lake_Toml_val_formatter___boxed), 5, 0);
v___x_2399_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(v___x_2398_, v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
return v___x_2399_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_toml_formatter___boxed(lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l_Lake_Toml_toml_formatter(v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_2402_);
lean_dec(v_a_2401_);
lean_dec_ref(v_a_2400_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_header_parenthesizer(lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; uint8_t v___x_2413_; lean_object* v___x_2414_; 
v___x_2411_ = ((lean_object*)(l_Lake_Toml_header___closed__0));
v___x_2412_ = ((lean_object*)(l_Lake_Toml_header___closed__1));
v___x_2413_ = 0;
v___x_2414_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v___x_2411_, v___x_2412_, v___x_2413_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_header_parenthesizer___boxed(lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Lake_Toml_header_parenthesizer(v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_parenthesizer(lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; lean_object* v___x_2429_; 
v___x_2426_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__0));
v___x_2427_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__1));
v___x_2428_ = 0;
v___x_2429_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v___x_2426_, v___x_2427_, v___x_2428_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
return v___x_2429_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_parenthesizer___boxed(lean_object* v_a_2430_, lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_){
_start:
{
lean_object* v_res_2435_; 
v_res_2435_ = l_Lake_Toml_unquotedKey_parenthesizer(v_a_2430_, v_a_2431_, v_a_2432_, v_a_2433_);
lean_dec(v_a_2433_);
lean_dec_ref(v_a_2432_);
lean_dec(v_a_2431_);
lean_dec_ref(v_a_2430_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_parenthesizer(lean_object* v_a_2436_, lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_){
_start:
{
lean_object* v___x_2441_; lean_object* v___x_2442_; uint8_t v___x_2443_; lean_object* v___x_2444_; 
v___x_2441_ = ((lean_object*)(l_Lake_Toml_basicString___closed__0));
v___x_2442_ = ((lean_object*)(l_Lake_Toml_basicString___closed__1));
v___x_2443_ = 0;
v___x_2444_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v___x_2441_, v___x_2442_, v___x_2443_, v_a_2436_, v_a_2437_, v_a_2438_, v_a_2439_);
return v___x_2444_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_parenthesizer___boxed(lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Lake_Toml_basicString_parenthesizer(v_a_2445_, v_a_2446_, v_a_2447_, v_a_2448_);
lean_dec(v_a_2448_);
lean_dec_ref(v_a_2447_);
lean_dec(v_a_2446_);
lean_dec_ref(v_a_2445_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_parenthesizer(lean_object* v_a_2451_, lean_object* v_a_2452_, lean_object* v_a_2453_, lean_object* v_a_2454_){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; uint8_t v___x_2458_; lean_object* v___x_2459_; 
v___x_2456_ = ((lean_object*)(l_Lake_Toml_literalString___closed__0));
v___x_2457_ = ((lean_object*)(l_Lake_Toml_literalString___closed__1));
v___x_2458_ = 0;
v___x_2459_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v___x_2456_, v___x_2457_, v___x_2458_, v_a_2451_, v_a_2452_, v_a_2453_, v_a_2454_);
return v___x_2459_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_parenthesizer___boxed(lean_object* v_a_2460_, lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_){
_start:
{
lean_object* v_res_2465_; 
v_res_2465_ = l_Lake_Toml_literalString_parenthesizer(v_a_2460_, v_a_2461_, v_a_2462_, v_a_2463_);
lean_dec(v_a_2463_);
lean_dec_ref(v_a_2462_);
lean_dec(v_a_2461_);
lean_dec_ref(v_a_2460_);
return v_res_2465_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_parenthesizer(lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_){
_start:
{
lean_object* v___x_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v___x_2471_ = lean_alloc_closure((void*)(l_Lake_Toml_basicString_parenthesizer___boxed), 5, 0);
v___x_2472_ = lean_alloc_closure((void*)(l_Lake_Toml_literalString_parenthesizer___boxed), 5, 0);
v___x_2473_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___x_2471_, v___x_2472_, v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_parenthesizer___boxed(lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_Lake_Toml_quotedKey_parenthesizer(v_a_2474_, v_a_2475_, v_a_2476_, v_a_2477_);
lean_dec(v_a_2477_);
lean_dec_ref(v_a_2476_);
lean_dec(v_a_2475_);
lean_dec_ref(v_a_2474_);
return v_res_2479_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2480_; lean_object* v___x_2481_; lean_object* v___x_2482_; 
v___x_2480_ = lean_alloc_closure((void*)(l_Lake_Toml_quotedKey_parenthesizer___boxed), 5, 0);
v___x_2481_ = lean_alloc_closure((void*)(l_Lake_Toml_unquotedKey_parenthesizer___boxed), 5, 0);
v___x_2482_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2482_, 0, v___x_2481_);
lean_closure_set(v___x_2482_, 1, v___x_2480_);
return v___x_2482_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_parenthesizer(lean_object* v_a_2483_, lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_){
_start:
{
lean_object* v___x_2488_; lean_object* v___x_2489_; lean_object* v___x_2490_; uint8_t v___x_2491_; lean_object* v___x_2492_; 
v___x_2488_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__0));
v___x_2489_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__1));
v___x_2490_ = lean_obj_once(&l_Lake_Toml_simpleKey_parenthesizer___closed__0, &l_Lake_Toml_simpleKey_parenthesizer___closed__0_once, _init_l_Lake_Toml_simpleKey_parenthesizer___closed__0);
v___x_2491_ = 1;
v___x_2492_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2488_, v___x_2489_, v___x_2490_, v___x_2491_, v_a_2483_, v_a_2484_, v_a_2485_, v_a_2486_);
return v___x_2492_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_parenthesizer___boxed(lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_, lean_object* v_a_2496_, lean_object* v_a_2497_){
_start:
{
lean_object* v_res_2498_; 
v_res_2498_ = l_Lake_Toml_simpleKey_parenthesizer(v_a_2493_, v_a_2494_, v_a_2495_, v_a_2496_);
lean_dec(v_a_2496_);
lean_dec_ref(v_a_2495_);
lean_dec(v_a_2494_);
lean_dec_ref(v_a_2493_);
return v_res_2498_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer___redArg(){
_start:
{
lean_object* v___x_2500_; 
v___x_2500_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer___redArg___boxed(lean_object* v_a_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_Lake_Toml_trailingWs_parenthesizer___redArg();
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer(lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_, lean_object* v_a_2506_){
_start:
{
lean_object* v___x_2508_; 
v___x_2508_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_2508_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer___boxed(lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_, lean_object* v_a_2513_){
_start:
{
lean_object* v_res_2514_; 
v_res_2514_ = l_Lake_Toml_trailingWs_parenthesizer(v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
lean_dec(v_a_2512_);
lean_dec_ref(v_a_2511_);
lean_dec(v_a_2510_);
lean_dec_ref(v_a_2509_);
return v_res_2514_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; 
v___x_2515_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2516_ = lean_obj_once(&l_Lake_Toml_key___closed__7, &l_Lake_Toml_key___closed__7_once, _init_l_Lake_Toml_key___closed__7);
v___x_2517_ = l_Lake_Toml_key_formatter___closed__0___boxed__const__1;
v___x_2518_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2518_, 0, v___x_2517_);
lean_closure_set(v___x_2518_, 1, v___x_2516_);
lean_closure_set(v___x_2518_, 2, v___x_2515_);
return v___x_2518_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_2519_; lean_object* v___x_2520_; lean_object* v___x_2521_; 
v___x_2519_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2520_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__0, &l_Lake_Toml_key_parenthesizer___closed__0_once, _init_l_Lake_Toml_key_parenthesizer___closed__0);
v___x_2521_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2521_, 0, v___x_2520_);
lean_closure_set(v___x_2521_, 1, v___x_2519_);
return v___x_2521_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; 
v___x_2522_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__1, &l_Lake_Toml_key_parenthesizer___closed__1_once, _init_l_Lake_Toml_key_parenthesizer___closed__1);
v___x_2523_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2524_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2524_, 0, v___x_2523_);
lean_closure_set(v___x_2524_, 1, v___x_2522_);
return v___x_2524_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__3(void){
_start:
{
uint8_t v___x_2525_; lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2525_ = 0;
v___x_2526_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__2, &l_Lake_Toml_key_parenthesizer___closed__2_once, _init_l_Lake_Toml_key_parenthesizer___closed__2);
v___x_2527_ = ((lean_object*)(l_Lake_Toml_key___closed__3));
v___x_2528_ = lean_alloc_closure((void*)(l_Lake_Toml_simpleKey_parenthesizer___boxed), 5, 0);
v___x_2529_ = lean_box(v___x_2525_);
v___x_2530_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_2530_, 0, v___x_2528_);
lean_closure_set(v___x_2530_, 1, v___x_2527_);
lean_closure_set(v___x_2530_, 2, v___x_2526_);
lean_closure_set(v___x_2530_, 3, v___x_2529_);
return v___x_2530_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2531_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__3, &l_Lake_Toml_key_parenthesizer___closed__3_once, _init_l_Lake_Toml_key_parenthesizer___closed__3);
v___x_2532_ = ((lean_object*)(l_Lake_Toml_key___closed__2));
v___x_2533_ = lean_alloc_closure((void*)(l_Lean_Parser_setExpected_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2533_, 0, v___x_2532_);
lean_closure_set(v___x_2533_, 1, v___x_2531_);
return v___x_2533_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_key_parenthesizer(lean_object* v_a_2534_, lean_object* v_a_2535_, lean_object* v_a_2536_, lean_object* v_a_2537_){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; uint8_t v___x_2542_; lean_object* v___x_2543_; 
v___x_2539_ = ((lean_object*)(l_Lake_Toml_key___closed__0));
v___x_2540_ = ((lean_object*)(l_Lake_Toml_key___closed__1));
v___x_2541_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__4, &l_Lake_Toml_key_parenthesizer___closed__4_once, _init_l_Lake_Toml_key_parenthesizer___closed__4);
v___x_2542_ = 1;
v___x_2543_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2539_, v___x_2540_, v___x_2541_, v___x_2542_, v_a_2534_, v_a_2535_, v_a_2536_, v_a_2537_);
return v___x_2543_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_key_parenthesizer___boxed(lean_object* v_a_2544_, lean_object* v_a_2545_, lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_){
_start:
{
lean_object* v_res_2549_; 
v_res_2549_ = l_Lake_Toml_key_parenthesizer(v_a_2544_, v_a_2545_, v_a_2546_, v_a_2547_);
lean_dec(v_a_2547_);
lean_dec_ref(v_a_2546_);
lean_dec(v_a_2545_);
lean_dec_ref(v_a_2544_);
return v_res_2549_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2550_; lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2550_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2551_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5);
v___x_2552_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1;
v___x_2553_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2553_, 0, v___x_2552_);
lean_closure_set(v___x_2553_, 1, v___x_2551_);
lean_closure_set(v___x_2553_, 2, v___x_2550_);
return v___x_2553_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer(lean_object* v_val_2554_, lean_object* v_a_2555_, lean_object* v_a_2556_, lean_object* v_a_2557_, lean_object* v_a_2558_){
_start:
{
lean_object* v___x_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; lean_object* v___x_2565_; lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; uint8_t v___x_2569_; lean_object* v___x_2570_; 
v___x_2560_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0));
v___x_2561_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1));
v___x_2562_ = lean_alloc_closure((void*)(l_Lake_Toml_key_parenthesizer___boxed), 5, 0);
v___x_2563_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2564_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0);
lean_inc_ref(v___x_2563_);
v___x_2565_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2565_, 0, v___x_2563_);
lean_closure_set(v___x_2565_, 1, v_val_2554_);
v___x_2566_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2566_, 0, v___x_2564_);
lean_closure_set(v___x_2566_, 1, v___x_2565_);
v___x_2567_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2567_, 0, v___x_2563_);
lean_closure_set(v___x_2567_, 1, v___x_2566_);
v___x_2568_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2568_, 0, v___x_2562_);
lean_closure_set(v___x_2568_, 1, v___x_2567_);
v___x_2569_ = 1;
v___x_2570_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2560_, v___x_2561_, v___x_2568_, v___x_2569_, v_a_2555_, v_a_2556_, v_a_2557_, v_a_2558_);
return v___x_2570_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___boxed(lean_object* v_val_2571_, lean_object* v_a_2572_, lean_object* v_a_2573_, lean_object* v_a_2574_, lean_object* v_a_2575_, lean_object* v_a_2576_){
_start:
{
lean_object* v_res_2577_; 
v_res_2577_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer(v_val_2571_, v_a_2572_, v_a_2573_, v_a_2574_, v_a_2575_);
lean_dec(v_a_2575_);
lean_dec_ref(v_a_2574_);
lean_dec(v_a_2573_);
lean_dec_ref(v_a_2572_);
return v_res_2577_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer___lam__0(lean_object* v___x_2578_, lean_object* v___x_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
lean_object* v___x_2585_; 
v___x_2585_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(v___x_2578_, v___x_2579_, v___y_2580_, v___y_2581_, v___y_2582_, v___y_2583_);
return v___x_2585_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer___lam__0___boxed(lean_object* v___x_2586_, lean_object* v___x_2587_, lean_object* v___y_2588_, lean_object* v___y_2589_, lean_object* v___y_2590_, lean_object* v___y_2591_, lean_object* v___y_2592_){
_start:
{
lean_object* v_res_2593_; 
v_res_2593_ = l_Lake_Toml_stdTable_parenthesizer___lam__0(v___x_2586_, v___x_2587_, v___y_2588_, v___y_2589_, v___y_2590_, v___y_2591_);
lean_dec(v___y_2591_);
lean_dec_ref(v___y_2590_);
lean_dec(v___y_2589_);
lean_dec_ref(v___y_2588_);
return v_res_2593_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2594_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2595_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__3));
v___x_2596_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
v___x_2597_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2597_, 0, v___x_2596_);
lean_closure_set(v___x_2597_, 1, v___x_2595_);
lean_closure_set(v___x_2597_, 2, v___x_2594_);
return v___x_2597_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v___x_2598_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2599_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__8, &l_Lake_Toml_stdTable___closed__8_once, _init_l_Lake_Toml_stdTable___closed__8);
v___x_2600_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
v___x_2601_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2601_, 0, v___x_2600_);
lean_closure_set(v___x_2601_, 1, v___x_2599_);
lean_closure_set(v___x_2601_, 2, v___x_2598_);
return v___x_2601_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; 
v___x_2602_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__1, &l_Lake_Toml_stdTable_parenthesizer___closed__1_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__1);
v___x_2603_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2603_, 0, v___x_2602_);
return v___x_2603_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___f_2606_; 
v___x_2604_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__2, &l_Lake_Toml_stdTable_parenthesizer___closed__2_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__2);
v___x_2605_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__0, &l_Lake_Toml_stdTable_parenthesizer___closed__0_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__0);
v___f_2606_ = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_parenthesizer___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2606_, 0, v___x_2605_);
lean_closure_set(v___f_2606_, 1, v___x_2604_);
return v___f_2606_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2607_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2608_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__17, &l_Lake_Toml_stdTable___closed__17_once, _init_l_Lake_Toml_stdTable___closed__17);
v___x_2609_ = l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1;
v___x_2610_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2610_, 0, v___x_2609_);
lean_closure_set(v___x_2610_, 1, v___x_2608_);
lean_closure_set(v___x_2610_, 2, v___x_2607_);
return v___x_2610_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__4, &l_Lake_Toml_stdTable_parenthesizer___closed__4_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__4);
v___x_2612_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2613_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2613_, 0, v___x_2612_);
lean_closure_set(v___x_2613_, 1, v___x_2611_);
return v___x_2613_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2614_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__5, &l_Lake_Toml_stdTable_parenthesizer___closed__5_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__5);
v___x_2615_ = lean_alloc_closure((void*)(l_Lake_Toml_key_parenthesizer___boxed), 5, 0);
v___x_2616_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2616_, 0, v___x_2615_);
lean_closure_set(v___x_2616_, 1, v___x_2614_);
return v___x_2616_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2617_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__6, &l_Lake_Toml_stdTable_parenthesizer___closed__6_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__6);
v___x_2618_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2619_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2619_, 0, v___x_2618_);
lean_closure_set(v___x_2619_, 1, v___x_2617_);
return v___x_2619_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_2620_; lean_object* v___f_2621_; lean_object* v___x_2622_; 
v___x_2620_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__7, &l_Lake_Toml_stdTable_parenthesizer___closed__7_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__7);
v___f_2621_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__3, &l_Lake_Toml_stdTable_parenthesizer___closed__3_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__3);
v___x_2622_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2622_, 0, v___f_2621_);
lean_closure_set(v___x_2622_, 1, v___x_2620_);
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer(lean_object* v_a_2623_, lean_object* v_a_2624_, lean_object* v_a_2625_, lean_object* v_a_2626_){
_start:
{
lean_object* v___x_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; uint8_t v___x_2631_; lean_object* v___x_2632_; 
v___x_2628_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__0));
v___x_2629_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__1));
v___x_2630_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__8, &l_Lake_Toml_stdTable_parenthesizer___closed__8_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__8);
v___x_2631_ = 0;
v___x_2632_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2628_, v___x_2629_, v___x_2630_, v___x_2631_, v_a_2623_, v_a_2624_, v_a_2625_, v_a_2626_);
return v___x_2632_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer___boxed(lean_object* v_a_2633_, lean_object* v_a_2634_, lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_){
_start:
{
lean_object* v_res_2638_; 
v_res_2638_ = l_Lake_Toml_stdTable_parenthesizer(v_a_2633_, v_a_2634_, v_a_2635_, v_a_2636_);
lean_dec(v_a_2636_);
lean_dec_ref(v_a_2635_);
lean_dec(v_a_2634_);
lean_dec_ref(v_a_2633_);
return v_res_2638_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___f_2641_; 
v___x_2639_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__1, &l_Lake_Toml_stdTable_parenthesizer___closed__1_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__1);
v___x_2640_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__0, &l_Lake_Toml_stdTable_parenthesizer___closed__0_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__0);
v___f_2641_ = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_parenthesizer___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2641_, 0, v___x_2640_);
lean_closure_set(v___f_2641_, 1, v___x_2639_);
return v___f_2641_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__4, &l_Lake_Toml_stdTable_parenthesizer___closed__4_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__4);
v___x_2643_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2643_, 0, v___x_2642_);
lean_closure_set(v___x_2643_, 1, v___x_2642_);
return v___x_2643_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2644_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__1, &l_Lake_Toml_arrayTable_parenthesizer___closed__1_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__1);
v___x_2645_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2646_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2646_, 0, v___x_2645_);
lean_closure_set(v___x_2646_, 1, v___x_2644_);
return v___x_2646_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; 
v___x_2647_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__2, &l_Lake_Toml_arrayTable_parenthesizer___closed__2_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__2);
v___x_2648_ = lean_alloc_closure((void*)(l_Lake_Toml_key_parenthesizer___boxed), 5, 0);
v___x_2649_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2649_, 0, v___x_2648_);
lean_closure_set(v___x_2649_, 1, v___x_2647_);
return v___x_2649_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2650_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__3, &l_Lake_Toml_arrayTable_parenthesizer___closed__3_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__3);
v___x_2651_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2652_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2652_, 0, v___x_2651_);
lean_closure_set(v___x_2652_, 1, v___x_2650_);
return v___x_2652_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_2653_; lean_object* v___f_2654_; lean_object* v___x_2655_; 
v___x_2653_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__4, &l_Lake_Toml_arrayTable_parenthesizer___closed__4_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__4);
v___f_2654_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__0, &l_Lake_Toml_arrayTable_parenthesizer___closed__0_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__0);
v___x_2655_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2655_, 0, v___f_2654_);
lean_closure_set(v___x_2655_, 1, v___x_2653_);
return v___x_2655_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_parenthesizer(lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_){
_start:
{
lean_object* v___x_2661_; lean_object* v___x_2662_; lean_object* v___x_2663_; uint8_t v___x_2664_; lean_object* v___x_2665_; 
v___x_2661_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__0));
v___x_2662_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__1));
v___x_2663_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__5, &l_Lake_Toml_arrayTable_parenthesizer___closed__5_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__5);
v___x_2664_ = 0;
v___x_2665_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2661_, v___x_2662_, v___x_2663_, v___x_2664_, v_a_2656_, v_a_2657_, v_a_2658_, v_a_2659_);
return v___x_2665_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_parenthesizer___boxed(lean_object* v_a_2666_, lean_object* v_a_2667_, lean_object* v_a_2668_, lean_object* v_a_2669_, lean_object* v_a_2670_){
_start:
{
lean_object* v_res_2671_; 
v_res_2671_ = l_Lake_Toml_arrayTable_parenthesizer(v_a_2666_, v_a_2667_, v_a_2668_, v_a_2669_);
lean_dec(v_a_2669_);
lean_dec_ref(v_a_2668_);
lean_dec(v_a_2667_);
lean_dec_ref(v_a_2666_);
return v_res_2671_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_table_parenthesizer(lean_object* v_a_2672_, lean_object* v_a_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_){
_start:
{
lean_object* v___x_2677_; lean_object* v___x_2678_; lean_object* v___x_2679_; 
v___x_2677_ = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_parenthesizer___boxed), 5, 0);
v___x_2678_ = lean_alloc_closure((void*)(l_Lake_Toml_arrayTable_parenthesizer___boxed), 5, 0);
v___x_2679_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___x_2677_, v___x_2678_, v_a_2672_, v_a_2673_, v_a_2674_, v_a_2675_);
return v___x_2679_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_table_parenthesizer___boxed(lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_Lake_Toml_table_parenthesizer(v_a_2680_, v_a_2681_, v_a_2682_, v_a_2683_);
lean_dec(v_a_2683_);
lean_dec_ref(v_a_2682_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer(lean_object* v_val_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_){
_start:
{
lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2698_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___closed__0));
v___x_2699_ = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2699_, 0, v_val_2692_);
v___x_2700_ = lean_alloc_closure((void*)(l_Lake_Toml_table_parenthesizer___boxed), 5, 0);
v___x_2701_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2701_, 0, v___x_2699_);
lean_closure_set(v___x_2701_, 1, v___x_2700_);
v___x_2702_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2698_, v___x_2701_, v_a_2693_, v_a_2694_, v_a_2695_, v_a_2696_);
return v___x_2702_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___boxed(lean_object* v_val_2703_, lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer(v_val_2703_, v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
lean_dec(v_a_2707_);
lean_dec_ref(v_a_2706_);
lean_dec(v_a_2705_);
lean_dec_ref(v_a_2704_);
return v_res_2709_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer___redArg(){
_start:
{
lean_object* v___x_2711_; 
v___x_2711_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_2711_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer___redArg___boxed(lean_object* v_a_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_Lake_Toml_trailingSep_parenthesizer___redArg();
return v_res_2713_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer(lean_object* v_a_2714_, lean_object* v_a_2715_, lean_object* v_a_2716_, lean_object* v_a_2717_){
_start:
{
lean_object* v___x_2719_; 
v___x_2719_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer___boxed(lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_){
_start:
{
lean_object* v_res_2725_; 
v_res_2725_ = l_Lake_Toml_trailingSep_parenthesizer(v_a_2720_, v_a_2721_, v_a_2722_, v_a_2723_);
lean_dec(v_a_2723_);
lean_dec_ref(v_a_2722_);
lean_dec(v_a_2721_);
lean_dec_ref(v_a_2720_);
return v_res_2725_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(lean_object* v_val_2726_, lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_){
_start:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; uint8_t v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; 
v___x_2732_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0));
v___x_2733_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1));
v___x_2734_ = lean_alloc_closure((void*)(l_Lake_Toml_header_parenthesizer___boxed), 5, 0);
v___x_2735_ = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2735_, 0, v_val_2726_);
v___x_2736_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingSep_parenthesizer___boxed), 5, 0);
v___x_2737_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2737_, 0, v___x_2735_);
lean_closure_set(v___x_2737_, 1, v___x_2736_);
v___x_2738_ = 1;
v___x_2739_ = lean_box(v___x_2738_);
v___x_2740_ = lean_alloc_closure((void*)(l_Lake_Toml_sepByLinebreak_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2740_, 0, v___x_2737_);
lean_closure_set(v___x_2740_, 1, v___x_2739_);
v___x_2741_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2741_, 0, v___x_2734_);
lean_closure_set(v___x_2741_, 1, v___x_2740_);
v___x_2742_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2732_, v___x_2733_, v___x_2741_, v___x_2738_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_);
return v___x_2742_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer___boxed(lean_object* v_val_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_, lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_){
_start:
{
lean_object* v_res_2749_; 
v_res_2749_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(v_val_2743_, v_a_2744_, v_a_2745_, v_a_2746_, v_a_2747_);
lean_dec(v_a_2747_);
lean_dec_ref(v_a_2746_);
lean_dec(v_a_2745_);
lean_dec_ref(v_a_2744_);
return v_res_2749_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_val_parenthesizer(lean_object* v_a_2750_, lean_object* v_a_2751_, lean_object* v_a_2752_, lean_object* v_a_2753_){
_start:
{
lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; uint8_t v___x_2758_; lean_object* v___x_2759_; 
v___x_2755_ = ((lean_object*)(l_Lake_Toml_val___closed__0));
v___x_2756_ = ((lean_object*)(l_Lake_Toml_val___closed__1));
v___x_2757_ = ((lean_object*)(l_Lake_Toml_val___closed__2));
v___x_2758_ = 1;
v___x_2759_ = l_Lake_Toml_recNodeWithAntiquot_parenthesizer(v___x_2755_, v___x_2756_, v___x_2757_, v___x_2758_, v_a_2750_, v_a_2751_, v_a_2752_, v_a_2753_);
return v___x_2759_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_val_parenthesizer___boxed(lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lake_Toml_val_parenthesizer(v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
lean_dec(v_a_2763_);
lean_dec_ref(v_a_2762_);
lean_dec(v_a_2761_);
lean_dec_ref(v_a_2760_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_toml_parenthesizer(lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_){
_start:
{
lean_object* v___x_2771_; lean_object* v___x_2772_; 
v___x_2771_ = lean_alloc_closure((void*)(l_Lake_Toml_val_parenthesizer___boxed), 5, 0);
v___x_2772_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(v___x_2771_, v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_toml_parenthesizer___boxed(lean_object* v_a_2773_, lean_object* v_a_2774_, lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_){
_start:
{
lean_object* v_res_2778_; 
v_res_2778_ = l_Lake_Toml_toml_parenthesizer(v_a_2773_, v_a_2774_, v_a_2775_, v_a_2776_);
lean_dec(v_a_2776_);
lean_dec_ref(v_a_2775_);
lean_dec(v_a_2774_);
lean_dec_ref(v_a_2773_);
return v_res_2778_;
}
}
static lean_object* _init_l_Lake_Toml_toml___closed__0(void){
_start:
{
lean_object* v___x_2779_; lean_object* v___x_2780_; 
v___x_2779_ = l_Lake_Toml_val;
v___x_2780_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore(v___x_2779_);
return v___x_2780_;
}
}
static lean_object* _init_l_Lake_Toml_toml___closed__1(void){
_start:
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; 
v___x_2781_ = lean_obj_once(&l_Lake_Toml_toml___closed__0, &l_Lake_Toml_toml___closed__0_once, _init_l_Lake_Toml_toml___closed__0);
v___x_2782_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1));
v___x_2783_ = l_Lean_Parser_withCache(v___x_2782_, v___x_2781_);
return v___x_2783_;
}
}
static lean_object* _init_l_Lake_Toml_toml(void){
_start:
{
lean_object* v___x_2784_; 
v___x_2784_ = lean_obj_once(&l_Lake_Toml_toml___closed__1, &l_Lake_Toml_toml___closed__1_once, _init_l_Lake_Toml_toml___closed__1);
return v___x_2784_;
}
}
lean_object* runtime_initialize_Lake_Toml_ParserUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter_Parenthesizer(uint8_t builtin);
void lean_initialize();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_Grammar(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize();
res = runtime_initialize_Lake_Toml_ParserUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_PrettyPrinter_Parenthesizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lake_Toml_trailingWs = _init_l_Lake_Toml_trailingWs();
lean_mark_persistent(l_Lake_Toml_trailingWs);
l_Lake_Toml_trailingSep = _init_l_Lake_Toml_trailingSep();
lean_mark_persistent(l_Lake_Toml_trailingSep);
l_Lake_Toml_unquotedKey = _init_l_Lake_Toml_unquotedKey();
lean_mark_persistent(l_Lake_Toml_unquotedKey);
l_Lake_Toml_basicString = _init_l_Lake_Toml_basicString();
lean_mark_persistent(l_Lake_Toml_basicString);
l_Lake_Toml_literalString = _init_l_Lake_Toml_literalString();
lean_mark_persistent(l_Lake_Toml_literalString);
l_Lake_Toml_mlBasicString = _init_l_Lake_Toml_mlBasicString();
lean_mark_persistent(l_Lake_Toml_mlBasicString);
l_Lake_Toml_mlLiteralString = _init_l_Lake_Toml_mlLiteralString();
lean_mark_persistent(l_Lake_Toml_mlLiteralString);
l_Lake_Toml_quotedKey = _init_l_Lake_Toml_quotedKey();
lean_mark_persistent(l_Lake_Toml_quotedKey);
l_Lake_Toml_simpleKey = _init_l_Lake_Toml_simpleKey();
lean_mark_persistent(l_Lake_Toml_simpleKey);
l_Lake_Toml_key = _init_l_Lake_Toml_key();
lean_mark_persistent(l_Lake_Toml_key);
l_Lake_Toml_stdTable = _init_l_Lake_Toml_stdTable();
lean_mark_persistent(l_Lake_Toml_stdTable);
l_Lake_Toml_arrayTable = _init_l_Lake_Toml_arrayTable();
lean_mark_persistent(l_Lake_Toml_arrayTable);
l_Lake_Toml_table = _init_l_Lake_Toml_table();
lean_mark_persistent(l_Lake_Toml_table);
l_Lake_Toml_header = _init_l_Lake_Toml_header();
lean_mark_persistent(l_Lake_Toml_header);
l_Lake_Toml_string = _init_l_Lake_Toml_string();
lean_mark_persistent(l_Lake_Toml_string);
l_Lake_Toml_true = _init_l_Lake_Toml_true();
lean_mark_persistent(l_Lake_Toml_true);
l_Lake_Toml_false = _init_l_Lake_Toml_false();
lean_mark_persistent(l_Lake_Toml_false);
l_Lake_Toml_boolean = _init_l_Lake_Toml_boolean();
lean_mark_persistent(l_Lake_Toml_boolean);
l_Lake_Toml_numeralAntiquot = _init_l_Lake_Toml_numeralAntiquot();
lean_mark_persistent(l_Lake_Toml_numeralAntiquot);
l_Lake_Toml_numeral = _init_l_Lake_Toml_numeral();
lean_mark_persistent(l_Lake_Toml_numeral);
l_Lake_Toml_float = _init_l_Lake_Toml_float();
lean_mark_persistent(l_Lake_Toml_float);
l_Lake_Toml_decInt = _init_l_Lake_Toml_decInt();
lean_mark_persistent(l_Lake_Toml_decInt);
l_Lake_Toml_binNum = _init_l_Lake_Toml_binNum();
lean_mark_persistent(l_Lake_Toml_binNum);
l_Lake_Toml_octNum = _init_l_Lake_Toml_octNum();
lean_mark_persistent(l_Lake_Toml_octNum);
l_Lake_Toml_hexNum = _init_l_Lake_Toml_hexNum();
lean_mark_persistent(l_Lake_Toml_hexNum);
l_Lake_Toml_dateTime = _init_l_Lake_Toml_dateTime();
lean_mark_persistent(l_Lake_Toml_dateTime);
l_Lake_Toml_val = _init_l_Lake_Toml_val();
lean_mark_persistent(l_Lake_Toml_val);
l_Lake_Toml_array = _init_l_Lake_Toml_array();
lean_mark_persistent(l_Lake_Toml_array);
l_Lake_Toml_inlineTable = _init_l_Lake_Toml_inlineTable();
lean_mark_persistent(l_Lake_Toml_inlineTable);
l_Lake_Toml_keyval = _init_l_Lake_Toml_keyval();
lean_mark_persistent(l_Lake_Toml_keyval);
l_Lake_Toml_expression = _init_l_Lake_Toml_expression();
lean_mark_persistent(l_Lake_Toml_expression);
l_Lake_Toml_key_formatter___closed__0___boxed__const__1 = _init_l_Lake_Toml_key_formatter___closed__0___boxed__const__1();
lean_mark_persistent(l_Lake_Toml_key_formatter___closed__0___boxed__const__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1);
l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1 = _init_l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1();
lean_mark_persistent(l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1);
l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1 = _init_l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1();
lean_mark_persistent(l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1);
l_Lake_Toml_toml = _init_l_Lake_Toml_toml();
lean_mark_persistent(l_Lake_Toml_toml);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lake_Toml_Grammar(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lake_Toml_ParserUtil(uint8_t builtin);
lean_object* initialize_Lean_Parser(uint8_t builtin);
lean_object* initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin);
lean_object* initialize_Lean_PrettyPrinter_Parenthesizer(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Grammar(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lake_Toml_ParserUtil(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Formatter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_PrettyPrinter_Parenthesizer(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lake_Toml_Grammar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lake_Toml_Grammar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lake_Toml_Grammar(builtin);
}
#ifdef __cplusplus
}
#endif
