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
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_Lean_Parser_takeWhileFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_trailing(lean_object*);
lean_object* l_Lake_Toml_skipFn___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Toml_chAtom(uint32_t, lean_object*, lean_object*);
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
lean_object* l_Lake_Toml_chFn(uint32_t, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Parser_instBEqError_beq(lean_object*, lean_object*);
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_mkUnexpectedCharError(lean_object*, uint32_t, lean_object*, uint8_t);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_litWithAntiquot(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Parser_hexDigitFn(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_Lake_Toml_takeWhile1Fn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_atomicFn(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Parser_setExpected(lean_object*, lean_object*);
lean_object* l_Lake_Toml_strFn(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_lit(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_pushLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
lean_object* l_Lake_Toml_sepByChar1Fn(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_sepByChar1AuxFn(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_push(lean_object*, uint32_t);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lake_Toml_digitPairFn(lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Parser_notFollowedBy(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0___boxed(lean_object*, lean_object*);
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
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "':'"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3_value;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "minute digit"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5_value;
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
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "'-'"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3_value;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "day digit"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5_value;
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
static const lean_string_object l_Lake_Toml_numeralFn___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__3 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__3_value;
static const lean_string_object l_Lake_Toml_numeralFn___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__4 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__4_value;
static const lean_closure_object l_Lake_Toml_numeralFn___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_isHexDigit___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__5 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__5_value;
static const lean_string_object l_Lake_Toml_numeralFn___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "hexadecimal integer"};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__6 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__6_value;
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__7 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__7_value;
static const lean_string_object l_Lake_Toml_numeralFn___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "hexNum"};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__8 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__8_value;
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__9_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__9_value_aux_1),((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__8_value),LEAN_SCALAR_PTR_LITERAL(93, 174, 95, 211, 123, 63, 171, 252)}};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__9 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__9_value;
static const lean_closure_object l_Lake_Toml_numeralFn___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_isOctDigit___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__10 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__10_value;
static const lean_string_object l_Lake_Toml_numeralFn___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "octal integer"};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__11 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__11_value;
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__12 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__12_value;
static const lean_string_object l_Lake_Toml_numeralFn___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "octNum"};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__13 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__13_value;
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__14_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__14_value_aux_1),((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__13_value),LEAN_SCALAR_PTR_LITERAL(93, 70, 221, 168, 145, 119, 144, 197)}};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__14 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__14_value;
static const lean_closure_object l_Lake_Toml_numeralFn___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lake_Toml_isBinDigit___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__15 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__15_value;
static const lean_string_object l_Lake_Toml_numeralFn___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "binary integer"};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__16 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__16_value;
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__16_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__17 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__17_value;
static const lean_string_object l_Lake_Toml_numeralFn___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "binNum"};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__18 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__18_value;
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0_value),LEAN_SCALAR_PTR_LITERAL(111, 69, 182, 10, 108, 181, 149, 180)}};
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__19_value_aux_0),((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1_value),LEAN_SCALAR_PTR_LITERAL(162, 254, 21, 174, 177, 224, 84, 229)}};
static const lean_ctor_object l_Lake_Toml_numeralFn___lam__0___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__19_value_aux_1),((lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__18_value),LEAN_SCALAR_PTR_LITERAL(59, 60, 170, 39, 77, 137, 193, 6)}};
static const lean_object* l_Lake_Toml_numeralFn___lam__0___closed__19 = (const lean_object*)&l_Lake_Toml_numeralFn___lam__0___closed__19_value;
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
static const lean_string_object l_Lake_Toml_key___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "'.'"};
static const lean_object* l_Lake_Toml_key___closed__4 = (const lean_object*)&l_Lake_Toml_key___closed__4_value;
static const lean_ctor_object l_Lake_Toml_key___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_key___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_key___closed__5 = (const lean_object*)&l_Lake_Toml_key___closed__5_value;
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
static const lean_string_object l_Lake_Toml_stdTable___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "'['"};
static const lean_object* l_Lake_Toml_stdTable___closed__5 = (const lean_object*)&l_Lake_Toml_stdTable___closed__5_value;
static const lean_ctor_object l_Lake_Toml_stdTable___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_stdTable___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_stdTable___closed__6 = (const lean_object*)&l_Lake_Toml_stdTable___closed__6_value;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__7;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__8;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__9;
static lean_once_cell_t l_Lake_Toml_stdTable___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lake_Toml_stdTable___closed__10;
static const lean_string_object l_Lake_Toml_stdTable___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "']'"};
static const lean_object* l_Lake_Toml_stdTable___closed__11 = (const lean_object*)&l_Lake_Toml_stdTable___closed__11_value;
static const lean_ctor_object l_Lake_Toml_stdTable___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lake_Toml_stdTable___closed__11_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lake_Toml_stdTable___closed__12 = (const lean_object*)&l_Lake_Toml_stdTable___closed__12_value;
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
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "'='"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3_value;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4;
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
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "','"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7_value;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8;
static const lean_string_object l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "'}'"};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9_value;
static const lean_ctor_object l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10 = (const lean_object*)&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10_value;
static lean_once_cell_t l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11;
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
uint8_t l_Lake_Toml_isControlChar(uint32_t v_c_1_){
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
LEAN_EXPORT void l_Lake_Toml_isControlChar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_1_ = stack[0].m_num;
uint8_t v_res_8_;
v_res_8_ = l_Lake_Toml_isControlChar(v_c_1_);
stack->m_num = v_res_8_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_isControlChar___boxed(lean_object* v_c_9_){
_start:
{
uint32_t v_c_boxed_10_; uint8_t v_res_11_; lean_object* v_r_12_; 
v_c_boxed_10_ = lean_unbox_uint32(v_c_9_);
lean_dec(v_c_9_);
v_res_11_ = l_Lake_Toml_isControlChar(v_c_boxed_10_);
v_r_12_ = lean_box(v_res_11_);
return v_r_12_;
}
}
uint8_t l_Lake_Toml_wsFn___lam__0(uint32_t v_c_13_){
_start:
{
uint32_t v___x_14_; uint8_t v___x_15_; 
v___x_14_ = 32;
v___x_15_ = lean_uint32_dec_eq(v_c_13_, v___x_14_);
if (v___x_15_ == 0)
{
uint32_t v___x_16_; uint8_t v___x_17_; 
v___x_16_ = 9;
v___x_17_ = lean_uint32_dec_eq(v_c_13_, v___x_16_);
return v___x_17_;
}
else
{
return v___x_15_;
}
}
}
LEAN_EXPORT void l_Lake_Toml_wsFn___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_13_ = stack[0].m_num;
uint8_t v_res_18_;
v_res_18_ = l_Lake_Toml_wsFn___lam__0(v_c_13_);
stack->m_num = v_res_18_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_wsFn___lam__0___boxed(lean_object* v_c_19_){
_start:
{
uint32_t v_c_boxed_20_; uint8_t v_res_21_; lean_object* v_r_22_; 
v_c_boxed_20_ = lean_unbox_uint32(v_c_19_);
lean_dec(v_c_19_);
v_res_21_ = l_Lake_Toml_wsFn___lam__0(v_c_boxed_20_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_wsFn(lean_object* v_a_24_, lean_object* v_a_25_){
_start:
{
lean_object* v___f_26_; lean_object* v___x_27_; 
v___f_26_ = ((lean_object*)(l_Lake_Toml_wsFn___closed__0));
v___x_27_ = l_Lean_Parser_takeWhileFn(v___f_26_, v_a_24_, v_a_25_);
return v___x_27_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_wsFn___boxed(lean_object* v_a_28_, lean_object* v_a_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_Lake_Toml_wsFn(v_a_28_, v_a_29_);
lean_dec_ref(v_a_28_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(lean_object* v_c_32_, lean_object* v_s_33_){
_start:
{
lean_object* v_toInputContext_34_; lean_object* v_pos_35_; lean_object* v_errMsg_36_; uint8_t v___x_37_; uint8_t v___x_38_; 
v_toInputContext_34_ = lean_ctor_get(v_c_32_, 0);
v_pos_35_ = lean_ctor_get(v_s_33_, 2);
v_errMsg_36_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___closed__0));
v___x_37_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_34_, v_pos_35_);
v___x_38_ = 1;
if (v___x_37_ == 0)
{
lean_object* v_inputString_39_; uint32_t v_curr_40_; uint32_t v___x_41_; uint8_t v___x_42_; 
v_inputString_39_ = lean_ctor_get(v_toInputContext_34_, 0);
v_curr_40_ = lean_string_utf8_get_fast(v_inputString_39_, v_pos_35_);
v___x_41_ = 10;
v___x_42_ = lean_uint32_dec_eq(v_curr_40_, v___x_41_);
if (v___x_42_ == 0)
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_box(0);
v___x_44_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_33_, v_errMsg_36_, v___x_43_, v___x_38_);
return v___x_44_;
}
else
{
lean_object* v___x_45_; 
lean_inc(v_pos_35_);
v___x_45_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_33_, v_c_32_, v_pos_35_);
lean_dec(v_pos_35_);
return v___x_45_;
}
}
else
{
lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_46_ = lean_box(0);
v___x_47_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_33_, v_errMsg_36_, v___x_46_, v___x_38_);
return v___x_47_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___boxed(lean_object* v_c_48_, lean_object* v_s_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_48_, v_s_49_);
lean_dec_ref(v_c_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_newlineFn(lean_object* v_c_55_, lean_object* v_s_56_){
_start:
{
lean_object* v_toInputContext_57_; lean_object* v_pos_58_; uint8_t v___x_59_; 
v_toInputContext_57_ = lean_ctor_get(v_c_55_, 0);
v_pos_58_ = lean_ctor_get(v_s_56_, 2);
v___x_59_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_57_, v_pos_58_);
if (v___x_59_ == 0)
{
lean_object* v_inputString_60_; uint32_t v_curr_61_; uint32_t v___x_62_; uint8_t v___x_63_; 
v_inputString_60_ = lean_ctor_get(v_toInputContext_57_, 0);
v_curr_61_ = lean_string_utf8_get_fast(v_inputString_60_, v_pos_58_);
v___x_62_ = 10;
v___x_63_ = lean_uint32_dec_eq(v_curr_61_, v___x_62_);
if (v___x_63_ == 0)
{
uint32_t v___x_64_; uint8_t v___x_65_; 
v___x_64_ = 13;
v___x_65_ = lean_uint32_dec_eq(v_curr_61_, v___x_64_);
if (v___x_65_ == 0)
{
uint8_t v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v___x_66_ = 1;
v___x_67_ = ((lean_object*)(l_Lake_Toml_newlineFn___closed__1));
v___x_68_ = l_Lake_Toml_mkUnexpectedCharError(v_s_56_, v_curr_61_, v___x_67_, v___x_66_);
return v___x_68_;
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; 
lean_inc(v_pos_58_);
v___x_69_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_56_, v_c_55_, v_pos_58_);
lean_dec(v_pos_58_);
v___x_70_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_55_, v___x_69_);
return v___x_70_;
}
}
else
{
lean_object* v___x_71_; 
lean_inc(v_pos_58_);
v___x_71_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_56_, v_c_55_, v_pos_58_);
lean_dec(v_pos_58_);
return v___x_71_;
}
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = ((lean_object*)(l_Lake_Toml_newlineFn___closed__1));
v___x_73_ = l_Lean_Parser_ParserState_mkEOIError(v_s_56_, v___x_72_);
return v___x_73_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_newlineFn___boxed(lean_object* v_c_74_, lean_object* v_s_75_){
_start:
{
lean_object* v_res_76_; 
v_res_76_ = l_Lake_Toml_newlineFn(v_c_74_, v_s_75_);
lean_dec_ref(v_c_74_);
return v_res_76_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(lean_object* v_a_78_, lean_object* v_a_79_){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; 
v___x_80_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___closed__0));
v___x_81_ = l_Lean_Parser_takeUntilFn(v___x_80_, v_a_78_, v_a_79_);
return v___x_81_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___boxed(lean_object* v_a_82_, lean_object* v_a_83_){
_start:
{
lean_object* v_res_84_; 
v_res_84_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(v_a_82_, v_a_83_);
lean_dec_ref(v_a_82_);
return v_res_84_;
}
}
uint8_t l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(lean_object* v_x_85_, lean_object* v_x_86_){
_start:
{
if (lean_obj_tag(v_x_85_) == 0)
{
if (lean_obj_tag(v_x_86_) == 0)
{
uint8_t v___x_87_; 
v___x_87_ = 1;
return v___x_87_;
}
else
{
uint8_t v___x_88_; 
v___x_88_ = 0;
return v___x_88_;
}
}
else
{
if (lean_obj_tag(v_x_86_) == 0)
{
uint8_t v___x_89_; 
v___x_89_ = 0;
return v___x_89_;
}
else
{
lean_object* v_val_90_; lean_object* v_val_91_; uint8_t v___x_92_; 
v_val_90_ = lean_ctor_get(v_x_85_, 0);
v_val_91_ = lean_ctor_get(v_x_86_, 0);
v___x_92_ = l_Lean_Parser_instBEqError_beq(v_val_90_, v_val_91_);
return v___x_92_;
}
}
}
}
LEAN_EXPORT void l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_85_ = stack[0].m_obj;
lean_object* v_x_86_ = stack[1].m_obj;
uint8_t v_res_93_;
v_res_93_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_x_85_, v_x_86_);
stack->m_num = v_res_93_;
}
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0___boxed(lean_object* v_x_94_, lean_object* v_x_95_){
_start:
{
uint8_t v_res_96_; lean_object* v_r_97_; 
v_res_96_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_x_94_, v_x_95_);
lean_dec(v_x_95_);
lean_dec(v_x_94_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_commentFn(lean_object* v_a_102_, lean_object* v_a_103_){
_start:
{
uint32_t v___x_104_; lean_object* v___x_105_; lean_object* v_s_106_; lean_object* v_errorMsg_107_; lean_object* v___x_108_; uint8_t v___x_109_; 
v___x_104_ = 35;
v___x_105_ = ((lean_object*)(l_Lake_Toml_commentFn___closed__1));
v_s_106_ = l_Lake_Toml_chFn(v___x_104_, v___x_105_, v_a_102_, v_a_103_);
v_errorMsg_107_ = lean_ctor_get(v_s_106_, 4);
v___x_108_ = lean_box(0);
v___x_109_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_107_, v___x_108_);
if (v___x_109_ == 0)
{
return v_s_106_;
}
else
{
lean_object* v___x_110_; 
v___x_110_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(v_a_102_, v_s_106_);
return v___x_110_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_commentFn___boxed(lean_object* v_a_111_, lean_object* v_a_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_Lake_Toml_commentFn(v_a_111_, v_a_112_);
lean_dec_ref(v_a_111_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_wsNewlineFn(lean_object* v_c_114_, lean_object* v_s_115_){
_start:
{
lean_object* v_toInputContext_116_; lean_object* v_pos_117_; uint8_t v___x_121_; 
v_toInputContext_116_ = lean_ctor_get(v_c_114_, 0);
v_pos_117_ = lean_ctor_get(v_s_115_, 2);
v___x_121_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_116_, v_pos_117_);
if (v___x_121_ == 0)
{
lean_object* v_inputString_122_; uint32_t v_curr_123_; uint32_t v___x_124_; uint8_t v___x_125_; 
v_inputString_122_ = lean_ctor_get(v_toInputContext_116_, 0);
v_curr_123_ = lean_string_utf8_get_fast(v_inputString_122_, v_pos_117_);
v___x_124_ = 32;
v___x_125_ = lean_uint32_dec_eq(v_curr_123_, v___x_124_);
if (v___x_125_ == 0)
{
uint32_t v___x_126_; uint8_t v___x_127_; 
v___x_126_ = 9;
v___x_127_ = lean_uint32_dec_eq(v_curr_123_, v___x_126_);
if (v___x_127_ == 0)
{
uint32_t v___x_128_; uint8_t v___x_129_; 
v___x_128_ = 10;
v___x_129_ = lean_uint32_dec_eq(v_curr_123_, v___x_128_);
if (v___x_129_ == 0)
{
uint32_t v___x_130_; uint8_t v___x_131_; 
v___x_130_ = 13;
v___x_131_ = lean_uint32_dec_eq(v_curr_123_, v___x_130_);
if (v___x_131_ == 0)
{
return v_s_115_;
}
else
{
lean_object* v___x_132_; lean_object* v_s_133_; lean_object* v_errorMsg_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
lean_inc(v_pos_117_);
v___x_132_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_115_, v_c_114_, v_pos_117_);
lean_dec(v_pos_117_);
v_s_133_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_114_, v___x_132_);
v_errorMsg_134_ = lean_ctor_get(v_s_133_, 4);
v___x_135_ = lean_box(0);
v___x_136_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_134_, v___x_135_);
if (v___x_136_ == 0)
{
return v_s_133_;
}
else
{
v_s_115_ = v_s_133_;
goto _start;
}
}
}
else
{
lean_inc(v_pos_117_);
goto v___jp_118_;
}
}
else
{
lean_inc(v_pos_117_);
goto v___jp_118_;
}
}
else
{
lean_inc(v_pos_117_);
goto v___jp_118_;
}
}
else
{
return v_s_115_;
}
v___jp_118_:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_115_, v_c_114_, v_pos_117_);
lean_dec(v_pos_117_);
v_s_115_ = v___x_119_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_wsNewlineFn___boxed(lean_object* v_c_138_, lean_object* v_s_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lake_Toml_wsNewlineFn(v_c_138_, v_s_139_);
lean_dec_ref(v_c_138_);
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingFn(lean_object* v_c_141_, lean_object* v_s_142_){
_start:
{
lean_object* v_toInputContext_143_; lean_object* v_pos_144_; uint8_t v___x_148_; 
v_toInputContext_143_ = lean_ctor_get(v_c_141_, 0);
v_pos_144_ = lean_ctor_get(v_s_142_, 2);
v___x_148_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_143_, v_pos_144_);
if (v___x_148_ == 0)
{
lean_object* v_inputString_149_; uint32_t v_curr_150_; uint32_t v___x_151_; uint8_t v___x_152_; 
v_inputString_149_ = lean_ctor_get(v_toInputContext_143_, 0);
v_curr_150_ = lean_string_utf8_get_fast(v_inputString_149_, v_pos_144_);
v___x_151_ = 32;
v___x_152_ = lean_uint32_dec_eq(v_curr_150_, v___x_151_);
if (v___x_152_ == 0)
{
uint32_t v___x_153_; uint8_t v___x_154_; 
v___x_153_ = 9;
v___x_154_ = lean_uint32_dec_eq(v_curr_150_, v___x_153_);
if (v___x_154_ == 0)
{
uint32_t v___x_155_; uint8_t v___x_156_; 
v___x_155_ = 10;
v___x_156_ = lean_uint32_dec_eq(v_curr_150_, v___x_155_);
if (v___x_156_ == 0)
{
uint32_t v___x_157_; uint8_t v___x_158_; 
v___x_157_ = 13;
v___x_158_ = lean_uint32_dec_eq(v_curr_150_, v___x_157_);
if (v___x_158_ == 0)
{
uint32_t v___x_159_; uint8_t v___x_160_; 
v___x_159_ = 35;
v___x_160_ = lean_uint32_dec_eq(v_curr_150_, v___x_159_);
if (v___x_160_ == 0)
{
return v_s_142_;
}
else
{
lean_object* v___x_161_; lean_object* v_s_162_; lean_object* v_errorMsg_163_; lean_object* v___x_164_; uint8_t v___x_165_; 
lean_inc(v_pos_144_);
v___x_161_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_142_, v_c_141_, v_pos_144_);
lean_dec(v_pos_144_);
v_s_162_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(v_c_141_, v___x_161_);
v_errorMsg_163_ = lean_ctor_get(v_s_162_, 4);
v___x_164_ = lean_box(0);
v___x_165_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_163_, v___x_164_);
if (v___x_165_ == 0)
{
return v_s_162_;
}
else
{
v_s_142_ = v_s_162_;
goto _start;
}
}
}
else
{
lean_object* v___x_167_; lean_object* v_s_168_; lean_object* v_errorMsg_169_; lean_object* v___x_170_; uint8_t v___x_171_; 
lean_inc(v_pos_144_);
v___x_167_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_142_, v_c_141_, v_pos_144_);
lean_dec(v_pos_144_);
v_s_168_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_141_, v___x_167_);
v_errorMsg_169_ = lean_ctor_get(v_s_168_, 4);
v___x_170_ = lean_box(0);
v___x_171_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_169_, v___x_170_);
if (v___x_171_ == 0)
{
return v_s_168_;
}
else
{
v_s_142_ = v_s_168_;
goto _start;
}
}
}
else
{
lean_inc(v_pos_144_);
goto v___jp_145_;
}
}
else
{
lean_inc(v_pos_144_);
goto v___jp_145_;
}
}
else
{
lean_inc(v_pos_144_);
goto v___jp_145_;
}
}
else
{
return v_s_142_;
}
v___jp_145_:
{
lean_object* v___x_146_; 
v___x_146_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_142_, v_c_141_, v_pos_144_);
lean_dec(v_pos_144_);
v_s_142_ = v___x_146_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingFn___boxed(lean_object* v_c_173_, lean_object* v_s_174_){
_start:
{
lean_object* v_res_175_; 
v_res_175_ = l_Lake_Toml_trailingFn(v_c_173_, v_s_174_);
lean_dec_ref(v_c_173_);
return v_res_175_;
}
}
uint8_t l_Lake_Toml_isEscapeChar(uint32_t v_c_176_){
_start:
{
uint32_t v___x_177_; uint8_t v___x_178_; 
v___x_177_ = 98;
v___x_178_ = lean_uint32_dec_eq(v_c_176_, v___x_177_);
if (v___x_178_ == 0)
{
uint32_t v___x_179_; uint8_t v___x_180_; 
v___x_179_ = 116;
v___x_180_ = lean_uint32_dec_eq(v_c_176_, v___x_179_);
if (v___x_180_ == 0)
{
uint32_t v___x_181_; uint8_t v___x_182_; 
v___x_181_ = 110;
v___x_182_ = lean_uint32_dec_eq(v_c_176_, v___x_181_);
if (v___x_182_ == 0)
{
uint32_t v___x_183_; uint8_t v___x_184_; 
v___x_183_ = 102;
v___x_184_ = lean_uint32_dec_eq(v_c_176_, v___x_183_);
if (v___x_184_ == 0)
{
uint32_t v___x_185_; uint8_t v___x_186_; 
v___x_185_ = 114;
v___x_186_ = lean_uint32_dec_eq(v_c_176_, v___x_185_);
if (v___x_186_ == 0)
{
uint32_t v___x_187_; uint8_t v___x_188_; 
v___x_187_ = 34;
v___x_188_ = lean_uint32_dec_eq(v_c_176_, v___x_187_);
if (v___x_188_ == 0)
{
uint32_t v___x_189_; uint8_t v___x_190_; 
v___x_189_ = 92;
v___x_190_ = lean_uint32_dec_eq(v_c_176_, v___x_189_);
return v___x_190_;
}
else
{
return v___x_188_;
}
}
else
{
return v___x_186_;
}
}
else
{
return v___x_184_;
}
}
else
{
return v___x_182_;
}
}
else
{
return v___x_180_;
}
}
else
{
return v___x_178_;
}
}
}
LEAN_EXPORT void l_Lake_Toml_isEscapeChar_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_176_ = stack[0].m_num;
uint8_t v_res_191_;
v_res_191_ = l_Lake_Toml_isEscapeChar(v_c_176_);
stack->m_num = v_res_191_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_isEscapeChar___boxed(lean_object* v_c_192_){
_start:
{
uint32_t v_c_boxed_193_; uint8_t v_res_194_; lean_object* v_r_195_; 
v_c_boxed_193_ = lean_unbox_uint32(v_c_192_);
lean_dec(v_c_192_);
v_res_194_ = l_Lake_Toml_isEscapeChar(v_c_boxed_193_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0(lean_object* v___y_196_, lean_object* v___y_197_){
_start:
{
lean_object* v_s_198_; lean_object* v_errorMsg_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v_s_198_ = l_Lake_Toml_wsFn(v___y_196_, v___y_197_);
v_errorMsg_199_ = lean_ctor_get(v_s_198_, 4);
v___x_200_ = lean_box(0);
v___x_201_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_199_, v___x_200_);
if (v___x_201_ == 0)
{
return v_s_198_;
}
else
{
lean_object* v_s_202_; lean_object* v_errorMsg_203_; uint8_t v___x_204_; 
v_s_202_ = l_Lake_Toml_newlineFn(v___y_196_, v_s_198_);
v_errorMsg_203_ = lean_ctor_get(v_s_202_, 4);
v___x_204_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_203_, v___x_200_);
if (v___x_204_ == 0)
{
return v_s_202_;
}
else
{
lean_object* v___x_205_; 
v___x_205_ = l_Lake_Toml_wsNewlineFn(v___y_196_, v_s_202_);
return v___x_205_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0___boxed(lean_object* v___y_206_, lean_object* v___y_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0(v___y_206_, v___y_207_);
lean_dec_ref(v___y_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1(lean_object* v___y_209_, lean_object* v___y_210_){
_start:
{
lean_object* v_s_211_; lean_object* v_errorMsg_212_; lean_object* v___x_213_; uint8_t v___x_214_; 
v_s_211_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v___y_209_, v___y_210_);
v_errorMsg_212_ = lean_ctor_get(v_s_211_, 4);
v___x_213_ = lean_box(0);
v___x_214_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_212_, v___x_213_);
if (v___x_214_ == 0)
{
return v_s_211_;
}
else
{
lean_object* v___x_215_; 
v___x_215_ = l_Lake_Toml_wsNewlineFn(v___y_209_, v_s_211_);
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1___boxed(lean_object* v___y_216_, lean_object* v___y_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1(v___y_216_, v___y_217_);
lean_dec_ref(v___y_216_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(lean_object* v_c_219_, lean_object* v_x_220_, lean_object* v_x_221_){
_start:
{
lean_object* v_zero_222_; uint8_t v_isZero_223_; 
v_zero_222_ = lean_unsigned_to_nat(0u);
v_isZero_223_ = lean_nat_dec_eq(v_x_220_, v_zero_222_);
if (v_isZero_223_ == 1)
{
lean_dec(v_x_220_);
return v_x_221_;
}
else
{
lean_object* v_s_224_; lean_object* v_errorMsg_225_; lean_object* v___x_226_; uint8_t v___x_227_; 
v_s_224_ = l_Lean_Parser_hexDigitFn(v_c_219_, v_x_221_);
v_errorMsg_225_ = lean_ctor_get(v_s_224_, 4);
v___x_226_ = lean_box(0);
v___x_227_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_225_, v___x_226_);
if (v___x_227_ == 0)
{
lean_dec(v_x_220_);
return v_s_224_;
}
else
{
lean_object* v_one_228_; lean_object* v_n_229_; 
v_one_228_ = lean_unsigned_to_nat(1u);
v_n_229_ = lean_nat_sub(v_x_220_, v_one_228_);
lean_dec(v_x_220_);
v_x_220_ = v_n_229_;
v_x_221_ = v_s_224_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0___boxed(lean_object* v_c_231_, lean_object* v_x_232_, lean_object* v_x_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(v_c_231_, v_x_232_, v_x_233_);
lean_dec_ref(v_c_231_);
return v_res_234_;
}
}
lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(uint8_t v_stringGap_244_, lean_object* v_c_245_, lean_object* v_s_246_){
_start:
{
lean_object* v_toInputContext_247_; lean_object* v_pos_248_; lean_object* v___x_249_; lean_object* v_expected_250_; uint8_t v___x_251_; 
v_toInputContext_247_ = lean_ctor_get(v_c_245_, 0);
v_pos_248_ = lean_ctor_get(v_s_246_, 2);
v___x_249_ = lean_box(0);
v_expected_250_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__1));
v___x_251_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_247_, v_pos_248_);
if (v___x_251_ == 0)
{
lean_object* v_inputString_252_; uint32_t v_curr_253_; uint8_t v___x_254_; 
v_inputString_252_ = lean_ctor_get(v_toInputContext_247_, 0);
v_curr_253_ = lean_string_utf8_get_fast(v_inputString_252_, v_pos_248_);
v___x_254_ = l_Lake_Toml_isEscapeChar(v_curr_253_);
if (v___x_254_ == 0)
{
uint32_t v___x_255_; uint8_t v___x_256_; 
v___x_255_ = 117;
v___x_256_ = lean_uint32_dec_eq(v_curr_253_, v___x_255_);
if (v___x_256_ == 0)
{
uint32_t v___x_257_; uint8_t v___x_258_; 
v___x_257_ = 85;
v___x_258_ = lean_uint32_dec_eq(v_curr_253_, v___x_257_);
if (v___x_258_ == 0)
{
lean_object* v___f_259_; uint8_t v___x_260_; lean_object* v_p_262_; uint32_t v___x_267_; uint8_t v___x_268_; 
v___f_259_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__2));
v___x_260_ = 1;
v___x_267_ = 32;
v___x_268_ = lean_uint32_dec_eq(v_curr_253_, v___x_267_);
if (v___x_268_ == 0)
{
uint32_t v___x_269_; uint8_t v___x_270_; 
v___x_269_ = 9;
v___x_270_ = lean_uint32_dec_eq(v_curr_253_, v___x_269_);
if (v___x_270_ == 0)
{
uint32_t v___x_271_; uint8_t v___x_272_; 
v___x_271_ = 10;
v___x_272_ = lean_uint32_dec_eq(v_curr_253_, v___x_271_);
if (v___x_272_ == 0)
{
uint32_t v___x_273_; uint8_t v___x_274_; 
v___x_273_ = 13;
v___x_274_ = lean_uint32_dec_eq(v_curr_253_, v___x_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; 
lean_dec_ref(v_c_245_);
v___x_275_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__4));
v___x_276_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_246_, v___x_275_, v___x_249_, v___x_260_);
return v___x_276_;
}
else
{
lean_object* v___f_277_; 
v___f_277_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__5));
v_p_262_ = v___f_277_;
goto v___jp_261_;
}
}
else
{
lean_object* v___x_278_; 
v___x_278_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__6));
v_p_262_ = v___x_278_;
goto v___jp_261_;
}
}
else
{
v_p_262_ = v___f_259_;
goto v___jp_261_;
}
}
else
{
v_p_262_ = v___f_259_;
goto v___jp_261_;
}
v___jp_261_:
{
if (v_stringGap_244_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec_ref(v_c_245_);
v___x_263_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__3));
v___x_264_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_246_, v___x_263_, v_expected_250_, v___x_260_);
return v___x_264_;
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_inc(v_pos_248_);
v___x_265_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_246_, v_c_245_, v_pos_248_);
lean_dec(v_pos_248_);
lean_inc_ref(v_p_262_);
v___x_266_ = lean_apply_2(v_p_262_, v_c_245_, v___x_265_);
return v___x_266_;
}
}
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
lean_inc(v_pos_248_);
v___x_279_ = lean_unsigned_to_nat(8u);
v___x_280_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_246_, v_c_245_, v_pos_248_);
lean_dec(v_pos_248_);
v___x_281_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(v_c_245_, v___x_279_, v___x_280_);
lean_dec_ref(v_c_245_);
return v___x_281_;
}
}
else
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
lean_inc(v_pos_248_);
v___x_282_ = lean_unsigned_to_nat(4u);
v___x_283_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_246_, v_c_245_, v_pos_248_);
lean_dec(v_pos_248_);
v___x_284_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(v_c_245_, v___x_282_, v___x_283_);
lean_dec_ref(v_c_245_);
return v___x_284_;
}
}
else
{
lean_object* v___x_285_; 
lean_inc(v_pos_248_);
v___x_285_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_246_, v_c_245_, v_pos_248_);
lean_dec(v_pos_248_);
lean_dec_ref(v_c_245_);
return v___x_285_;
}
}
else
{
lean_object* v___x_286_; 
lean_dec_ref(v_c_245_);
v___x_286_ = l_Lean_Parser_ParserState_mkEOIError(v_s_246_, v_expected_250_);
return v___x_286_;
}
}
}
LEAN_EXPORT void l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_0interp(lean_interpreter_value* stack)
{
uint8_t v_stringGap_244_ = stack[0].m_num;
lean_object* v_c_245_ = stack[1].m_obj;
lean_object* v_s_246_ = stack[2].m_obj;
lean_object* v_res_287_;
v_res_287_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(v_stringGap_244_, v_c_245_, v_s_246_);
stack->m_obj
 = v_res_287_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___boxed(lean_object* v_stringGap_288_, lean_object* v_c_289_, lean_object* v_s_290_){
_start:
{
uint8_t v_stringGap_boxed_291_; lean_object* v_res_292_; 
v_stringGap_boxed_291_ = lean_unbox(v_stringGap_288_);
v_res_292_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(v_stringGap_boxed_291_, v_c_289_, v_s_290_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn(lean_object* v_startPos_294_, lean_object* v_c_295_, lean_object* v_s_296_){
_start:
{
lean_object* v_toInputContext_297_; lean_object* v_pos_298_; uint8_t v___x_299_; 
v_toInputContext_297_ = lean_ctor_get(v_c_295_, 0);
v_pos_298_ = lean_ctor_get(v_s_296_, 2);
v___x_299_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_297_, v_pos_298_);
if (v___x_299_ == 0)
{
lean_object* v_inputString_300_; uint32_t v_curr_301_; uint32_t v___x_302_; uint8_t v___x_303_; 
v_inputString_300_ = lean_ctor_get(v_toInputContext_297_, 0);
v_curr_301_ = lean_string_utf8_get_fast(v_inputString_300_, v_pos_298_);
v___x_302_ = 34;
v___x_303_ = lean_uint32_dec_eq(v_curr_301_, v___x_302_);
if (v___x_303_ == 0)
{
uint32_t v___x_304_; uint8_t v___x_305_; 
v___x_304_ = 92;
v___x_305_ = lean_uint32_dec_eq(v_curr_301_, v___x_304_);
if (v___x_305_ == 0)
{
uint8_t v___x_306_; 
v___x_306_ = l_Lake_Toml_isControlChar(v_curr_301_);
if (v___x_306_ == 0)
{
lean_object* v___x_307_; 
lean_inc(v_pos_298_);
v___x_307_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_296_, v_c_295_, v_pos_298_);
lean_dec(v_pos_298_);
v_s_296_ = v___x_307_;
goto _start;
}
else
{
lean_object* v___x_309_; lean_object* v___x_310_; 
lean_dec_ref(v_c_295_);
lean_dec(v_startPos_294_);
v___x_309_ = lean_box(0);
v___x_310_ = l_Lake_Toml_mkUnexpectedCharError(v_s_296_, v_curr_301_, v___x_309_, v___x_306_);
return v___x_310_;
}
}
else
{
lean_object* v___x_311_; lean_object* v_s_312_; lean_object* v_errorMsg_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
lean_inc(v_pos_298_);
v___x_311_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_296_, v_c_295_, v_pos_298_);
lean_dec(v_pos_298_);
lean_inc_ref(v_c_295_);
v_s_312_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(v___x_303_, v_c_295_, v___x_311_);
v_errorMsg_313_ = lean_ctor_get(v_s_312_, 4);
v___x_314_ = lean_box(0);
v___x_315_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_313_, v___x_314_);
if (v___x_315_ == 0)
{
lean_dec_ref(v_c_295_);
lean_dec(v_startPos_294_);
return v_s_312_;
}
else
{
v_s_296_ = v_s_312_;
goto _start;
}
}
}
else
{
lean_object* v___x_317_; 
lean_inc(v_pos_298_);
lean_dec(v_startPos_294_);
v___x_317_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_296_, v_c_295_, v_pos_298_);
lean_dec(v_pos_298_);
lean_dec_ref(v_c_295_);
return v___x_317_;
}
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; 
lean_dec_ref(v_c_295_);
v___x_318_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn___closed__0));
v___x_319_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_296_, v___x_318_, v_startPos_294_);
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicStringFn(lean_object* v_a_324_, lean_object* v_a_325_){
_start:
{
lean_object* v_pos_326_; uint32_t v___x_327_; lean_object* v___x_328_; lean_object* v_s_329_; lean_object* v_errorMsg_330_; lean_object* v___x_331_; uint8_t v___x_332_; 
v_pos_326_ = lean_ctor_get(v_a_325_, 2);
lean_inc(v_pos_326_);
v___x_327_ = 34;
v___x_328_ = ((lean_object*)(l_Lake_Toml_basicStringFn___closed__1));
v_s_329_ = l_Lake_Toml_chFn(v___x_327_, v___x_328_, v_a_324_, v_a_325_);
v_errorMsg_330_ = lean_ctor_get(v_s_329_, 4);
v___x_331_ = lean_box(0);
v___x_332_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_330_, v___x_331_);
if (v___x_332_ == 0)
{
lean_dec(v_pos_326_);
lean_dec_ref(v_a_324_);
return v_s_329_;
}
else
{
lean_object* v___x_333_; 
v___x_333_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn(v_pos_326_, v_a_324_, v_s_329_);
return v___x_333_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(lean_object* v_startPos_335_, lean_object* v_c_336_, lean_object* v_s_337_){
_start:
{
lean_object* v_toInputContext_338_; lean_object* v_pos_339_; uint8_t v___x_340_; 
v_toInputContext_338_ = lean_ctor_get(v_c_336_, 0);
v_pos_339_ = lean_ctor_get(v_s_337_, 2);
v___x_340_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_338_, v_pos_339_);
if (v___x_340_ == 0)
{
lean_object* v_inputString_341_; uint32_t v_curr_342_; uint32_t v___x_343_; uint8_t v___x_344_; 
v_inputString_341_ = lean_ctor_get(v_toInputContext_338_, 0);
v_curr_342_ = lean_string_utf8_get_fast(v_inputString_341_, v_pos_339_);
v___x_343_ = 39;
v___x_344_ = lean_uint32_dec_eq(v_curr_342_, v___x_343_);
if (v___x_344_ == 0)
{
uint8_t v___x_345_; 
v___x_345_ = l_Lake_Toml_isControlChar(v_curr_342_);
if (v___x_345_ == 0)
{
lean_object* v___x_346_; 
lean_inc(v_pos_339_);
v___x_346_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_337_, v_c_336_, v_pos_339_);
lean_dec(v_pos_339_);
v_s_337_ = v___x_346_;
goto _start;
}
else
{
lean_object* v___x_348_; lean_object* v___x_349_; 
lean_dec(v_startPos_335_);
v___x_348_ = lean_box(0);
v___x_349_ = l_Lake_Toml_mkUnexpectedCharError(v_s_337_, v_curr_342_, v___x_348_, v___x_345_);
return v___x_349_;
}
}
else
{
lean_object* v___x_350_; 
lean_inc(v_pos_339_);
lean_dec(v_startPos_335_);
v___x_350_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_337_, v_c_336_, v_pos_339_);
lean_dec(v_pos_339_);
return v___x_350_;
}
}
else
{
lean_object* v___x_351_; lean_object* v___x_352_; 
v___x_351_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___closed__0));
v___x_352_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_337_, v___x_351_, v_startPos_335_);
return v___x_352_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___boxed(lean_object* v_startPos_353_, lean_object* v_c_354_, lean_object* v_s_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(v_startPos_353_, v_c_354_, v_s_355_);
lean_dec_ref(v_c_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalStringFn(lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_pos_363_; uint32_t v___x_364_; lean_object* v___x_365_; lean_object* v_s_366_; lean_object* v_errorMsg_367_; lean_object* v___x_368_; uint8_t v___x_369_; 
v_pos_363_ = lean_ctor_get(v_a_362_, 2);
lean_inc(v_pos_363_);
v___x_364_ = 39;
v___x_365_ = ((lean_object*)(l_Lake_Toml_literalStringFn___closed__1));
v_s_366_ = l_Lake_Toml_chFn(v___x_364_, v___x_365_, v_a_361_, v_a_362_);
v_errorMsg_367_ = lean_ctor_get(v_s_366_, 4);
v___x_368_ = lean_box(0);
v___x_369_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_367_, v___x_368_);
if (v___x_369_ == 0)
{
lean_dec(v_pos_363_);
return v_s_366_;
}
else
{
lean_object* v___x_370_; 
v___x_370_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(v_pos_363_, v_a_361_, v_s_366_);
return v___x_370_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalStringFn___boxed(lean_object* v_a_371_, lean_object* v_a_372_){
_start:
{
lean_object* v_res_373_; 
v_res_373_ = l_Lake_Toml_literalStringFn(v_a_371_, v_a_372_);
lean_dec_ref(v_a_371_);
return v_res_373_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(lean_object* v_startPos_376_, lean_object* v_quoteDepth_377_, lean_object* v_c_378_, lean_object* v_s_379_){
_start:
{
lean_object* v_toInputContext_380_; lean_object* v_pos_381_; uint8_t v___x_382_; 
v_toInputContext_380_ = lean_ctor_get(v_c_378_, 0);
v_pos_381_ = lean_ctor_get(v_s_379_, 2);
v___x_382_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_380_, v_pos_381_);
if (v___x_382_ == 0)
{
lean_object* v_inputString_383_; uint8_t v___x_384_; uint32_t v_curr_385_; uint32_t v___x_386_; uint8_t v___x_387_; 
v_inputString_383_ = lean_ctor_get(v_toInputContext_380_, 0);
v___x_384_ = 1;
v_curr_385_ = lean_string_utf8_get_fast(v_inputString_383_, v_pos_381_);
v___x_386_ = 39;
v___x_387_ = lean_uint32_dec_eq(v_curr_385_, v___x_386_);
if (v___x_387_ == 0)
{
lean_object* v___x_388_; uint8_t v___x_389_; 
v___x_388_ = lean_unsigned_to_nat(3u);
v___x_389_ = lean_nat_dec_le(v___x_388_, v_quoteDepth_377_);
lean_dec(v_quoteDepth_377_);
if (v___x_389_ == 0)
{
uint32_t v___x_390_; uint8_t v___x_391_; 
v___x_390_ = 10;
v___x_391_ = lean_uint32_dec_eq(v_curr_385_, v___x_390_);
if (v___x_391_ == 0)
{
uint32_t v___x_392_; uint8_t v___x_393_; 
v___x_392_ = 13;
v___x_393_ = lean_uint32_dec_eq(v_curr_385_, v___x_392_);
if (v___x_393_ == 0)
{
uint8_t v___x_394_; 
v___x_394_ = l_Lake_Toml_isControlChar(v_curr_385_);
if (v___x_394_ == 0)
{
lean_object* v___x_395_; lean_object* v___x_396_; 
lean_inc(v_pos_381_);
v___x_395_ = lean_unsigned_to_nat(0u);
v___x_396_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_379_, v_c_378_, v_pos_381_);
lean_dec(v_pos_381_);
v_quoteDepth_377_ = v___x_395_;
v_s_379_ = v___x_396_;
goto _start;
}
else
{
lean_object* v___x_398_; lean_object* v___x_399_; 
lean_dec(v_startPos_376_);
v___x_398_ = lean_box(0);
v___x_399_ = l_Lake_Toml_mkUnexpectedCharError(v_s_379_, v_curr_385_, v___x_398_, v___x_384_);
return v___x_399_;
}
}
else
{
lean_object* v___x_400_; lean_object* v_s_401_; lean_object* v_errorMsg_402_; lean_object* v___x_403_; uint8_t v___x_404_; 
lean_inc(v_pos_381_);
v___x_400_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_379_, v_c_378_, v_pos_381_);
lean_dec(v_pos_381_);
v_s_401_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_378_, v___x_400_);
v_errorMsg_402_ = lean_ctor_get(v_s_401_, 4);
v___x_403_ = lean_box(0);
v___x_404_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_402_, v___x_403_);
if (v___x_404_ == 0)
{
lean_dec(v_startPos_376_);
return v_s_401_;
}
else
{
lean_object* v___x_405_; 
v___x_405_ = lean_unsigned_to_nat(0u);
v_quoteDepth_377_ = v___x_405_;
v_s_379_ = v_s_401_;
goto _start;
}
}
}
else
{
lean_object* v___x_407_; lean_object* v___x_408_; 
lean_inc(v_pos_381_);
v___x_407_ = lean_unsigned_to_nat(0u);
v___x_408_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_379_, v_c_378_, v_pos_381_);
lean_dec(v_pos_381_);
v_quoteDepth_377_ = v___x_407_;
v_s_379_ = v___x_408_;
goto _start;
}
}
else
{
lean_dec(v_startPos_376_);
return v_s_379_;
}
}
else
{
lean_object* v_s_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
lean_inc(v_pos_381_);
v_s_410_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_379_, v_c_378_, v_pos_381_);
lean_dec(v_pos_381_);
v___x_411_ = lean_unsigned_to_nat(5u);
v___x_412_ = lean_nat_dec_le(v___x_411_, v_quoteDepth_377_);
if (v___x_412_ == 0)
{
lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_413_ = lean_unsigned_to_nat(1u);
v___x_414_ = lean_nat_add(v_quoteDepth_377_, v___x_413_);
lean_dec(v_quoteDepth_377_);
v_quoteDepth_377_ = v___x_414_;
v_s_379_ = v_s_410_;
goto _start;
}
else
{
lean_object* v___x_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
lean_dec(v_quoteDepth_377_);
lean_dec(v_startPos_376_);
v___x_416_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0));
v___x_417_ = lean_box(0);
v___x_418_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_410_, v___x_416_, v___x_417_, v___x_384_);
return v___x_418_;
}
}
}
else
{
lean_object* v___x_419_; uint8_t v___x_420_; 
v___x_419_ = lean_unsigned_to_nat(3u);
v___x_420_ = lean_nat_dec_le(v___x_419_, v_quoteDepth_377_);
lean_dec(v_quoteDepth_377_);
if (v___x_420_ == 0)
{
lean_object* v___x_421_; lean_object* v___x_422_; 
v___x_421_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__1));
v___x_422_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_379_, v___x_421_, v_startPos_376_);
return v___x_422_;
}
else
{
lean_dec(v_startPos_376_);
return v_s_379_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___boxed(lean_object* v_startPos_423_, lean_object* v_quoteDepth_424_, lean_object* v_c_425_, lean_object* v_s_426_){
_start:
{
lean_object* v_res_427_; 
v_res_427_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(v_startPos_423_, v_quoteDepth_424_, v_c_425_, v_s_426_);
lean_dec_ref(v_c_425_);
return v_res_427_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0(lean_object* v_c_432_, lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
lean_object* v_zero_435_; uint8_t v_isZero_436_; 
v_zero_435_ = lean_unsigned_to_nat(0u);
v_isZero_436_ = lean_nat_dec_eq(v_x_433_, v_zero_435_);
if (v_isZero_436_ == 1)
{
lean_dec(v_x_433_);
return v_x_434_;
}
else
{
uint32_t v___x_437_; lean_object* v___x_438_; lean_object* v_s_439_; lean_object* v_errorMsg_440_; lean_object* v___x_441_; uint8_t v___x_442_; 
v___x_437_ = 39;
v___x_438_ = ((lean_object*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__1));
v_s_439_ = l_Lake_Toml_chFn(v___x_437_, v___x_438_, v_c_432_, v_x_434_);
v_errorMsg_440_ = lean_ctor_get(v_s_439_, 4);
v___x_441_ = lean_box(0);
v___x_442_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_440_, v___x_441_);
if (v___x_442_ == 0)
{
lean_dec(v_x_433_);
return v_s_439_;
}
else
{
lean_object* v_one_443_; lean_object* v_n_444_; 
v_one_443_ = lean_unsigned_to_nat(1u);
v_n_444_ = lean_nat_sub(v_x_433_, v_one_443_);
lean_dec(v_x_433_);
v_x_433_ = v_n_444_;
v_x_434_ = v_s_439_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___boxed(lean_object* v_c_446_, lean_object* v_x_447_, lean_object* v_x_448_){
_start:
{
lean_object* v_res_449_; 
v_res_449_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0(v_c_446_, v_x_447_, v_x_448_);
lean_dec_ref(v_c_446_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralStringFn___lam__0(lean_object* v___x_450_, lean_object* v___y_451_, lean_object* v___y_452_){
_start:
{
lean_object* v___x_453_; 
v___x_453_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0(v___y_451_, v___x_450_, v___y_452_);
return v___x_453_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralStringFn___lam__0___boxed(lean_object* v___x_454_, lean_object* v___y_455_, lean_object* v___y_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Lake_Toml_mlLiteralStringFn___lam__0(v___x_454_, v___y_455_, v___y_456_);
lean_dec_ref(v___y_455_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralStringFn(lean_object* v_a_460_, lean_object* v_a_461_){
_start:
{
lean_object* v_pos_462_; lean_object* v___f_463_; lean_object* v_s_464_; lean_object* v_errorMsg_465_; lean_object* v___x_466_; uint8_t v___x_467_; 
v_pos_462_ = lean_ctor_get(v_a_461_, 2);
lean_inc(v_pos_462_);
v___f_463_ = ((lean_object*)(l_Lake_Toml_mlLiteralStringFn___closed__0));
lean_inc_ref(v_a_460_);
v_s_464_ = l_Lean_Parser_atomicFn(v___f_463_, v_a_460_, v_a_461_);
v_errorMsg_465_ = lean_ctor_get(v_s_464_, 4);
v___x_466_ = lean_box(0);
v___x_467_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_465_, v___x_466_);
if (v___x_467_ == 0)
{
lean_dec(v_pos_462_);
lean_dec_ref(v_a_460_);
return v_s_464_;
}
else
{
lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_468_ = lean_unsigned_to_nat(0u);
v___x_469_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(v_pos_462_, v___x_468_, v_a_460_, v_s_464_);
lean_dec_ref(v_a_460_);
return v___x_469_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn(lean_object* v_startPos_471_, lean_object* v_quoteDepth_472_, lean_object* v_c_473_, lean_object* v_s_474_){
_start:
{
lean_object* v_toInputContext_475_; lean_object* v_pos_476_; uint8_t v___x_477_; 
v_toInputContext_475_ = lean_ctor_get(v_c_473_, 0);
v_pos_476_ = lean_ctor_get(v_s_474_, 2);
v___x_477_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_475_, v_pos_476_);
if (v___x_477_ == 0)
{
lean_object* v_inputString_478_; uint8_t v___x_479_; uint32_t v_curr_480_; uint32_t v___x_481_; uint8_t v___x_482_; 
v_inputString_478_ = lean_ctor_get(v_toInputContext_475_, 0);
v___x_479_ = 1;
v_curr_480_ = lean_string_utf8_get_fast(v_inputString_478_, v_pos_476_);
v___x_481_ = 34;
v___x_482_ = lean_uint32_dec_eq(v_curr_480_, v___x_481_);
if (v___x_482_ == 0)
{
lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_483_ = lean_unsigned_to_nat(3u);
v___x_484_ = lean_nat_dec_le(v___x_483_, v_quoteDepth_472_);
lean_dec(v_quoteDepth_472_);
if (v___x_484_ == 0)
{
uint32_t v___x_485_; uint8_t v___x_486_; 
v___x_485_ = 10;
v___x_486_ = lean_uint32_dec_eq(v_curr_480_, v___x_485_);
if (v___x_486_ == 0)
{
uint32_t v___x_487_; uint8_t v___x_488_; 
v___x_487_ = 13;
v___x_488_ = lean_uint32_dec_eq(v_curr_480_, v___x_487_);
if (v___x_488_ == 0)
{
uint32_t v___x_489_; uint8_t v___x_490_; 
v___x_489_ = 92;
v___x_490_ = lean_uint32_dec_eq(v_curr_480_, v___x_489_);
if (v___x_490_ == 0)
{
uint8_t v___x_491_; 
v___x_491_ = l_Lake_Toml_isControlChar(v_curr_480_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; 
lean_inc(v_pos_476_);
v___x_492_ = lean_unsigned_to_nat(0u);
v___x_493_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_474_, v_c_473_, v_pos_476_);
lean_dec(v_pos_476_);
v_quoteDepth_472_ = v___x_492_;
v_s_474_ = v___x_493_;
goto _start;
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; 
lean_dec_ref(v_c_473_);
lean_dec(v_startPos_471_);
v___x_495_ = lean_box(0);
v___x_496_ = l_Lake_Toml_mkUnexpectedCharError(v_s_474_, v_curr_480_, v___x_495_, v___x_479_);
return v___x_496_;
}
}
else
{
lean_object* v___x_497_; lean_object* v_s_498_; lean_object* v_errorMsg_499_; lean_object* v___x_500_; uint8_t v___x_501_; 
lean_inc(v_pos_476_);
v___x_497_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_474_, v_c_473_, v_pos_476_);
lean_dec(v_pos_476_);
lean_inc_ref(v_c_473_);
v_s_498_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(v___x_479_, v_c_473_, v___x_497_);
v_errorMsg_499_ = lean_ctor_get(v_s_498_, 4);
v___x_500_ = lean_box(0);
v___x_501_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_499_, v___x_500_);
if (v___x_501_ == 0)
{
lean_dec_ref(v_c_473_);
lean_dec(v_startPos_471_);
return v_s_498_;
}
else
{
lean_object* v___x_502_; 
v___x_502_ = lean_unsigned_to_nat(0u);
v_quoteDepth_472_ = v___x_502_;
v_s_474_ = v_s_498_;
goto _start;
}
}
}
else
{
lean_object* v___x_504_; lean_object* v_s_505_; lean_object* v_errorMsg_506_; lean_object* v___x_507_; uint8_t v___x_508_; 
lean_inc(v_pos_476_);
v___x_504_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_474_, v_c_473_, v_pos_476_);
lean_dec(v_pos_476_);
v_s_505_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_473_, v___x_504_);
v_errorMsg_506_ = lean_ctor_get(v_s_505_, 4);
v___x_507_ = lean_box(0);
v___x_508_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_506_, v___x_507_);
if (v___x_508_ == 0)
{
lean_dec_ref(v_c_473_);
lean_dec(v_startPos_471_);
return v_s_505_;
}
else
{
lean_object* v___x_509_; 
v___x_509_ = lean_unsigned_to_nat(0u);
v_quoteDepth_472_ = v___x_509_;
v_s_474_ = v_s_505_;
goto _start;
}
}
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; 
lean_inc(v_pos_476_);
v___x_511_ = lean_unsigned_to_nat(0u);
v___x_512_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_474_, v_c_473_, v_pos_476_);
lean_dec(v_pos_476_);
v_quoteDepth_472_ = v___x_511_;
v_s_474_ = v___x_512_;
goto _start;
}
}
else
{
lean_dec_ref(v_c_473_);
lean_dec(v_startPos_471_);
return v_s_474_;
}
}
else
{
lean_object* v_s_514_; lean_object* v___x_515_; uint8_t v___x_516_; 
lean_inc(v_pos_476_);
v_s_514_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_474_, v_c_473_, v_pos_476_);
lean_dec(v_pos_476_);
v___x_515_ = lean_unsigned_to_nat(5u);
v___x_516_ = lean_nat_dec_le(v___x_515_, v_quoteDepth_472_);
if (v___x_516_ == 0)
{
lean_object* v___x_517_; lean_object* v___x_518_; 
v___x_517_ = lean_unsigned_to_nat(1u);
v___x_518_ = lean_nat_add(v_quoteDepth_472_, v___x_517_);
lean_dec(v_quoteDepth_472_);
v_quoteDepth_472_ = v___x_518_;
v_s_474_ = v_s_514_;
goto _start;
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; 
lean_dec_ref(v_c_473_);
lean_dec(v_quoteDepth_472_);
lean_dec(v_startPos_471_);
v___x_520_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0));
v___x_521_ = lean_box(0);
v___x_522_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_514_, v___x_520_, v___x_521_, v___x_479_);
return v___x_522_;
}
}
}
else
{
lean_object* v___x_523_; uint8_t v___x_524_; 
lean_dec_ref(v_c_473_);
v___x_523_ = lean_unsigned_to_nat(3u);
v___x_524_ = lean_nat_dec_le(v___x_523_, v_quoteDepth_472_);
lean_dec(v_quoteDepth_472_);
if (v___x_524_ == 0)
{
lean_object* v___x_525_; lean_object* v___x_526_; 
v___x_525_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn___closed__0));
v___x_526_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_474_, v___x_525_, v_startPos_471_);
return v___x_526_;
}
else
{
lean_dec(v_startPos_471_);
return v_s_474_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0(lean_object* v_c_531_, lean_object* v_x_532_, lean_object* v_x_533_){
_start:
{
lean_object* v_zero_534_; uint8_t v_isZero_535_; 
v_zero_534_ = lean_unsigned_to_nat(0u);
v_isZero_535_ = lean_nat_dec_eq(v_x_532_, v_zero_534_);
if (v_isZero_535_ == 1)
{
lean_dec(v_x_532_);
return v_x_533_;
}
else
{
uint32_t v___x_536_; lean_object* v___x_537_; lean_object* v_s_538_; lean_object* v_errorMsg_539_; lean_object* v___x_540_; uint8_t v___x_541_; 
v___x_536_ = 34;
v___x_537_ = ((lean_object*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__1));
v_s_538_ = l_Lake_Toml_chFn(v___x_536_, v___x_537_, v_c_531_, v_x_533_);
v_errorMsg_539_ = lean_ctor_get(v_s_538_, 4);
v___x_540_ = lean_box(0);
v___x_541_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_539_, v___x_540_);
if (v___x_541_ == 0)
{
lean_dec(v_x_532_);
return v_s_538_;
}
else
{
lean_object* v_one_542_; lean_object* v_n_543_; 
v_one_542_ = lean_unsigned_to_nat(1u);
v_n_543_ = lean_nat_sub(v_x_532_, v_one_542_);
lean_dec(v_x_532_);
v_x_532_ = v_n_543_;
v_x_533_ = v_s_538_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___boxed(lean_object* v_c_545_, lean_object* v_x_546_, lean_object* v_x_547_){
_start:
{
lean_object* v_res_548_; 
v_res_548_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0(v_c_545_, v_x_546_, v_x_547_);
lean_dec_ref(v_c_545_);
return v_res_548_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicStringFn___lam__0(lean_object* v___x_549_, lean_object* v___y_550_, lean_object* v___y_551_){
_start:
{
lean_object* v___x_552_; 
v___x_552_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0(v___y_550_, v___x_549_, v___y_551_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicStringFn___lam__0___boxed(lean_object* v___x_553_, lean_object* v___y_554_, lean_object* v___y_555_){
_start:
{
lean_object* v_res_556_; 
v_res_556_ = l_Lake_Toml_mlBasicStringFn___lam__0(v___x_553_, v___y_554_, v___y_555_);
lean_dec_ref(v___y_554_);
return v_res_556_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicStringFn(lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_pos_561_; lean_object* v___f_562_; lean_object* v_s_563_; lean_object* v_errorMsg_564_; lean_object* v___x_565_; uint8_t v___x_566_; 
v_pos_561_ = lean_ctor_get(v_a_560_, 2);
lean_inc(v_pos_561_);
v___f_562_ = ((lean_object*)(l_Lake_Toml_mlBasicStringFn___closed__0));
lean_inc_ref(v_a_559_);
v_s_563_ = l_Lean_Parser_atomicFn(v___f_562_, v_a_559_, v_a_560_);
v_errorMsg_564_ = lean_ctor_get(v_s_563_, 4);
v___x_565_ = lean_box(0);
v___x_566_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_564_, v___x_565_);
if (v___x_566_ == 0)
{
lean_dec(v_pos_561_);
lean_dec_ref(v_a_559_);
return v_s_563_;
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = lean_unsigned_to_nat(0u);
v___x_568_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn(v_pos_561_, v___x_567_, v_a_559_, v_s_563_);
return v___x_568_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(lean_object* v_a_581_, lean_object* v_a_582_){
_start:
{
lean_object* v___x_583_; lean_object* v_s_584_; lean_object* v_errorMsg_585_; lean_object* v___x_586_; uint8_t v___x_587_; 
v___x_583_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__1));
v_s_584_ = l_Lake_Toml_digitPairFn(v___x_583_, v_a_581_, v_a_582_);
v_errorMsg_585_ = lean_ctor_get(v_s_584_, 4);
v___x_586_ = lean_box(0);
v___x_587_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_585_, v___x_586_);
if (v___x_587_ == 0)
{
return v_s_584_;
}
else
{
uint32_t v___x_588_; lean_object* v___x_589_; lean_object* v_s_590_; lean_object* v_errorMsg_591_; uint8_t v___x_592_; 
v___x_588_ = 58;
v___x_589_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v_s_590_ = l_Lake_Toml_chFn(v___x_588_, v___x_589_, v_a_581_, v_s_584_);
v_errorMsg_591_ = lean_ctor_get(v_s_590_, 4);
v___x_592_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_591_, v___x_586_);
if (v___x_592_ == 0)
{
return v_s_590_;
}
else
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5));
v___x_594_ = l_Lake_Toml_digitPairFn(v___x_593_, v_a_581_, v_s_590_);
return v___x_594_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___boxed(lean_object* v_a_595_, lean_object* v_a_596_){
_start:
{
lean_object* v_res_597_; 
v_res_597_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(v_a_595_, v_a_596_);
lean_dec_ref(v_a_595_);
return v_res_597_;
}
}
lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn(uint8_t v_allowOffset_599_, uint32_t v_curr_600_, lean_object* v_nextPos_601_, lean_object* v_c_602_, lean_object* v_s_603_){
_start:
{
uint32_t v___x_610_; uint8_t v___x_611_; 
v___x_610_ = 90;
v___x_611_ = lean_uint32_dec_eq(v_curr_600_, v___x_610_);
if (v___x_611_ == 0)
{
uint32_t v___x_612_; uint8_t v___x_613_; 
v___x_612_ = 122;
v___x_613_ = lean_uint32_dec_eq(v_curr_600_, v___x_612_);
if (v___x_613_ == 0)
{
uint8_t v___x_614_; uint32_t v___x_621_; uint8_t v___x_622_; 
v___x_614_ = 1;
v___x_621_ = 43;
v___x_622_ = lean_uint32_dec_eq(v_curr_600_, v___x_621_);
if (v___x_622_ == 0)
{
uint32_t v___x_623_; uint8_t v___x_624_; 
v___x_623_ = 45;
v___x_624_ = lean_uint32_dec_eq(v_curr_600_, v___x_623_);
if (v___x_624_ == 0)
{
lean_dec(v_nextPos_601_);
return v_s_603_;
}
else
{
goto v___jp_615_;
}
}
else
{
goto v___jp_615_;
}
v___jp_615_:
{
if (v_allowOffset_599_ == 0)
{
lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; 
lean_dec(v_nextPos_601_);
v___x_616_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_617_ = lean_box(0);
v___x_618_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_603_, v___x_616_, v___x_617_, v___x_614_);
return v___x_618_;
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = l_Lean_Parser_ParserState_setPos(v_s_603_, v_nextPos_601_);
v___x_620_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(v_c_602_, v___x_619_);
return v___x_620_;
}
}
}
else
{
goto v___jp_604_;
}
}
else
{
goto v___jp_604_;
}
v___jp_604_:
{
if (v_allowOffset_599_ == 0)
{
uint8_t v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; 
lean_dec(v_nextPos_601_);
v___x_605_ = 1;
v___x_606_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_607_ = lean_box(0);
v___x_608_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_603_, v___x_606_, v___x_607_, v___x_605_);
return v___x_608_;
}
else
{
lean_object* v___x_609_; 
v___x_609_ = l_Lean_Parser_ParserState_setPos(v_s_603_, v_nextPos_601_);
return v___x_609_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn_0interp(lean_interpreter_value* stack)
{
uint8_t v_allowOffset_599_ = stack[0].m_num;
uint32_t v_curr_600_ = stack[1].m_num;
lean_object* v_nextPos_601_ = stack[2].m_obj;
lean_object* v_c_602_ = stack[3].m_obj;
lean_object* v_s_603_ = stack[4].m_obj;
lean_object* v_res_625_;
v_res_625_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn(v_allowOffset_599_, v_curr_600_, v_nextPos_601_, v_c_602_, v_s_603_);
stack->m_obj
 = v_res_625_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___boxed(lean_object* v_allowOffset_626_, lean_object* v_curr_627_, lean_object* v_nextPos_628_, lean_object* v_c_629_, lean_object* v_s_630_){
_start:
{
uint8_t v_allowOffset_boxed_631_; uint32_t v_curr_boxed_632_; lean_object* v_res_633_; 
v_allowOffset_boxed_631_ = lean_unbox(v_allowOffset_626_);
v_curr_boxed_632_ = lean_unbox_uint32(v_curr_627_);
lean_dec(v_curr_627_);
v_res_633_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn(v_allowOffset_boxed_631_, v_curr_boxed_632_, v_nextPos_628_, v_c_629_, v_s_630_);
lean_dec_ref(v_c_629_);
return v_res_633_;
}
}
uint8_t l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0(uint32_t v_x_634_){
_start:
{
uint32_t v___x_635_; uint8_t v___x_636_; 
v___x_635_ = 48;
v___x_636_ = lean_uint32_dec_le(v___x_635_, v_x_634_);
if (v___x_636_ == 0)
{
return v___x_636_;
}
else
{
uint32_t v___x_637_; uint8_t v___x_638_; 
v___x_637_ = 57;
v___x_638_ = lean_uint32_dec_le(v_x_634_, v___x_637_);
return v___x_638_;
}
}
}
LEAN_EXPORT void l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_x_634_ = stack[0].m_num;
uint8_t v_res_639_;
v_res_639_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0(v_x_634_);
stack->m_num = v_res_639_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0___boxed(lean_object* v_x_640_){
_start:
{
uint32_t v_x_270__boxed_641_; uint8_t v_res_642_; lean_object* v_r_643_; 
v_x_270__boxed_641_ = lean_unbox_uint32(v_x_640_);
lean_dec(v_x_640_);
v_res_642_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0(v_x_270__boxed_641_);
v_r_643_ = lean_box(v_res_642_);
return v_r_643_;
}
}
lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(uint8_t v_allowOffset_649_, lean_object* v_c_650_, lean_object* v_s_651_){
_start:
{
lean_object* v_toInputContext_652_; lean_object* v_pos_653_; uint8_t v___x_654_; 
v_toInputContext_652_ = lean_ctor_get(v_c_650_, 0);
v_pos_653_ = lean_ctor_get(v_s_651_, 2);
v___x_654_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_652_, v_pos_653_);
if (v___x_654_ == 0)
{
lean_object* v_inputString_655_; uint32_t v_curr_656_; uint32_t v___x_657_; uint8_t v___x_658_; 
v_inputString_655_ = lean_ctor_get(v_toInputContext_652_, 0);
v_curr_656_ = lean_string_utf8_get_fast(v_inputString_655_, v_pos_653_);
v___x_657_ = 46;
v___x_658_ = lean_uint32_dec_eq(v_curr_656_, v___x_657_);
if (v___x_658_ == 0)
{
lean_object* v___x_659_; uint32_t v___x_666_; uint8_t v___x_667_; 
v___x_659_ = lean_string_utf8_next_fast(v_inputString_655_, v_pos_653_);
v___x_666_ = 90;
v___x_667_ = lean_uint32_dec_eq(v_curr_656_, v___x_666_);
if (v___x_667_ == 0)
{
uint32_t v___x_668_; uint8_t v___x_669_; 
v___x_668_ = 122;
v___x_669_ = lean_uint32_dec_eq(v_curr_656_, v___x_668_);
if (v___x_669_ == 0)
{
uint8_t v___x_670_; uint32_t v___x_677_; uint8_t v___x_678_; 
v___x_670_ = 1;
v___x_677_ = 43;
v___x_678_ = lean_uint32_dec_eq(v_curr_656_, v___x_677_);
if (v___x_678_ == 0)
{
uint32_t v___x_679_; uint8_t v___x_680_; 
v___x_679_ = 45;
v___x_680_ = lean_uint32_dec_eq(v_curr_656_, v___x_679_);
if (v___x_680_ == 0)
{
return v_s_651_;
}
else
{
goto v___jp_671_;
}
}
else
{
goto v___jp_671_;
}
v___jp_671_:
{
if (v_allowOffset_649_ == 0)
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_672_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_673_ = lean_box(0);
v___x_674_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_651_, v___x_672_, v___x_673_, v___x_670_);
return v___x_674_;
}
else
{
lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_675_ = l_Lean_Parser_ParserState_setPos(v_s_651_, v___x_659_);
v___x_676_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(v_c_650_, v___x_675_);
return v___x_676_;
}
}
}
else
{
goto v___jp_660_;
}
}
else
{
goto v___jp_660_;
}
v___jp_660_:
{
if (v_allowOffset_649_ == 0)
{
uint8_t v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_661_ = 1;
v___x_662_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_663_ = lean_box(0);
v___x_664_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_651_, v___x_662_, v___x_663_, v___x_661_);
return v___x_664_;
}
else
{
lean_object* v___x_665_; 
v___x_665_ = l_Lean_Parser_ParserState_setPos(v_s_651_, v___x_659_);
return v___x_665_;
}
}
}
else
{
lean_object* v___f_681_; lean_object* v_s_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v_s_685_; lean_object* v_pos_686_; lean_object* v_errorMsg_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
lean_inc(v_pos_653_);
v___f_681_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0));
v_s_682_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_651_, v_c_650_, v_pos_653_);
lean_dec(v_pos_653_);
v___x_683_ = lean_box(0);
v___x_684_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__2));
v_s_685_ = l_Lake_Toml_takeWhile1Fn(v___f_681_, v___x_684_, v_c_650_, v_s_682_);
v_pos_686_ = lean_ctor_get(v_s_685_, 2);
v_errorMsg_687_ = lean_ctor_get(v_s_685_, 4);
v___x_688_ = lean_box(0);
v___x_689_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_687_, v___x_688_);
if (v___x_689_ == 0)
{
return v_s_685_;
}
else
{
if (v___x_654_ == 0)
{
uint8_t v___x_690_; 
v___x_690_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_652_, v_pos_686_);
if (v___x_690_ == 0)
{
uint32_t v___x_691_; lean_object* v___x_692_; uint32_t v___x_702_; uint8_t v___x_703_; 
v___x_691_ = lean_string_utf8_get_fast(v_inputString_655_, v_pos_686_);
v___x_692_ = lean_string_utf8_next_fast(v_inputString_655_, v_pos_686_);
v___x_702_ = 90;
v___x_703_ = lean_uint32_dec_eq(v___x_691_, v___x_702_);
if (v___x_703_ == 0)
{
uint32_t v___x_704_; uint8_t v___x_705_; 
v___x_704_ = 122;
v___x_705_ = lean_uint32_dec_eq(v___x_691_, v___x_704_);
if (v___x_705_ == 0)
{
uint32_t v___x_706_; uint8_t v___x_707_; 
v___x_706_ = 43;
v___x_707_ = lean_uint32_dec_eq(v___x_691_, v___x_706_);
if (v___x_707_ == 0)
{
uint32_t v___x_708_; uint8_t v___x_709_; 
v___x_708_ = 45;
v___x_709_ = lean_uint32_dec_eq(v___x_691_, v___x_708_);
if (v___x_709_ == 0)
{
return v_s_685_;
}
else
{
goto v___jp_693_;
}
}
else
{
goto v___jp_693_;
}
}
else
{
goto v___jp_698_;
}
}
else
{
goto v___jp_698_;
}
v___jp_693_:
{
if (v_allowOffset_649_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; 
v___x_694_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_695_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_685_, v___x_694_, v___x_683_, v___x_658_);
return v___x_695_;
}
else
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = l_Lean_Parser_ParserState_setPos(v_s_685_, v___x_692_);
v___x_697_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(v_c_650_, v___x_696_);
return v___x_697_;
}
}
v___jp_698_:
{
if (v_allowOffset_649_ == 0)
{
lean_object* v___x_699_; lean_object* v___x_700_; 
v___x_699_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_700_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_685_, v___x_699_, v___x_683_, v___x_658_);
return v___x_700_;
}
else
{
lean_object* v___x_701_; 
v___x_701_ = l_Lean_Parser_ParserState_setPos(v_s_685_, v___x_692_);
return v___x_701_;
}
}
}
else
{
return v_s_685_;
}
}
else
{
return v_s_685_;
}
}
}
}
else
{
return v_s_651_;
}
}
}
LEAN_EXPORT void l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_0interp(lean_interpreter_value* stack)
{
uint8_t v_allowOffset_649_ = stack[0].m_num;
lean_object* v_c_650_ = stack[1].m_obj;
lean_object* v_s_651_ = stack[2].m_obj;
lean_object* v_res_710_;
v_res_710_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(v_allowOffset_649_, v_c_650_, v_s_651_);
stack->m_obj
 = v_res_710_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___boxed(lean_object* v_allowOffset_711_, lean_object* v_c_712_, lean_object* v_s_713_){
_start:
{
uint8_t v_allowOffset_boxed_714_; lean_object* v_res_715_; 
v_allowOffset_boxed_714_ = lean_unbox(v_allowOffset_711_);
v_res_715_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(v_allowOffset_boxed_714_, v_c_712_, v_s_713_);
lean_dec_ref(v_c_712_);
return v_res_715_;
}
}
lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(uint8_t v_allowOffset_720_, lean_object* v_a_721_, lean_object* v_a_722_){
_start:
{
lean_object* v___x_723_; lean_object* v_s_724_; lean_object* v_errorMsg_725_; lean_object* v___x_726_; uint8_t v___x_727_; 
v___x_723_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5));
v_s_724_ = l_Lake_Toml_digitPairFn(v___x_723_, v_a_721_, v_a_722_);
v_errorMsg_725_ = lean_ctor_get(v_s_724_, 4);
v___x_726_ = lean_box(0);
v___x_727_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_725_, v___x_726_);
if (v___x_727_ == 0)
{
return v_s_724_;
}
else
{
uint32_t v___x_728_; lean_object* v___x_729_; lean_object* v_s_730_; lean_object* v_errorMsg_731_; uint8_t v___x_732_; 
v___x_728_ = 58;
v___x_729_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v_s_730_ = l_Lake_Toml_chFn(v___x_728_, v___x_729_, v_a_721_, v_s_724_);
v_errorMsg_731_ = lean_ctor_get(v_s_730_, 4);
v___x_732_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_731_, v___x_726_);
if (v___x_732_ == 0)
{
return v_s_730_;
}
else
{
lean_object* v___x_733_; lean_object* v_s_734_; lean_object* v_errorMsg_735_; uint8_t v___x_736_; 
v___x_733_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__1));
v_s_734_ = l_Lake_Toml_digitPairFn(v___x_733_, v_a_721_, v_s_730_);
v_errorMsg_735_ = lean_ctor_get(v_s_734_, 4);
v___x_736_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_735_, v___x_726_);
if (v___x_736_ == 0)
{
return v_s_734_;
}
else
{
lean_object* v___x_737_; 
v___x_737_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(v_allowOffset_720_, v_a_721_, v_s_734_);
return v___x_737_;
}
}
}
}
}
LEAN_EXPORT void l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn_0interp(lean_interpreter_value* stack)
{
uint8_t v_allowOffset_720_ = stack[0].m_num;
lean_object* v_a_721_ = stack[1].m_obj;
lean_object* v_a_722_ = stack[2].m_obj;
lean_object* v_res_738_;
v_res_738_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(v_allowOffset_720_, v_a_721_, v_a_722_);
stack->m_obj
 = v_res_738_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___boxed(lean_object* v_allowOffset_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
uint8_t v_allowOffset_boxed_742_; lean_object* v_res_743_; 
v_allowOffset_boxed_742_ = lean_unbox(v_allowOffset_739_);
v_res_743_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(v_allowOffset_boxed_742_, v_a_740_, v_a_741_);
lean_dec_ref(v_a_740_);
return v_res_743_;
}
}
lean_object* l_Lake_Toml_timeFn(uint8_t v_allowOffset_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v___x_751_; lean_object* v_s_752_; lean_object* v_errorMsg_753_; lean_object* v___x_754_; uint8_t v___x_755_; 
v___x_751_ = ((lean_object*)(l_Lake_Toml_timeFn___closed__1));
v_s_752_ = l_Lake_Toml_digitPairFn(v___x_751_, v_a_749_, v_a_750_);
v_errorMsg_753_ = lean_ctor_get(v_s_752_, 4);
v___x_754_ = lean_box(0);
v___x_755_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_753_, v___x_754_);
if (v___x_755_ == 0)
{
return v_s_752_;
}
else
{
uint32_t v___x_756_; lean_object* v___x_757_; lean_object* v_s_758_; lean_object* v_errorMsg_759_; uint8_t v___x_760_; 
v___x_756_ = 58;
v___x_757_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v_s_758_ = l_Lake_Toml_chFn(v___x_756_, v___x_757_, v_a_749_, v_s_752_);
v_errorMsg_759_ = lean_ctor_get(v_s_758_, 4);
v___x_760_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_759_, v___x_754_);
if (v___x_760_ == 0)
{
return v_s_758_;
}
else
{
lean_object* v___x_761_; 
v___x_761_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(v_allowOffset_748_, v_a_749_, v_s_758_);
return v___x_761_;
}
}
}
}
LEAN_EXPORT void l_Lake_Toml_timeFn_0interp(lean_interpreter_value* stack)
{
uint8_t v_allowOffset_748_ = stack[0].m_num;
lean_object* v_a_749_ = stack[1].m_obj;
lean_object* v_a_750_ = stack[2].m_obj;
lean_object* v_res_762_;
v_res_762_ = l_Lake_Toml_timeFn(v_allowOffset_748_, v_a_749_, v_a_750_);
stack->m_obj
 = v_res_762_;
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
v_errorMsg_789_ = lean_ctor_get(v_s_787_, 4);
v___x_790_ = lean_box(0);
v___x_791_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_789_, v___x_790_);
if (v___x_791_ == 0)
{
uint8_t v_decide_792_; 
v_decide_792_ = lean_nat_dec_eq(v_pos_788_, v_tPos_785_);
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
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(lean_object* v_a_812_, lean_object* v_a_813_){
_start:
{
lean_object* v___x_814_; lean_object* v_s_815_; lean_object* v_errorMsg_816_; lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_814_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__1));
v_s_815_ = l_Lake_Toml_digitPairFn(v___x_814_, v_a_812_, v_a_813_);
v_errorMsg_816_ = lean_ctor_get(v_s_815_, 4);
v___x_817_ = lean_box(0);
v___x_818_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_816_, v___x_817_);
if (v___x_818_ == 0)
{
return v_s_815_;
}
else
{
uint32_t v___x_819_; lean_object* v___x_820_; lean_object* v_s_821_; lean_object* v_errorMsg_822_; uint8_t v___x_823_; 
v___x_819_ = 45;
v___x_820_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3));
v_s_821_ = l_Lake_Toml_chFn(v___x_819_, v___x_820_, v_a_812_, v_s_815_);
v_errorMsg_822_ = lean_ctor_get(v_s_821_, 4);
v___x_823_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_822_, v___x_817_);
if (v___x_823_ == 0)
{
return v_s_821_;
}
else
{
lean_object* v___x_824_; lean_object* v_s_825_; lean_object* v_errorMsg_826_; uint8_t v___x_827_; 
v___x_824_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5));
v_s_825_ = l_Lake_Toml_digitPairFn(v___x_824_, v_a_812_, v_s_821_);
v_errorMsg_826_ = lean_ctor_get(v_s_825_, 4);
v___x_827_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_826_, v___x_817_);
if (v___x_827_ == 0)
{
return v_s_825_;
}
else
{
lean_object* v___x_828_; 
v___x_828_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(v_a_812_, v_s_825_);
return v___x_828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___boxed(lean_object* v_a_829_, lean_object* v_a_830_){
_start:
{
lean_object* v_res_831_; 
v_res_831_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(v_a_829_, v_a_830_);
lean_dec_ref(v_a_829_);
return v_res_831_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0(lean_object* v_c_836_, lean_object* v_x_837_, lean_object* v_x_838_){
_start:
{
lean_object* v_zero_839_; uint8_t v_isZero_840_; 
v_zero_839_ = lean_unsigned_to_nat(0u);
v_isZero_840_ = lean_nat_dec_eq(v_x_837_, v_zero_839_);
if (v_isZero_840_ == 1)
{
lean_dec(v_x_837_);
return v_x_838_;
}
else
{
lean_object* v___x_841_; lean_object* v_s_842_; lean_object* v_errorMsg_843_; lean_object* v___x_844_; uint8_t v___x_845_; 
v___x_841_ = ((lean_object*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__1));
v_s_842_ = l_Lake_Toml_digitFn(v___x_841_, v_c_836_, v_x_838_);
v_errorMsg_843_ = lean_ctor_get(v_s_842_, 4);
v___x_844_ = lean_box(0);
v___x_845_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_843_, v___x_844_);
if (v___x_845_ == 0)
{
lean_dec(v_x_837_);
return v_s_842_;
}
else
{
lean_object* v_one_846_; lean_object* v_n_847_; 
v_one_846_ = lean_unsigned_to_nat(1u);
v_n_847_ = lean_nat_sub(v_x_837_, v_one_846_);
lean_dec(v_x_837_);
v_x_837_ = v_n_847_;
v_x_838_ = v_s_842_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___boxed(lean_object* v_c_849_, lean_object* v_x_850_, lean_object* v_x_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0(v_c_849_, v_x_850_, v_x_851_);
lean_dec_ref(v_c_849_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dateTimeFn(lean_object* v_a_853_, lean_object* v_a_854_){
_start:
{
lean_object* v___x_855_; lean_object* v_s_856_; lean_object* v_errorMsg_857_; lean_object* v___x_858_; uint8_t v___x_859_; 
v___x_855_ = lean_unsigned_to_nat(4u);
v_s_856_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0(v_a_853_, v___x_855_, v_a_854_);
v_errorMsg_857_ = lean_ctor_get(v_s_856_, 4);
v___x_858_ = lean_box(0);
v___x_859_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_857_, v___x_858_);
if (v___x_859_ == 0)
{
return v_s_856_;
}
else
{
uint32_t v___x_860_; lean_object* v___x_861_; lean_object* v_s_862_; lean_object* v_errorMsg_863_; uint8_t v___x_864_; 
v___x_860_ = 45;
v___x_861_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3));
v_s_862_ = l_Lake_Toml_chFn(v___x_860_, v___x_861_, v_a_853_, v_s_856_);
v_errorMsg_863_ = lean_ctor_get(v_s_862_, 4);
v___x_864_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_863_, v___x_858_);
if (v___x_864_ == 0)
{
return v_s_862_;
}
else
{
lean_object* v___x_865_; 
v___x_865_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(v_a_853_, v_s_862_);
return v___x_865_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dateTimeFn___boxed(lean_object* v_a_866_, lean_object* v_a_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l_Lake_Toml_dateTimeFn(v_a_866_, v_a_867_);
lean_dec_ref(v_a_866_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(lean_object* v_c_873_, lean_object* v_s_874_){
_start:
{
lean_object* v_toInputContext_875_; lean_object* v_pos_876_; lean_object* v_expected_877_; uint8_t v___x_878_; 
v_toInputContext_875_ = lean_ctor_get(v_c_873_, 0);
v_pos_876_ = lean_ctor_get(v_s_874_, 2);
v_expected_877_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__1));
v___x_878_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_875_, v_pos_876_);
if (v___x_878_ == 0)
{
lean_object* v_inputString_879_; lean_object* v___f_880_; uint32_t v_curr_885_; uint32_t v___x_886_; uint8_t v___x_887_; 
v_inputString_879_ = lean_ctor_get(v_toInputContext_875_, 0);
v___f_880_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0));
v_curr_885_ = lean_string_utf8_get_fast(v_inputString_879_, v_pos_876_);
v___x_886_ = 45;
v___x_887_ = lean_uint32_dec_eq(v_curr_885_, v___x_886_);
if (v___x_887_ == 0)
{
uint32_t v___x_888_; uint8_t v___x_889_; 
v___x_888_ = 43;
v___x_889_ = lean_uint32_dec_eq(v_curr_885_, v___x_888_);
if (v___x_889_ == 0)
{
uint8_t v___x_890_; uint32_t v___x_891_; uint8_t v___x_892_; 
v___x_890_ = 1;
v___x_891_ = 48;
v___x_892_ = lean_uint32_dec_le(v___x_891_, v_curr_885_);
if (v___x_892_ == 0)
{
lean_object* v___x_893_; 
v___x_893_ = l_Lake_Toml_mkUnexpectedCharError(v_s_874_, v_curr_885_, v_expected_877_, v___x_890_);
return v___x_893_;
}
else
{
uint32_t v___x_894_; uint8_t v___x_895_; 
v___x_894_ = 57;
v___x_895_ = lean_uint32_dec_le(v_curr_885_, v___x_894_);
if (v___x_895_ == 0)
{
lean_object* v___x_896_; 
v___x_896_ = l_Lake_Toml_mkUnexpectedCharError(v_s_874_, v_curr_885_, v_expected_877_, v___x_890_);
return v___x_896_;
}
else
{
lean_object* v_s_897_; uint32_t v___x_898_; lean_object* v___x_899_; 
lean_inc(v_pos_876_);
v_s_897_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_874_, v_c_873_, v_pos_876_);
lean_dec(v_pos_876_);
v___x_898_ = 95;
v___x_899_ = l_Lake_Toml_sepByChar1AuxFn(v___f_880_, v___x_898_, v_expected_877_, v_c_873_, v_s_897_);
return v___x_899_;
}
}
}
else
{
lean_inc(v_pos_876_);
goto v___jp_881_;
}
}
else
{
lean_inc(v_pos_876_);
goto v___jp_881_;
}
v___jp_881_:
{
lean_object* v_s_882_; uint32_t v___x_883_; lean_object* v___x_884_; 
v_s_882_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_874_, v_c_873_, v_pos_876_);
lean_dec(v_pos_876_);
v___x_883_ = 95;
v___x_884_ = l_Lake_Toml_sepByChar1Fn(v___f_880_, v___x_883_, v_expected_877_, v_c_873_, v_s_882_);
return v___x_884_;
}
}
else
{
lean_object* v___x_900_; 
v___x_900_ = l_Lean_Parser_ParserState_mkEOIError(v_s_874_, v_expected_877_);
return v___x_900_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___boxed(lean_object* v_c_901_, lean_object* v_s_902_){
_start:
{
lean_object* v_res_903_; 
v_res_903_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(v_c_901_, v_s_902_);
lean_dec_ref(v_c_901_);
return v_res_903_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(lean_object* v_c_904_, lean_object* v_s_905_){
_start:
{
lean_object* v_toInputContext_906_; lean_object* v_pos_907_; uint8_t v___x_911_; 
v_toInputContext_906_ = lean_ctor_get(v_c_904_, 0);
v_pos_907_ = lean_ctor_get(v_s_905_, 2);
v___x_911_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_906_, v_pos_907_);
if (v___x_911_ == 0)
{
lean_object* v_inputString_912_; uint32_t v_curr_913_; uint32_t v___x_914_; uint8_t v___x_915_; 
v_inputString_912_ = lean_ctor_get(v_toInputContext_906_, 0);
v_curr_913_ = lean_string_utf8_get_fast(v_inputString_912_, v_pos_907_);
v___x_914_ = 101;
v___x_915_ = lean_uint32_dec_eq(v_curr_913_, v___x_914_);
if (v___x_915_ == 0)
{
uint32_t v___x_916_; uint8_t v___x_917_; 
v___x_916_ = 69;
v___x_917_ = lean_uint32_dec_eq(v_curr_913_, v___x_916_);
if (v___x_917_ == 0)
{
return v_s_905_;
}
else
{
lean_inc(v_pos_907_);
goto v___jp_908_;
}
}
else
{
lean_inc(v_pos_907_);
goto v___jp_908_;
}
}
else
{
return v_s_905_;
}
v___jp_908_:
{
lean_object* v___x_909_; lean_object* v___x_910_; 
v___x_909_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_905_, v_c_904_, v_pos_907_);
lean_dec(v_pos_907_);
v___x_910_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(v_c_904_, v___x_909_);
return v___x_910_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn___boxed(lean_object* v_c_918_, lean_object* v_s_919_){
_start:
{
lean_object* v_res_920_; 
v_res_920_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(v_c_918_, v_s_919_);
lean_dec_ref(v_c_918_);
return v_res_920_;
}
}
lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(lean_object* v_startPos_938_, uint32_t v_curr_939_, lean_object* v_nextPos_940_, lean_object* v_c_941_, lean_object* v_s_942_){
_start:
{
uint32_t v___x_952_; uint8_t v___x_953_; 
v___x_952_ = 46;
v___x_953_ = lean_uint32_dec_eq(v_curr_939_, v___x_952_);
if (v___x_953_ == 0)
{
uint32_t v___x_954_; uint8_t v___x_955_; 
v___x_954_ = 101;
v___x_955_ = lean_uint32_dec_eq(v_curr_939_, v___x_954_);
if (v___x_955_ == 0)
{
uint32_t v___x_956_; uint8_t v___x_957_; 
v___x_956_ = 69;
v___x_957_ = lean_uint32_dec_eq(v_curr_939_, v___x_956_);
if (v___x_957_ == 0)
{
lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; 
lean_dec(v_nextPos_940_);
v___x_958_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_959_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_960_ = l_Lake_Toml_pushLit(v___x_958_, v_startPos_938_, v___x_959_, v_c_941_, v_s_942_);
return v___x_960_;
}
else
{
goto v___jp_943_;
}
}
else
{
goto v___jp_943_;
}
}
else
{
lean_object* v___f_961_; lean_object* v_s_962_; uint32_t v___x_963_; lean_object* v___x_964_; lean_object* v_s_965_; lean_object* v_errorMsg_966_; lean_object* v___x_967_; uint8_t v___x_968_; 
v___f_961_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0));
v_s_962_ = l_Lean_Parser_ParserState_setPos(v_s_942_, v_nextPos_940_);
v___x_963_ = 95;
v___x_964_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__8));
v_s_965_ = l_Lake_Toml_sepByChar1Fn(v___f_961_, v___x_963_, v___x_964_, v_c_941_, v_s_962_);
v_errorMsg_966_ = lean_ctor_get(v_s_965_, 4);
v___x_967_ = lean_box(0);
v___x_968_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_966_, v___x_967_);
if (v___x_968_ == 0)
{
lean_dec_ref(v_c_941_);
lean_dec(v_startPos_938_);
return v_s_965_;
}
else
{
lean_object* v_s_969_; lean_object* v_errorMsg_970_; uint8_t v___x_971_; 
v_s_969_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(v_c_941_, v_s_965_);
v_errorMsg_970_ = lean_ctor_get(v_s_969_, 4);
v___x_971_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_970_, v___x_967_);
if (v___x_971_ == 0)
{
lean_dec_ref(v_c_941_);
lean_dec(v_startPos_938_);
return v_s_969_;
}
else
{
lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; 
v___x_972_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_973_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_974_ = l_Lake_Toml_pushLit(v___x_972_, v_startPos_938_, v___x_973_, v_c_941_, v_s_969_);
return v___x_974_;
}
}
}
v___jp_943_:
{
lean_object* v_s_944_; lean_object* v_s_945_; lean_object* v_errorMsg_946_; lean_object* v___x_947_; uint8_t v___x_948_; 
v_s_944_ = l_Lean_Parser_ParserState_setPos(v_s_942_, v_nextPos_940_);
v_s_945_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(v_c_941_, v_s_944_);
v_errorMsg_946_ = lean_ctor_get(v_s_945_, 4);
v___x_947_ = lean_box(0);
v___x_948_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_946_, v___x_947_);
if (v___x_948_ == 0)
{
lean_dec_ref(v_c_941_);
lean_dec(v_startPos_938_);
return v_s_945_;
}
else
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; 
v___x_949_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_950_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_951_ = l_Lake_Toml_pushLit(v___x_949_, v_startPos_938_, v___x_950_, v_c_941_, v_s_945_);
return v___x_951_;
}
}
}
}
LEAN_EXPORT void l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_startPos_938_ = stack[0].m_obj;
uint32_t v_curr_939_ = stack[1].m_num;
lean_object* v_nextPos_940_ = stack[2].m_obj;
lean_object* v_c_941_ = stack[3].m_obj;
lean_object* v_s_942_ = stack[4].m_obj;
lean_object* v_res_975_;
v_res_975_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(v_startPos_938_, v_curr_939_, v_nextPos_940_, v_c_941_, v_s_942_);
stack->m_obj
 = v_res_975_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___boxed(lean_object* v_startPos_976_, lean_object* v_curr_977_, lean_object* v_nextPos_978_, lean_object* v_c_979_, lean_object* v_s_980_){
_start:
{
uint32_t v_curr_boxed_981_; lean_object* v_res_982_; 
v_curr_boxed_981_ = lean_unbox_uint32(v_curr_977_);
lean_dec(v_curr_977_);
v_res_982_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(v_startPos_976_, v_curr_boxed_981_, v_nextPos_978_, v_c_979_, v_s_980_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailFn(lean_object* v_startPos_983_, lean_object* v_c_984_, lean_object* v_s_985_){
_start:
{
lean_object* v_toInputContext_986_; lean_object* v_pos_987_; uint8_t v___x_988_; 
v_toInputContext_986_ = lean_ctor_get(v_c_984_, 0);
v_pos_987_ = lean_ctor_get(v_s_985_, 2);
v___x_988_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_986_, v_pos_987_);
if (v___x_988_ == 0)
{
lean_object* v_inputString_989_; uint32_t v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; 
v_inputString_989_ = lean_ctor_get(v_toInputContext_986_, 0);
v___x_990_ = lean_string_utf8_get_fast(v_inputString_989_, v_pos_987_);
v___x_991_ = lean_string_utf8_next_fast(v_inputString_989_, v_pos_987_);
v___x_992_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(v_startPos_983_, v___x_990_, v___x_991_, v_c_984_, v_s_985_);
return v___x_992_;
}
else
{
lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; 
v___x_993_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_994_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_995_ = l_Lake_Toml_pushLit(v___x_993_, v_startPos_983_, v___x_994_, v_c_984_, v_s_985_);
return v___x_995_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(lean_object* v_startPos_1003_, lean_object* v_c_1004_, lean_object* v_s_1005_){
_start:
{
lean_object* v_toInputContext_1006_; lean_object* v_pos_1007_; uint8_t v___x_1008_; 
v_toInputContext_1006_ = lean_ctor_get(v_c_1004_, 0);
v_pos_1007_ = lean_ctor_get(v_s_1005_, 2);
v___x_1008_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1006_, v_pos_1007_);
if (v___x_1008_ == 0)
{
lean_object* v_inputString_1009_; uint32_t v_curr_1010_; uint32_t v___x_1014_; uint8_t v___x_1015_; 
v_inputString_1009_ = lean_ctor_get(v_toInputContext_1006_, 0);
v_curr_1010_ = lean_string_utf8_get_fast(v_inputString_1009_, v_pos_1007_);
v___x_1014_ = 48;
v___x_1015_ = lean_uint32_dec_le(v___x_1014_, v_curr_1010_);
if (v___x_1015_ == 0)
{
goto v___jp_1011_;
}
else
{
uint32_t v___x_1016_; uint8_t v___x_1017_; 
v___x_1016_ = 57;
v___x_1017_ = lean_uint32_dec_le(v_curr_1010_, v___x_1016_);
if (v___x_1017_ == 0)
{
goto v___jp_1011_;
}
else
{
lean_object* v_s_1018_; 
lean_inc(v_pos_1007_);
v_s_1018_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1005_, v_c_1004_, v_pos_1007_);
lean_dec(v_pos_1007_);
v_s_1005_ = v_s_1018_;
goto _start;
}
}
v___jp_1011_:
{
lean_object* v___x_1012_; lean_object* v___x_1013_; 
v___x_1012_ = lean_string_utf8_next_fast(v_inputString_1009_, v_pos_1007_);
v___x_1013_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1003_, v_curr_1010_, v___x_1012_, v_c_1004_, v_s_1005_);
return v___x_1013_;
}
}
else
{
lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; 
v___x_1020_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1021_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1022_ = l_Lake_Toml_pushLit(v___x_1020_, v_startPos_1003_, v___x_1021_, v_c_1004_, v_s_1005_);
return v___x_1022_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn(lean_object* v_startPos_1023_, lean_object* v_c_1024_, lean_object* v_s_1025_){
_start:
{
lean_object* v_pos_1026_; lean_object* v_toInputContext_1027_; lean_object* v_expected_1028_; uint8_t v___x_1029_; 
v_pos_1026_ = lean_ctor_get(v_s_1025_, 2);
v_toInputContext_1027_ = lean_ctor_get(v_c_1024_, 0);
v_expected_1028_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2));
v___x_1029_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1027_, v_pos_1026_);
if (v___x_1029_ == 0)
{
lean_object* v_inputString_1030_; uint8_t v___x_1031_; uint32_t v_curr_1032_; uint32_t v___x_1033_; uint8_t v___x_1034_; 
v_inputString_1030_ = lean_ctor_get(v_toInputContext_1027_, 0);
v___x_1031_ = 1;
v_curr_1032_ = lean_string_utf8_get_fast(v_inputString_1030_, v_pos_1026_);
v___x_1033_ = 48;
v___x_1034_ = lean_uint32_dec_le(v___x_1033_, v_curr_1032_);
if (v___x_1034_ == 0)
{
lean_object* v___x_1035_; 
lean_dec_ref(v_c_1024_);
lean_dec(v_startPos_1023_);
v___x_1035_ = l_Lake_Toml_mkUnexpectedCharError(v_s_1025_, v_curr_1032_, v_expected_1028_, v___x_1031_);
return v___x_1035_;
}
else
{
uint32_t v___x_1036_; uint8_t v___x_1037_; 
v___x_1036_ = 57;
v___x_1037_ = lean_uint32_dec_le(v_curr_1032_, v___x_1036_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; 
lean_dec_ref(v_c_1024_);
lean_dec(v_startPos_1023_);
v___x_1038_ = l_Lake_Toml_mkUnexpectedCharError(v_s_1025_, v_curr_1032_, v_expected_1028_, v___x_1031_);
return v___x_1038_;
}
else
{
lean_object* v_s_1039_; lean_object* v___x_1040_; 
lean_inc(v_pos_1026_);
v_s_1039_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1025_, v_c_1024_, v_pos_1026_);
lean_dec(v_pos_1026_);
v___x_1040_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(v_startPos_1023_, v_c_1024_, v_s_1039_);
return v___x_1040_;
}
}
}
else
{
lean_object* v___x_1041_; 
lean_dec_ref(v_c_1024_);
lean_dec(v_startPos_1023_);
v___x_1041_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1025_, v_expected_1028_);
return v___x_1041_;
}
}
}
lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(lean_object* v_startPos_1042_, uint32_t v_curr_1043_, lean_object* v_nextPos_1044_, lean_object* v_c_1045_, lean_object* v_s_1046_){
_start:
{
uint32_t v___x_1047_; uint8_t v___x_1048_; 
v___x_1047_ = 95;
v___x_1048_ = lean_uint32_dec_eq(v_curr_1043_, v___x_1047_);
if (v___x_1048_ == 0)
{
lean_object* v___x_1049_; 
v___x_1049_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(v_startPos_1042_, v_curr_1043_, v_nextPos_1044_, v_c_1045_, v_s_1046_);
return v___x_1049_;
}
else
{
lean_object* v_s_1050_; lean_object* v___x_1051_; 
v_s_1050_ = l_Lean_Parser_ParserState_setPos(v_s_1046_, v_nextPos_1044_);
v___x_1051_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn(v_startPos_1042_, v_c_1045_, v_s_1050_);
return v___x_1051_;
}
}
}
LEAN_EXPORT void l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_startPos_1042_ = stack[0].m_obj;
uint32_t v_curr_1043_ = stack[1].m_num;
lean_object* v_nextPos_1044_ = stack[2].m_obj;
lean_object* v_c_1045_ = stack[3].m_obj;
lean_object* v_s_1046_ = stack[4].m_obj;
lean_object* v_res_1052_;
v_res_1052_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1042_, v_curr_1043_, v_nextPos_1044_, v_c_1045_, v_s_1046_);
stack->m_obj
 = v_res_1052_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn___boxed(lean_object* v_startPos_1053_, lean_object* v_curr_1054_, lean_object* v_nextPos_1055_, lean_object* v_c_1056_, lean_object* v_s_1057_){
_start:
{
uint32_t v_curr_boxed_1058_; lean_object* v_res_1059_; 
v_curr_boxed_1058_ = lean_unbox_uint32(v_curr_1054_);
lean_dec(v_curr_1054_);
v_res_1059_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1053_, v_curr_boxed_1058_, v_nextPos_1055_, v_c_1056_, v_s_1057_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(lean_object* v_startPos_1065_, lean_object* v_a_1066_, lean_object* v_a_1067_){
_start:
{
lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v_s_1070_; lean_object* v_errorMsg_1071_; lean_object* v___x_1072_; uint8_t v___x_1073_; 
v___x_1068_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__0));
v___x_1069_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__2));
lean_inc_ref(v_a_1066_);
v_s_1070_ = l_Lake_Toml_strFn(v___x_1068_, v___x_1069_, v_a_1066_, v_a_1067_);
v_errorMsg_1071_ = lean_ctor_get(v_s_1070_, 4);
v___x_1072_ = lean_box(0);
v___x_1073_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1071_, v___x_1072_);
if (v___x_1073_ == 0)
{
lean_dec_ref(v_a_1066_);
lean_dec(v_startPos_1065_);
return v_s_1070_;
}
else
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; 
v___x_1074_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_1075_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1076_ = l_Lake_Toml_pushLit(v___x_1074_, v_startPos_1065_, v___x_1075_, v_a_1066_, v_s_1070_);
return v___x_1076_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(lean_object* v_startPos_1082_, lean_object* v_a_1083_, lean_object* v_a_1084_){
_start:
{
lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v_s_1087_; lean_object* v_errorMsg_1088_; lean_object* v___x_1089_; uint8_t v___x_1090_; 
v___x_1085_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__0));
v___x_1086_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__2));
lean_inc_ref(v_a_1083_);
v_s_1087_ = l_Lake_Toml_strFn(v___x_1085_, v___x_1086_, v_a_1083_, v_a_1084_);
v_errorMsg_1088_ = lean_ctor_get(v_s_1087_, 4);
v___x_1089_ = lean_box(0);
v___x_1090_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1088_, v___x_1089_);
if (v___x_1090_ == 0)
{
lean_dec_ref(v_a_1083_);
lean_dec(v_startPos_1082_);
return v_s_1087_;
}
else
{
lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; 
v___x_1091_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_1092_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1093_ = l_Lake_Toml_pushLit(v___x_1091_, v_startPos_1082_, v___x_1092_, v_a_1083_, v_s_1087_);
return v___x_1093_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decimalFn(lean_object* v_startPos_1094_, lean_object* v_c_1095_, lean_object* v_s_1096_){
_start:
{
lean_object* v_toInputContext_1097_; lean_object* v_pos_1098_; lean_object* v_expected_1099_; uint8_t v___x_1100_; 
v_toInputContext_1097_ = lean_ctor_get(v_c_1095_, 0);
v_pos_1098_ = lean_ctor_get(v_s_1096_, 2);
v_expected_1099_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2));
v___x_1100_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1097_, v_pos_1098_);
if (v___x_1100_ == 0)
{
lean_object* v_inputString_1101_; uint32_t v_curr_1102_; uint32_t v___x_1103_; uint8_t v___x_1104_; 
v_inputString_1101_ = lean_ctor_get(v_toInputContext_1097_, 0);
v_curr_1102_ = lean_string_utf8_get_fast(v_inputString_1101_, v_pos_1098_);
v___x_1103_ = 48;
v___x_1104_ = lean_uint32_dec_eq(v_curr_1102_, v___x_1103_);
if (v___x_1104_ == 0)
{
uint8_t v___x_1105_; uint8_t v___x_1116_; 
v___x_1105_ = 1;
v___x_1116_ = lean_uint32_dec_le(v___x_1103_, v_curr_1102_);
if (v___x_1116_ == 0)
{
goto v___jp_1106_;
}
else
{
uint32_t v___x_1117_; uint8_t v___x_1118_; 
v___x_1117_ = 57;
v___x_1118_ = lean_uint32_dec_le(v_curr_1102_, v___x_1117_);
if (v___x_1118_ == 0)
{
goto v___jp_1106_;
}
else
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_inc(v_pos_1098_);
v___x_1119_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1096_, v_c_1095_, v_pos_1098_);
lean_dec(v_pos_1098_);
v___x_1120_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(v_startPos_1094_, v_c_1095_, v___x_1119_);
return v___x_1120_;
}
}
v___jp_1106_:
{
uint32_t v___x_1107_; uint8_t v___x_1108_; 
v___x_1107_ = 105;
v___x_1108_ = lean_uint32_dec_eq(v_curr_1102_, v___x_1107_);
if (v___x_1108_ == 0)
{
uint32_t v___x_1109_; uint8_t v___x_1110_; 
v___x_1109_ = 110;
v___x_1110_ = lean_uint32_dec_eq(v_curr_1102_, v___x_1109_);
if (v___x_1110_ == 0)
{
lean_object* v___x_1111_; 
lean_dec_ref(v_c_1095_);
lean_dec(v_startPos_1094_);
v___x_1111_ = l_Lake_Toml_mkUnexpectedCharError(v_s_1096_, v_curr_1102_, v_expected_1099_, v___x_1105_);
return v___x_1111_;
}
else
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
lean_inc(v_pos_1098_);
v___x_1112_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1096_, v_c_1095_, v_pos_1098_);
lean_dec(v_pos_1098_);
v___x_1113_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(v_startPos_1094_, v_c_1095_, v___x_1112_);
return v___x_1113_;
}
}
else
{
lean_object* v___x_1114_; lean_object* v___x_1115_; 
lean_inc(v_pos_1098_);
v___x_1114_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1096_, v_c_1095_, v_pos_1098_);
lean_dec(v_pos_1098_);
v___x_1115_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(v_startPos_1094_, v_c_1095_, v___x_1114_);
return v___x_1115_;
}
}
}
else
{
lean_object* v___x_1121_; lean_object* v___x_1122_; 
lean_inc(v_pos_1098_);
v___x_1121_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1096_, v_c_1095_, v_pos_1098_);
lean_dec(v_pos_1098_);
v___x_1122_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailFn(v_startPos_1094_, v_c_1095_, v___x_1121_);
return v___x_1122_;
}
}
else
{
lean_object* v___x_1123_; 
lean_dec_ref(v_c_1095_);
lean_dec(v_startPos_1094_);
v___x_1123_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1096_, v_expected_1099_);
return v___x_1123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn(lean_object* v_startPos_1139_, lean_object* v_c_1140_, lean_object* v_s_1141_){
_start:
{
lean_object* v_toInputContext_1142_; lean_object* v_pos_1143_; uint8_t v___x_1144_; 
v_toInputContext_1142_ = lean_ctor_get(v_c_1140_, 0);
v_pos_1143_ = lean_ctor_get(v_s_1141_, 2);
v___x_1144_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1142_, v_pos_1143_);
if (v___x_1144_ == 0)
{
lean_object* v_inputString_1145_; uint32_t v_curr_1146_; lean_object* v_nextPos_1147_; uint32_t v___x_1148_; uint8_t v___x_1149_; 
v_inputString_1145_ = lean_ctor_get(v_toInputContext_1142_, 0);
v_curr_1146_ = lean_string_utf8_get_fast(v_inputString_1145_, v_pos_1143_);
v_nextPos_1147_ = lean_string_utf8_next_fast(v_inputString_1145_, v_pos_1143_);
v___x_1148_ = 48;
v___x_1149_ = lean_uint32_dec_le(v___x_1148_, v_curr_1146_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; 
v___x_1150_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1139_, v_curr_1146_, v_nextPos_1147_, v_c_1140_, v_s_1141_);
return v___x_1150_;
}
else
{
uint32_t v___x_1151_; uint8_t v___x_1152_; 
v___x_1151_ = 57;
v___x_1152_ = lean_uint32_dec_le(v_curr_1146_, v___x_1151_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; 
v___x_1153_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1139_, v_curr_1146_, v_nextPos_1147_, v_c_1140_, v_s_1141_);
return v___x_1153_;
}
else
{
lean_object* v_s_1154_; lean_object* v_pos_1155_; uint8_t v___x_1156_; 
v_s_1154_ = l_Lean_Parser_ParserState_setPos(v_s_1141_, v_nextPos_1147_);
v_pos_1155_ = lean_ctor_get(v_s_1154_, 2);
v___x_1156_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1142_, v_pos_1155_);
if (v___x_1156_ == 0)
{
uint32_t v_curr_1157_; lean_object* v_nextPos_1158_; uint32_t v___x_1159_; uint8_t v___x_1160_; 
v_curr_1157_ = lean_string_utf8_get_fast(v_inputString_1145_, v_pos_1155_);
v_nextPos_1158_ = lean_string_utf8_next_fast(v_inputString_1145_, v_pos_1155_);
v___x_1159_ = 58;
v___x_1160_ = lean_uint32_dec_eq(v_curr_1157_, v___x_1159_);
if (v___x_1160_ == 0)
{
uint8_t v___x_1161_; 
v___x_1161_ = lean_uint32_dec_le(v___x_1148_, v_curr_1157_);
if (v___x_1161_ == 0)
{
lean_object* v___x_1162_; 
v___x_1162_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1139_, v_curr_1157_, v_nextPos_1158_, v_c_1140_, v_s_1154_);
return v___x_1162_;
}
else
{
uint8_t v___x_1163_; 
v___x_1163_ = lean_uint32_dec_le(v_curr_1157_, v___x_1151_);
if (v___x_1163_ == 0)
{
lean_object* v___x_1164_; 
v___x_1164_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1139_, v_curr_1157_, v_nextPos_1158_, v_c_1140_, v_s_1154_);
return v___x_1164_;
}
else
{
lean_object* v_s_1165_; lean_object* v_pos_1166_; uint8_t v___x_1167_; 
v_s_1165_ = l_Lean_Parser_ParserState_setPos(v_s_1154_, v_nextPos_1158_);
v_pos_1166_ = lean_ctor_get(v_s_1165_, 2);
v___x_1167_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1142_, v_pos_1166_);
if (v___x_1167_ == 0)
{
uint32_t v_curr_1168_; lean_object* v_nextPos_1169_; uint8_t v___x_1170_; 
v_curr_1168_ = lean_string_utf8_get_fast(v_inputString_1145_, v_pos_1166_);
v_nextPos_1169_ = lean_string_utf8_next_fast(v_inputString_1145_, v_pos_1166_);
v___x_1170_ = lean_uint32_dec_le(v___x_1148_, v_curr_1168_);
if (v___x_1170_ == 0)
{
lean_object* v___x_1171_; 
v___x_1171_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1139_, v_curr_1168_, v_nextPos_1169_, v_c_1140_, v_s_1165_);
return v___x_1171_;
}
else
{
uint8_t v___x_1172_; 
v___x_1172_ = lean_uint32_dec_le(v_curr_1168_, v___x_1151_);
if (v___x_1172_ == 0)
{
lean_object* v___x_1173_; 
v___x_1173_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1139_, v_curr_1168_, v_nextPos_1169_, v_c_1140_, v_s_1165_);
return v___x_1173_;
}
else
{
lean_object* v_s_1174_; uint8_t v___x_1175_; 
v_s_1174_ = l_Lean_Parser_ParserState_setPos(v_s_1165_, v_nextPos_1169_);
v___x_1175_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1142_, v_nextPos_1169_);
if (v___x_1175_ == 0)
{
lean_object* v_pos_1176_; uint32_t v_curr_1177_; lean_object* v_nextPos_1178_; uint32_t v___x_1179_; uint8_t v___x_1180_; 
v_pos_1176_ = lean_ctor_get(v_s_1174_, 2);
v_curr_1177_ = lean_string_utf8_get_fast(v_inputString_1145_, v_pos_1176_);
v_nextPos_1178_ = lean_string_utf8_next_fast(v_inputString_1145_, v_pos_1176_);
v___x_1179_ = 45;
v___x_1180_ = lean_uint32_dec_eq(v_curr_1177_, v___x_1179_);
if (v___x_1180_ == 0)
{
uint8_t v___x_1181_; 
v___x_1181_ = lean_uint32_dec_le(v___x_1148_, v_curr_1177_);
if (v___x_1181_ == 0)
{
lean_object* v___x_1182_; 
v___x_1182_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1139_, v_curr_1177_, v_nextPos_1178_, v_c_1140_, v_s_1174_);
return v___x_1182_;
}
else
{
uint8_t v___x_1183_; 
v___x_1183_ = lean_uint32_dec_le(v_curr_1177_, v___x_1151_);
if (v___x_1183_ == 0)
{
lean_object* v___x_1184_; 
v___x_1184_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1139_, v_curr_1177_, v_nextPos_1178_, v_c_1140_, v_s_1174_);
return v___x_1184_;
}
else
{
lean_object* v_s_1185_; lean_object* v___x_1186_; 
v_s_1185_ = l_Lean_Parser_ParserState_setPos(v_s_1174_, v_nextPos_1178_);
v___x_1186_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(v_startPos_1139_, v_c_1140_, v_s_1185_);
return v___x_1186_;
}
}
}
else
{
lean_object* v_s_1187_; lean_object* v_s_1188_; lean_object* v_errorMsg_1189_; lean_object* v___x_1190_; uint8_t v___x_1191_; 
v_s_1187_ = l_Lean_Parser_ParserState_setPos(v_s_1174_, v_nextPos_1178_);
v_s_1188_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(v_c_1140_, v_s_1187_);
v_errorMsg_1189_ = lean_ctor_get(v_s_1188_, 4);
v___x_1190_ = lean_box(0);
v___x_1191_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1189_, v___x_1190_);
if (v___x_1191_ == 0)
{
lean_dec_ref(v_c_1140_);
lean_dec(v_startPos_1139_);
return v_s_1188_;
}
else
{
if (v___x_1175_ == 0)
{
lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; 
v___x_1192_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_1193_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1194_ = l_Lake_Toml_pushLit(v___x_1192_, v_startPos_1139_, v___x_1193_, v_c_1140_, v_s_1188_);
return v___x_1194_;
}
else
{
lean_dec_ref(v_c_1140_);
lean_dec(v_startPos_1139_);
return v_s_1188_;
}
}
}
}
else
{
lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; 
v___x_1195_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1196_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1197_ = l_Lake_Toml_pushLit(v___x_1195_, v_startPos_1139_, v___x_1196_, v_c_1140_, v_s_1174_);
return v___x_1197_;
}
}
}
}
else
{
lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; 
v___x_1198_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1199_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1200_ = l_Lake_Toml_pushLit(v___x_1198_, v_startPos_1139_, v___x_1199_, v_c_1140_, v_s_1165_);
return v___x_1200_;
}
}
}
}
else
{
lean_object* v_s_1201_; lean_object* v_s_1202_; lean_object* v_errorMsg_1203_; lean_object* v___x_1204_; uint8_t v___x_1205_; 
v_s_1201_ = l_Lean_Parser_ParserState_setPos(v_s_1154_, v_nextPos_1158_);
v_s_1202_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(v___x_1156_, v_c_1140_, v_s_1201_);
v_errorMsg_1203_ = lean_ctor_get(v_s_1202_, 4);
v___x_1204_ = lean_box(0);
v___x_1205_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1203_, v___x_1204_);
if (v___x_1205_ == 0)
{
lean_dec_ref(v_c_1140_);
lean_dec(v_startPos_1139_);
return v_s_1202_;
}
else
{
if (v___x_1156_ == 0)
{
lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; 
v___x_1206_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_1207_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1208_ = l_Lake_Toml_pushLit(v___x_1206_, v_startPos_1139_, v___x_1207_, v_c_1140_, v_s_1202_);
return v___x_1208_;
}
else
{
lean_dec_ref(v_c_1140_);
lean_dec(v_startPos_1139_);
return v_s_1202_;
}
}
}
}
else
{
lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; 
v___x_1209_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1210_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1211_ = l_Lake_Toml_pushLit(v___x_1209_, v_startPos_1139_, v___x_1210_, v_c_1140_, v_s_1154_);
return v___x_1211_;
}
}
}
}
else
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
lean_dec_ref(v_c_1140_);
lean_dec(v_startPos_1139_);
v___x_1212_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__5));
v___x_1213_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1141_, v___x_1212_);
return v___x_1213_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralFn___lam__0(lean_object* v_c_1251_, lean_object* v_s_1252_){
_start:
{
lean_object* v_pos_1253_; lean_object* v___y_1258_; lean_object* v_toInputContext_1265_; lean_object* v_expected_1266_; uint8_t v___x_1267_; 
v_pos_1253_ = lean_ctor_get(v_s_1252_, 2);
v_toInputContext_1265_ = lean_ctor_get(v_c_1251_, 0);
v_expected_1266_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__1));
v___x_1267_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1265_, v_pos_1253_);
if (v___x_1267_ == 0)
{
lean_object* v_inputString_1268_; uint32_t v_curr_1269_; uint32_t v___x_1270_; uint8_t v___x_1271_; 
v_inputString_1268_ = lean_ctor_get(v_toInputContext_1265_, 0);
v_curr_1269_ = lean_string_utf8_get_fast(v_inputString_1268_, v_pos_1253_);
v___x_1270_ = 48;
v___x_1271_ = lean_uint32_dec_eq(v_curr_1269_, v___x_1270_);
if (v___x_1271_ == 0)
{
uint8_t v___x_1272_; uint8_t v___x_1293_; 
v___x_1272_ = 1;
v___x_1293_ = lean_uint32_dec_le(v___x_1270_, v_curr_1269_);
if (v___x_1293_ == 0)
{
goto v___jp_1273_;
}
else
{
uint32_t v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = 57;
v___x_1295_ = lean_uint32_dec_le(v_curr_1269_, v___x_1294_);
if (v___x_1295_ == 0)
{
goto v___jp_1273_;
}
else
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
lean_inc(v_pos_1253_);
v___x_1296_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1252_, v_c_1251_, v_pos_1253_);
v___x_1297_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn(v_pos_1253_, v_c_1251_, v___x_1296_);
return v___x_1297_;
}
}
v___jp_1273_:
{
uint32_t v___x_1274_; uint8_t v___x_1275_; 
v___x_1274_ = 43;
v___x_1275_ = lean_uint32_dec_eq(v_curr_1269_, v___x_1274_);
if (v___x_1275_ == 0)
{
uint32_t v___x_1276_; uint8_t v___x_1277_; 
v___x_1276_ = 45;
v___x_1277_ = lean_uint32_dec_eq(v_curr_1269_, v___x_1276_);
if (v___x_1277_ == 0)
{
uint32_t v___x_1278_; uint8_t v___x_1279_; 
v___x_1278_ = 105;
v___x_1279_ = lean_uint32_dec_eq(v_curr_1269_, v___x_1278_);
if (v___x_1279_ == 0)
{
uint32_t v___x_1280_; uint8_t v___x_1281_; 
v___x_1280_ = 110;
v___x_1281_ = lean_uint32_dec_eq(v_curr_1269_, v___x_1280_);
if (v___x_1281_ == 0)
{
lean_object* v___x_1282_; lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
lean_dec_ref(v_c_1251_);
v___x_1282_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__2));
v___x_1283_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__3));
v___x_1284_ = lean_string_push(v___x_1283_, v_curr_1269_);
v___x_1285_ = lean_string_append(v___x_1282_, v___x_1284_);
lean_dec_ref(v___x_1284_);
v___x_1286_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__4));
v___x_1287_ = lean_string_append(v___x_1285_, v___x_1286_);
v___x_1288_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1252_, v___x_1287_, v_expected_1266_, v___x_1272_);
return v___x_1288_;
}
else
{
lean_object* v___x_1289_; lean_object* v___x_1290_; 
lean_inc(v_pos_1253_);
v___x_1289_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1252_, v_c_1251_, v_pos_1253_);
v___x_1290_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(v_pos_1253_, v_c_1251_, v___x_1289_);
return v___x_1290_;
}
}
else
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
lean_inc(v_pos_1253_);
v___x_1291_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1252_, v_c_1251_, v_pos_1253_);
v___x_1292_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(v_pos_1253_, v_c_1251_, v___x_1291_);
return v___x_1292_;
}
}
else
{
lean_inc(v_pos_1253_);
goto v___jp_1254_;
}
}
else
{
lean_inc(v_pos_1253_);
goto v___jp_1254_;
}
}
}
else
{
lean_object* v_s_1298_; lean_object* v_pos_1299_; uint8_t v___x_1300_; 
lean_inc(v_pos_1253_);
v_s_1298_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1252_, v_c_1251_, v_pos_1253_);
v_pos_1299_ = lean_ctor_get(v_s_1298_, 2);
v___x_1300_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1265_, v_pos_1299_);
if (v___x_1300_ == 0)
{
uint32_t v_curr_1301_; uint32_t v___x_1305_; uint8_t v___x_1306_; 
v_curr_1301_ = lean_string_utf8_get_fast(v_inputString_1268_, v_pos_1299_);
v___x_1305_ = 98;
v___x_1306_ = lean_uint32_dec_eq(v_curr_1301_, v___x_1305_);
if (v___x_1306_ == 0)
{
uint32_t v___x_1307_; uint8_t v___x_1308_; 
v___x_1307_ = 111;
v___x_1308_ = lean_uint32_dec_eq(v_curr_1301_, v___x_1307_);
if (v___x_1308_ == 0)
{
uint32_t v___x_1309_; uint8_t v___x_1310_; 
v___x_1309_ = 120;
v___x_1310_ = lean_uint32_dec_eq(v_curr_1301_, v___x_1309_);
if (v___x_1310_ == 0)
{
uint8_t v___x_1311_; 
v___x_1311_ = lean_uint32_dec_le(v___x_1270_, v_curr_1301_);
if (v___x_1311_ == 0)
{
goto v___jp_1302_;
}
else
{
uint32_t v___x_1312_; uint8_t v___x_1313_; 
v___x_1312_ = 57;
v___x_1313_ = lean_uint32_dec_le(v_curr_1301_, v___x_1312_);
if (v___x_1313_ == 0)
{
goto v___jp_1302_;
}
else
{
lean_object* v_s_1314_; uint32_t v___x_1315_; lean_object* v___x_1316_; lean_object* v_s_1317_; lean_object* v_errorMsg_1318_; lean_object* v___x_1319_; uint8_t v___x_1320_; 
lean_inc(v_pos_1299_);
v_s_1314_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1298_, v_c_1251_, v_pos_1299_);
lean_dec(v_pos_1299_);
v___x_1315_ = 58;
v___x_1316_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v_s_1317_ = l_Lake_Toml_chFn(v___x_1315_, v___x_1316_, v_c_1251_, v_s_1314_);
v_errorMsg_1318_ = lean_ctor_get(v_s_1317_, 4);
v___x_1319_ = lean_box(0);
v___x_1320_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1318_, v___x_1319_);
if (v___x_1320_ == 0)
{
v___y_1258_ = v_s_1317_;
goto v___jp_1257_;
}
else
{
lean_object* v___x_1321_; 
v___x_1321_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(v___x_1310_, v_c_1251_, v_s_1317_);
v___y_1258_ = v___x_1321_;
goto v___jp_1257_;
}
}
}
}
else
{
lean_object* v_s_1322_; lean_object* v___x_1323_; uint32_t v___x_1324_; lean_object* v___x_1325_; lean_object* v_s_1326_; lean_object* v_errorMsg_1327_; lean_object* v___x_1328_; uint8_t v___x_1329_; 
lean_inc(v_pos_1299_);
v_s_1322_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1298_, v_c_1251_, v_pos_1299_);
lean_dec(v_pos_1299_);
v___x_1323_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__5));
v___x_1324_ = 95;
v___x_1325_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__7));
v_s_1326_ = l_Lake_Toml_sepByChar1Fn(v___x_1323_, v___x_1324_, v___x_1325_, v_c_1251_, v_s_1322_);
v_errorMsg_1327_ = lean_ctor_get(v_s_1326_, 4);
v___x_1328_ = lean_box(0);
v___x_1329_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1327_, v___x_1328_);
if (v___x_1329_ == 0)
{
lean_dec(v_pos_1253_);
lean_dec_ref(v_c_1251_);
return v_s_1326_;
}
else
{
lean_object* v___x_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; 
v___x_1330_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__9));
v___x_1331_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1332_ = l_Lake_Toml_pushLit(v___x_1330_, v_pos_1253_, v___x_1331_, v_c_1251_, v_s_1326_);
return v___x_1332_;
}
}
}
else
{
lean_object* v_s_1333_; lean_object* v___x_1334_; uint32_t v___x_1335_; lean_object* v___x_1336_; lean_object* v_s_1337_; lean_object* v_errorMsg_1338_; lean_object* v___x_1339_; uint8_t v___x_1340_; 
lean_inc(v_pos_1299_);
v_s_1333_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1298_, v_c_1251_, v_pos_1299_);
lean_dec(v_pos_1299_);
v___x_1334_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__10));
v___x_1335_ = 95;
v___x_1336_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__12));
v_s_1337_ = l_Lake_Toml_sepByChar1Fn(v___x_1334_, v___x_1335_, v___x_1336_, v_c_1251_, v_s_1333_);
v_errorMsg_1338_ = lean_ctor_get(v_s_1337_, 4);
v___x_1339_ = lean_box(0);
v___x_1340_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1338_, v___x_1339_);
if (v___x_1340_ == 0)
{
lean_dec(v_pos_1253_);
lean_dec_ref(v_c_1251_);
return v_s_1337_;
}
else
{
lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; 
v___x_1341_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__14));
v___x_1342_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1343_ = l_Lake_Toml_pushLit(v___x_1341_, v_pos_1253_, v___x_1342_, v_c_1251_, v_s_1337_);
return v___x_1343_;
}
}
}
else
{
lean_object* v_s_1344_; lean_object* v___x_1345_; uint32_t v___x_1346_; lean_object* v___x_1347_; lean_object* v_s_1348_; lean_object* v_errorMsg_1349_; lean_object* v___x_1350_; uint8_t v___x_1351_; 
lean_inc(v_pos_1299_);
v_s_1344_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1298_, v_c_1251_, v_pos_1299_);
lean_dec(v_pos_1299_);
v___x_1345_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__15));
v___x_1346_ = 95;
v___x_1347_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__17));
v_s_1348_ = l_Lake_Toml_sepByChar1Fn(v___x_1345_, v___x_1346_, v___x_1347_, v_c_1251_, v_s_1344_);
v_errorMsg_1349_ = lean_ctor_get(v_s_1348_, 4);
v___x_1350_ = lean_box(0);
v___x_1351_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1349_, v___x_1350_);
if (v___x_1351_ == 0)
{
lean_dec(v_pos_1253_);
lean_dec_ref(v_c_1251_);
return v_s_1348_;
}
else
{
if (v___x_1300_ == 0)
{
lean_object* v___x_1352_; lean_object* v___x_1353_; lean_object* v___x_1354_; 
v___x_1352_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__19));
v___x_1353_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1354_ = l_Lake_Toml_pushLit(v___x_1352_, v_pos_1253_, v___x_1353_, v_c_1251_, v_s_1348_);
return v___x_1354_;
}
else
{
lean_dec(v_pos_1253_);
lean_dec_ref(v_c_1251_);
return v_s_1348_;
}
}
}
v___jp_1302_:
{
lean_object* v___x_1303_; lean_object* v___x_1304_; 
v___x_1303_ = lean_string_utf8_next_fast(v_inputString_1268_, v_pos_1299_);
v___x_1304_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(v_pos_1253_, v_curr_1301_, v___x_1303_, v_c_1251_, v_s_1298_);
return v___x_1304_;
}
}
else
{
lean_object* v___x_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1355_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1356_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1357_ = l_Lake_Toml_pushLit(v___x_1355_, v_pos_1253_, v___x_1356_, v_c_1251_, v_s_1298_);
return v___x_1357_;
}
}
}
else
{
lean_object* v___x_1358_; 
lean_dec_ref(v_c_1251_);
v___x_1358_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1252_, v_expected_1266_);
return v___x_1358_;
}
v___jp_1254_:
{
lean_object* v___x_1255_; lean_object* v___x_1256_; 
v___x_1255_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1252_, v_c_1251_, v_pos_1253_);
v___x_1256_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decimalFn(v_pos_1253_, v_c_1251_, v___x_1255_);
return v___x_1256_;
}
v___jp_1257_:
{
lean_object* v_errorMsg_1259_; lean_object* v___x_1260_; uint8_t v___x_1261_; 
v_errorMsg_1259_ = lean_ctor_get(v___y_1258_, 4);
v___x_1260_ = lean_box(0);
v___x_1261_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1259_, v___x_1260_);
if (v___x_1261_ == 0)
{
lean_dec(v_pos_1253_);
lean_dec_ref(v_c_1251_);
return v___y_1258_;
}
else
{
lean_object* v___x_1262_; lean_object* v___x_1263_; lean_object* v___x_1264_; 
v___x_1262_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_1263_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1264_ = l_Lake_Toml_pushLit(v___x_1262_, v_pos_1253_, v___x_1263_, v_c_1251_, v___y_1258_);
return v___x_1264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralFn(lean_object* v_a_1360_, lean_object* v_a_1361_){
_start:
{
lean_object* v___f_1362_; lean_object* v___x_1363_; 
v___f_1362_ = ((lean_object*)(l_Lake_Toml_numeralFn___closed__0));
v___x_1363_ = l_Lean_Parser_atomicFn(v___f_1362_, v_a_1360_, v_a_1361_);
return v___x_1363_;
}
}
static lean_object* _init_l_Lake_Toml_trailingWs___closed__0(void){
_start:
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
v___x_1364_ = lean_alloc_closure((void*)(l_Lake_Toml_wsFn___boxed), 2, 0);
v___x_1365_ = l_Lake_Toml_trailing(v___x_1364_);
return v___x_1365_;
}
}
static lean_object* _init_l_Lake_Toml_trailingWs(void){
_start:
{
lean_object* v___x_1366_; 
v___x_1366_ = lean_obj_once(&l_Lake_Toml_trailingWs___closed__0, &l_Lake_Toml_trailingWs___closed__0_once, _init_l_Lake_Toml_trailingWs___closed__0);
return v___x_1366_;
}
}
static lean_object* _init_l_Lake_Toml_trailingSep___closed__1(void){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1369_ = l_Lake_Toml_trailing(v___x_1368_);
return v___x_1369_;
}
}
static lean_object* _init_l_Lake_Toml_trailingSep(void){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = lean_obj_once(&l_Lake_Toml_trailingSep___closed__1, &l_Lake_Toml_trailingSep___closed__1_once, _init_l_Lake_Toml_trailingSep___closed__1);
return v___x_1370_;
}
}
uint8_t l_Lake_Toml_unquotedKeyFn___lam__0(uint32_t v_c_1371_){
_start:
{
uint32_t v___x_1387_; uint8_t v___x_1388_; 
v___x_1387_ = 65;
v___x_1388_ = lean_uint32_dec_le(v___x_1387_, v_c_1371_);
if (v___x_1388_ == 0)
{
goto v___jp_1382_;
}
else
{
uint32_t v___x_1389_; uint8_t v___x_1390_; 
v___x_1389_ = 90;
v___x_1390_ = lean_uint32_dec_le(v_c_1371_, v___x_1389_);
if (v___x_1390_ == 0)
{
goto v___jp_1382_;
}
else
{
return v___x_1390_;
}
}
v___jp_1372_:
{
uint32_t v___x_1373_; uint8_t v___x_1374_; 
v___x_1373_ = 95;
v___x_1374_ = lean_uint32_dec_eq(v_c_1371_, v___x_1373_);
if (v___x_1374_ == 0)
{
uint32_t v___x_1375_; uint8_t v___x_1376_; 
v___x_1375_ = 45;
v___x_1376_ = lean_uint32_dec_eq(v_c_1371_, v___x_1375_);
return v___x_1376_;
}
else
{
return v___x_1374_;
}
}
v___jp_1377_:
{
uint32_t v___x_1378_; uint8_t v___x_1379_; 
v___x_1378_ = 48;
v___x_1379_ = lean_uint32_dec_le(v___x_1378_, v_c_1371_);
if (v___x_1379_ == 0)
{
goto v___jp_1372_;
}
else
{
uint32_t v___x_1380_; uint8_t v___x_1381_; 
v___x_1380_ = 57;
v___x_1381_ = lean_uint32_dec_le(v_c_1371_, v___x_1380_);
if (v___x_1381_ == 0)
{
goto v___jp_1372_;
}
else
{
return v___x_1381_;
}
}
}
v___jp_1382_:
{
uint32_t v___x_1383_; uint8_t v___x_1384_; 
v___x_1383_ = 97;
v___x_1384_ = lean_uint32_dec_le(v___x_1383_, v_c_1371_);
if (v___x_1384_ == 0)
{
goto v___jp_1377_;
}
else
{
uint32_t v___x_1385_; uint8_t v___x_1386_; 
v___x_1385_ = 122;
v___x_1386_ = lean_uint32_dec_le(v_c_1371_, v___x_1385_);
if (v___x_1386_ == 0)
{
goto v___jp_1377_;
}
else
{
return v___x_1386_;
}
}
}
}
}
LEAN_EXPORT void l_Lake_Toml_unquotedKeyFn___lam__0_0interp(lean_interpreter_value* stack)
{
uint32_t v_c_1371_ = stack[0].m_num;
uint8_t v_res_1391_;
v_res_1391_ = l_Lake_Toml_unquotedKeyFn___lam__0(v_c_1371_);
stack->m_num = v_res_1391_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn___lam__0___boxed(lean_object* v_c_1392_){
_start:
{
uint32_t v_c_boxed_1393_; uint8_t v_res_1394_; lean_object* v_r_1395_; 
v_c_boxed_1393_ = lean_unbox_uint32(v_c_1392_);
lean_dec(v_c_1392_);
v_res_1394_ = l_Lake_Toml_unquotedKeyFn___lam__0(v_c_boxed_1393_);
v_r_1395_ = lean_box(v_res_1394_);
return v_r_1395_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn(lean_object* v_a_1401_, lean_object* v_a_1402_){
_start:
{
lean_object* v___f_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; 
v___f_1403_ = ((lean_object*)(l_Lake_Toml_unquotedKeyFn___closed__0));
v___x_1404_ = ((lean_object*)(l_Lake_Toml_unquotedKeyFn___closed__2));
v___x_1405_ = l_Lake_Toml_takeWhile1Fn(v___f_1403_, v___x_1404_, v_a_1401_, v_a_1402_);
return v___x_1405_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn___boxed(lean_object* v_a_1406_, lean_object* v_a_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_Lake_Toml_unquotedKeyFn(v_a_1406_, v_a_1407_);
lean_dec_ref(v_a_1406_);
return v_res_1408_;
}
}
static lean_object* _init_l_Lake_Toml_unquotedKey___closed__2(void){
_start:
{
uint8_t v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1414_ = 0;
v___x_1415_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1416_ = lean_alloc_closure((void*)(l_Lake_Toml_unquotedKeyFn___boxed), 2, 0);
v___x_1417_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__1));
v___x_1418_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__0));
v___x_1419_ = l_Lake_Toml_litWithAntiquot(v___x_1418_, v___x_1417_, v___x_1416_, v___x_1415_, v___x_1414_);
return v___x_1419_;
}
}
static lean_object* _init_l_Lake_Toml_unquotedKey(void){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = lean_obj_once(&l_Lake_Toml_unquotedKey___closed__2, &l_Lake_Toml_unquotedKey___closed__2_once, _init_l_Lake_Toml_unquotedKey___closed__2);
return v___x_1420_;
}
}
static lean_object* _init_l_Lake_Toml_basicString___closed__2(void){
_start:
{
uint8_t v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1426_ = 0;
v___x_1427_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1428_ = lean_alloc_closure((void*)(l_Lake_Toml_basicStringFn), 2, 0);
v___x_1429_ = ((lean_object*)(l_Lake_Toml_basicString___closed__1));
v___x_1430_ = ((lean_object*)(l_Lake_Toml_basicString___closed__0));
v___x_1431_ = l_Lake_Toml_litWithAntiquot(v___x_1430_, v___x_1429_, v___x_1428_, v___x_1427_, v___x_1426_);
return v___x_1431_;
}
}
static lean_object* _init_l_Lake_Toml_basicString(void){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = lean_obj_once(&l_Lake_Toml_basicString___closed__2, &l_Lake_Toml_basicString___closed__2_once, _init_l_Lake_Toml_basicString___closed__2);
return v___x_1432_;
}
}
static lean_object* _init_l_Lake_Toml_literalString___closed__2(void){
_start:
{
uint8_t v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1438_ = 0;
v___x_1439_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1440_ = lean_alloc_closure((void*)(l_Lake_Toml_literalStringFn___boxed), 2, 0);
v___x_1441_ = ((lean_object*)(l_Lake_Toml_literalString___closed__1));
v___x_1442_ = ((lean_object*)(l_Lake_Toml_literalString___closed__0));
v___x_1443_ = l_Lake_Toml_litWithAntiquot(v___x_1442_, v___x_1441_, v___x_1440_, v___x_1439_, v___x_1438_);
return v___x_1443_;
}
}
static lean_object* _init_l_Lake_Toml_literalString(void){
_start:
{
lean_object* v___x_1444_; 
v___x_1444_ = lean_obj_once(&l_Lake_Toml_literalString___closed__2, &l_Lake_Toml_literalString___closed__2_once, _init_l_Lake_Toml_literalString___closed__2);
return v___x_1444_;
}
}
static lean_object* _init_l_Lake_Toml_mlBasicString___closed__2(void){
_start:
{
uint8_t v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1450_ = 0;
v___x_1451_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1452_ = lean_alloc_closure((void*)(l_Lake_Toml_mlBasicStringFn), 2, 0);
v___x_1453_ = ((lean_object*)(l_Lake_Toml_mlBasicString___closed__1));
v___x_1454_ = ((lean_object*)(l_Lake_Toml_mlBasicString___closed__0));
v___x_1455_ = l_Lake_Toml_litWithAntiquot(v___x_1454_, v___x_1453_, v___x_1452_, v___x_1451_, v___x_1450_);
return v___x_1455_;
}
}
static lean_object* _init_l_Lake_Toml_mlBasicString(void){
_start:
{
lean_object* v___x_1456_; 
v___x_1456_ = lean_obj_once(&l_Lake_Toml_mlBasicString___closed__2, &l_Lake_Toml_mlBasicString___closed__2_once, _init_l_Lake_Toml_mlBasicString___closed__2);
return v___x_1456_;
}
}
static lean_object* _init_l_Lake_Toml_mlLiteralString___closed__2(void){
_start:
{
uint8_t v___x_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1462_ = 0;
v___x_1463_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1464_ = lean_alloc_closure((void*)(l_Lake_Toml_mlLiteralStringFn), 2, 0);
v___x_1465_ = ((lean_object*)(l_Lake_Toml_mlLiteralString___closed__1));
v___x_1466_ = ((lean_object*)(l_Lake_Toml_mlLiteralString___closed__0));
v___x_1467_ = l_Lake_Toml_litWithAntiquot(v___x_1466_, v___x_1465_, v___x_1464_, v___x_1463_, v___x_1462_);
return v___x_1467_;
}
}
static lean_object* _init_l_Lake_Toml_mlLiteralString(void){
_start:
{
lean_object* v___x_1468_; 
v___x_1468_ = lean_obj_once(&l_Lake_Toml_mlLiteralString___closed__2, &l_Lake_Toml_mlLiteralString___closed__2_once, _init_l_Lake_Toml_mlLiteralString___closed__2);
return v___x_1468_;
}
}
static lean_object* _init_l_Lake_Toml_quotedKey___closed__0(void){
_start:
{
lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1469_ = l_Lake_Toml_literalString;
v___x_1470_ = l_Lake_Toml_basicString;
v___x_1471_ = l_Lean_Parser_orelse(v___x_1470_, v___x_1469_);
return v___x_1471_;
}
}
static lean_object* _init_l_Lake_Toml_quotedKey(void){
_start:
{
lean_object* v___x_1472_; 
v___x_1472_ = lean_obj_once(&l_Lake_Toml_quotedKey___closed__0, &l_Lake_Toml_quotedKey___closed__0_once, _init_l_Lake_Toml_quotedKey___closed__0);
return v___x_1472_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey___closed__2(void){
_start:
{
lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; 
v___x_1478_ = l_Lake_Toml_quotedKey;
v___x_1479_ = l_Lake_Toml_unquotedKey;
v___x_1480_ = l_Lean_Parser_orelse(v___x_1479_, v___x_1478_);
return v___x_1480_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey___closed__3(void){
_start:
{
uint8_t v___x_1481_; lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v___x_1481_ = 1;
v___x_1482_ = lean_obj_once(&l_Lake_Toml_simpleKey___closed__2, &l_Lake_Toml_simpleKey___closed__2_once, _init_l_Lake_Toml_simpleKey___closed__2);
v___x_1483_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__1));
v___x_1484_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__0));
v___x_1485_ = l_Lean_Parser_nodeWithAntiquot(v___x_1484_, v___x_1483_, v___x_1482_, v___x_1481_);
return v___x_1485_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey(void){
_start:
{
lean_object* v___x_1486_; 
v___x_1486_ = lean_obj_once(&l_Lake_Toml_simpleKey___closed__3, &l_Lake_Toml_simpleKey___closed__3_once, _init_l_Lake_Toml_simpleKey___closed__3);
return v___x_1486_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__6(void){
_start:
{
lean_object* v___x_1500_; lean_object* v___x_1501_; uint32_t v___x_1502_; lean_object* v___x_1503_; 
v___x_1500_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1501_ = ((lean_object*)(l_Lake_Toml_key___closed__5));
v___x_1502_ = 46;
v___x_1503_ = l_Lake_Toml_chAtom(v___x_1502_, v___x_1501_, v___x_1500_);
return v___x_1503_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__7(void){
_start:
{
lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1504_ = l_Lake_Toml_trailingWs;
v___x_1505_ = lean_obj_once(&l_Lake_Toml_key___closed__6, &l_Lake_Toml_key___closed__6_once, _init_l_Lake_Toml_key___closed__6);
v___x_1506_ = l_Lean_Parser_andthen(v___x_1505_, v___x_1504_);
return v___x_1506_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__8(void){
_start:
{
lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1507_ = lean_obj_once(&l_Lake_Toml_key___closed__7, &l_Lake_Toml_key___closed__7_once, _init_l_Lake_Toml_key___closed__7);
v___x_1508_ = l_Lake_Toml_trailingWs;
v___x_1509_ = l_Lean_Parser_andthen(v___x_1508_, v___x_1507_);
return v___x_1509_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__9(void){
_start:
{
uint8_t v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1510_ = 0;
v___x_1511_ = lean_obj_once(&l_Lake_Toml_key___closed__8, &l_Lake_Toml_key___closed__8_once, _init_l_Lake_Toml_key___closed__8);
v___x_1512_ = ((lean_object*)(l_Lake_Toml_key___closed__3));
v___x_1513_ = l_Lake_Toml_simpleKey;
v___x_1514_ = l_Lean_Parser_sepBy1(v___x_1513_, v___x_1512_, v___x_1511_, v___x_1510_);
return v___x_1514_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__10(void){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; lean_object* v___x_1517_; 
v___x_1515_ = lean_obj_once(&l_Lake_Toml_key___closed__9, &l_Lake_Toml_key___closed__9_once, _init_l_Lake_Toml_key___closed__9);
v___x_1516_ = ((lean_object*)(l_Lake_Toml_key___closed__2));
v___x_1517_ = l_Lean_Parser_setExpected(v___x_1516_, v___x_1515_);
return v___x_1517_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__11(void){
_start:
{
uint8_t v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; lean_object* v___x_1522_; 
v___x_1518_ = 1;
v___x_1519_ = lean_obj_once(&l_Lake_Toml_key___closed__10, &l_Lake_Toml_key___closed__10_once, _init_l_Lake_Toml_key___closed__10);
v___x_1520_ = ((lean_object*)(l_Lake_Toml_key___closed__1));
v___x_1521_ = ((lean_object*)(l_Lake_Toml_key___closed__0));
v___x_1522_ = l_Lean_Parser_nodeWithAntiquot(v___x_1521_, v___x_1520_, v___x_1519_, v___x_1518_);
return v___x_1522_;
}
}
static lean_object* _init_l_Lake_Toml_key(void){
_start:
{
lean_object* v___x_1523_; 
v___x_1523_ = lean_obj_once(&l_Lake_Toml_key___closed__11, &l_Lake_Toml_key___closed__11_once, _init_l_Lake_Toml_key___closed__11);
return v___x_1523_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__4(void){
_start:
{
lean_object* v___x_1533_; lean_object* v___x_1534_; uint32_t v___x_1535_; lean_object* v___x_1536_; 
v___x_1533_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1534_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__3));
v___x_1535_ = 91;
v___x_1536_ = l_Lake_Toml_chAtom(v___x_1535_, v___x_1534_, v___x_1533_);
return v___x_1536_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__7(void){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; uint32_t v___x_1543_; lean_object* v___x_1544_; 
v___x_1541_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1542_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__6));
v___x_1543_ = 91;
v___x_1544_ = l_Lake_Toml_chAtom(v___x_1543_, v___x_1542_, v___x_1541_);
return v___x_1544_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__8(void){
_start:
{
lean_object* v___x_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; 
v___x_1545_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__5));
v___x_1546_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__7, &l_Lake_Toml_stdTable___closed__7_once, _init_l_Lake_Toml_stdTable___closed__7);
v___x_1547_ = l_Lean_Parser_notFollowedBy(v___x_1546_, v___x_1545_);
return v___x_1547_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__9(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1548_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__8, &l_Lake_Toml_stdTable___closed__8_once, _init_l_Lake_Toml_stdTable___closed__8);
v___x_1549_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__4, &l_Lake_Toml_stdTable___closed__4_once, _init_l_Lake_Toml_stdTable___closed__4);
v___x_1550_ = l_Lean_Parser_andthen(v___x_1549_, v___x_1548_);
return v___x_1550_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__10(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; 
v___x_1551_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__9, &l_Lake_Toml_stdTable___closed__9_once, _init_l_Lake_Toml_stdTable___closed__9);
v___x_1552_ = l_Lean_Parser_atomic(v___x_1551_);
return v___x_1552_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__13(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; uint32_t v___x_1559_; lean_object* v___x_1560_; 
v___x_1557_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1558_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__12));
v___x_1559_ = 93;
v___x_1560_ = l_Lake_Toml_chAtom(v___x_1559_, v___x_1558_, v___x_1557_);
return v___x_1560_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__14(void){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1561_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__13, &l_Lake_Toml_stdTable___closed__13_once, _init_l_Lake_Toml_stdTable___closed__13);
v___x_1562_ = l_Lake_Toml_trailingWs;
v___x_1563_ = l_Lean_Parser_andthen(v___x_1562_, v___x_1561_);
return v___x_1563_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__15(void){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1564_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__14, &l_Lake_Toml_stdTable___closed__14_once, _init_l_Lake_Toml_stdTable___closed__14);
v___x_1565_ = l_Lake_Toml_key;
v___x_1566_ = l_Lean_Parser_andthen(v___x_1565_, v___x_1564_);
return v___x_1566_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__16(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1567_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__15, &l_Lake_Toml_stdTable___closed__15_once, _init_l_Lake_Toml_stdTable___closed__15);
v___x_1568_ = l_Lake_Toml_trailingWs;
v___x_1569_ = l_Lean_Parser_andthen(v___x_1568_, v___x_1567_);
return v___x_1569_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__17(void){
_start:
{
lean_object* v___x_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; 
v___x_1570_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__16, &l_Lake_Toml_stdTable___closed__16_once, _init_l_Lake_Toml_stdTable___closed__16);
v___x_1571_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__10, &l_Lake_Toml_stdTable___closed__10_once, _init_l_Lake_Toml_stdTable___closed__10);
v___x_1572_ = l_Lean_Parser_andthen(v___x_1571_, v___x_1570_);
return v___x_1572_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__18(void){
_start:
{
uint8_t v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1573_ = 0;
v___x_1574_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__17, &l_Lake_Toml_stdTable___closed__17_once, _init_l_Lake_Toml_stdTable___closed__17);
v___x_1575_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__1));
v___x_1576_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__0));
v___x_1577_ = l_Lean_Parser_nodeWithAntiquot(v___x_1576_, v___x_1575_, v___x_1574_, v___x_1573_);
return v___x_1577_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable(void){
_start:
{
lean_object* v___x_1578_; 
v___x_1578_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__18, &l_Lake_Toml_stdTable___closed__18_once, _init_l_Lake_Toml_stdTable___closed__18);
return v___x_1578_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__2(void){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1584_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__7, &l_Lake_Toml_stdTable___closed__7_once, _init_l_Lake_Toml_stdTable___closed__7);
v___x_1585_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__4, &l_Lake_Toml_stdTable___closed__4_once, _init_l_Lake_Toml_stdTable___closed__4);
v___x_1586_ = l_Lean_Parser_andthen(v___x_1585_, v___x_1584_);
return v___x_1586_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__3(void){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1587_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__2, &l_Lake_Toml_arrayTable___closed__2_once, _init_l_Lake_Toml_arrayTable___closed__2);
v___x_1588_ = l_Lean_Parser_atomic(v___x_1587_);
return v___x_1588_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__4(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; 
v___x_1589_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__13, &l_Lake_Toml_stdTable___closed__13_once, _init_l_Lake_Toml_stdTable___closed__13);
v___x_1590_ = l_Lean_Parser_andthen(v___x_1589_, v___x_1589_);
return v___x_1590_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__5(void){
_start:
{
lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1591_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__4, &l_Lake_Toml_arrayTable___closed__4_once, _init_l_Lake_Toml_arrayTable___closed__4);
v___x_1592_ = l_Lake_Toml_trailingWs;
v___x_1593_ = l_Lean_Parser_andthen(v___x_1592_, v___x_1591_);
return v___x_1593_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__6(void){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; lean_object* v___x_1596_; 
v___x_1594_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__5, &l_Lake_Toml_arrayTable___closed__5_once, _init_l_Lake_Toml_arrayTable___closed__5);
v___x_1595_ = l_Lake_Toml_key;
v___x_1596_ = l_Lean_Parser_andthen(v___x_1595_, v___x_1594_);
return v___x_1596_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__7(void){
_start:
{
lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1599_; 
v___x_1597_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__6, &l_Lake_Toml_arrayTable___closed__6_once, _init_l_Lake_Toml_arrayTable___closed__6);
v___x_1598_ = l_Lake_Toml_trailingWs;
v___x_1599_ = l_Lean_Parser_andthen(v___x_1598_, v___x_1597_);
return v___x_1599_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__8(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1602_; 
v___x_1600_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__7, &l_Lake_Toml_arrayTable___closed__7_once, _init_l_Lake_Toml_arrayTable___closed__7);
v___x_1601_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__3, &l_Lake_Toml_arrayTable___closed__3_once, _init_l_Lake_Toml_arrayTable___closed__3);
v___x_1602_ = l_Lean_Parser_andthen(v___x_1601_, v___x_1600_);
return v___x_1602_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__9(void){
_start:
{
uint8_t v___x_1603_; lean_object* v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1603_ = 0;
v___x_1604_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__8, &l_Lake_Toml_arrayTable___closed__8_once, _init_l_Lake_Toml_arrayTable___closed__8);
v___x_1605_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__1));
v___x_1606_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__0));
v___x_1607_ = l_Lean_Parser_nodeWithAntiquot(v___x_1606_, v___x_1605_, v___x_1604_, v___x_1603_);
return v___x_1607_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable(void){
_start:
{
lean_object* v___x_1608_; 
v___x_1608_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__9, &l_Lake_Toml_arrayTable___closed__9_once, _init_l_Lake_Toml_arrayTable___closed__9);
return v___x_1608_;
}
}
static lean_object* _init_l_Lake_Toml_table___closed__0(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; 
v___x_1609_ = l_Lake_Toml_arrayTable;
v___x_1610_ = l_Lake_Toml_stdTable;
v___x_1611_ = l_Lean_Parser_orelse(v___x_1610_, v___x_1609_);
return v___x_1611_;
}
}
static lean_object* _init_l_Lake_Toml_table(void){
_start:
{
lean_object* v___x_1612_; 
v___x_1612_ = lean_obj_once(&l_Lake_Toml_table___closed__0, &l_Lake_Toml_table___closed__0_once, _init_l_Lake_Toml_table___closed__0);
return v___x_1612_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4(void){
_start:
{
lean_object* v___x_1622_; lean_object* v___x_1623_; uint32_t v___x_1624_; lean_object* v___x_1625_; 
v___x_1622_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1623_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3));
v___x_1624_ = 61;
v___x_1625_ = l_Lake_Toml_chAtom(v___x_1624_, v___x_1623_, v___x_1622_);
return v___x_1625_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(lean_object* v_val_1626_){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; lean_object* v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1635_; uint8_t v___x_1636_; lean_object* v___x_1637_; 
v___x_1627_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0));
v___x_1628_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1));
v___x_1629_ = l_Lake_Toml_key;
v___x_1630_ = l_Lake_Toml_trailingWs;
v___x_1631_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4);
v___x_1632_ = l_Lean_Parser_andthen(v___x_1630_, v_val_1626_);
v___x_1633_ = l_Lean_Parser_andthen(v___x_1631_, v___x_1632_);
v___x_1634_ = l_Lean_Parser_andthen(v___x_1630_, v___x_1633_);
v___x_1635_ = l_Lean_Parser_andthen(v___x_1629_, v___x_1634_);
v___x_1636_ = 1;
v___x_1637_ = l_Lean_Parser_nodeWithAntiquot(v___x_1627_, v___x_1628_, v___x_1635_, v___x_1636_);
return v___x_1637_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2(void){
_start:
{
uint8_t v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1643_ = 1;
v___x_1644_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1));
v___x_1645_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0));
v___x_1646_ = l_Lean_Parser_mkAntiquot(v___x_1645_, v___x_1644_, v___x_1643_, v___x_1643_);
return v___x_1646_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(lean_object* v_val_1647_){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1652_; 
v___x_1648_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2, &l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2);
v___x_1649_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(v_val_1647_);
v___x_1650_ = l_Lake_Toml_table;
v___x_1651_ = l_Lean_Parser_orelse(v___x_1649_, v___x_1650_);
v___x_1652_ = l_Lean_Parser_withAntiquot(v___x_1648_, v___x_1651_);
return v___x_1652_;
}
}
static lean_object* _init_l_Lake_Toml_header___closed__2(void){
_start:
{
uint8_t v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v___x_1658_ = 0;
v___x_1659_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1660_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1661_ = ((lean_object*)(l_Lake_Toml_header___closed__1));
v___x_1662_ = ((lean_object*)(l_Lake_Toml_header___closed__0));
v___x_1663_ = l_Lake_Toml_litWithAntiquot(v___x_1662_, v___x_1661_, v___x_1660_, v___x_1659_, v___x_1658_);
return v___x_1663_;
}
}
static lean_object* _init_l_Lake_Toml_header(void){
_start:
{
lean_object* v___x_1664_; 
v___x_1664_ = lean_obj_once(&l_Lake_Toml_header___closed__2, &l_Lake_Toml_header___closed__2_once, _init_l_Lake_Toml_header___closed__2);
return v___x_1664_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5(void){
_start:
{
lean_object* v___x_1674_; lean_object* v___x_1675_; 
v___x_1674_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__4));
v___x_1675_ = l_Lean_Parser_symbol(v___x_1674_);
return v___x_1675_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7(void){
_start:
{
lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1677_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__6));
v___x_1678_ = l_Lean_Parser_checkLinebreakBefore(v___x_1677_);
return v___x_1678_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = l_Lean_Parser_pushNone;
v___x_1680_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7, &l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7);
v___x_1681_ = l_Lean_Parser_andthen(v___x_1680_, v___x_1679_);
return v___x_1681_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore(lean_object* v_val_1682_){
_start:
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; lean_object* v___x_1688_; uint8_t v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v_p_1692_; lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; 
v___x_1683_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0));
v___x_1684_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1));
v___x_1685_ = l_Lake_Toml_header;
v___x_1686_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(v_val_1682_);
v___x_1687_ = l_Lake_Toml_trailingSep;
v___x_1688_ = l_Lean_Parser_andthen(v___x_1686_, v___x_1687_);
v___x_1689_ = 1;
v___x_1690_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__3));
v___x_1691_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5);
v_p_1692_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1690_, v___x_1688_, v___x_1691_);
v___x_1693_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8, &l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8);
v___x_1694_ = l_Lean_Parser_sepByNoAntiquot(v_p_1692_, v___x_1693_, v___x_1689_);
v___x_1695_ = l_Lean_Parser_andthen(v___x_1685_, v___x_1694_);
v___x_1696_ = l_Lean_Parser_nodeWithAntiquot(v___x_1683_, v___x_1684_, v___x_1695_, v___x_1689_);
return v___x_1696_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4(void){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; uint32_t v___x_1708_; lean_object* v___x_1709_; 
v___x_1706_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1707_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__3));
v___x_1708_ = 123;
v___x_1709_ = l_Lake_Toml_chAtom(v___x_1708_, v___x_1707_, v___x_1706_);
return v___x_1709_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; uint32_t v___x_1717_; lean_object* v___x_1718_; 
v___x_1715_ = lean_alloc_closure((void*)(l_Lake_Toml_wsFn___boxed), 2, 0);
v___x_1716_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7));
v___x_1717_ = 44;
v___x_1718_ = l_Lake_Toml_chAtom(v___x_1717_, v___x_1716_, v___x_1715_);
return v___x_1718_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11(void){
_start:
{
lean_object* v___x_1723_; lean_object* v___x_1724_; uint32_t v___x_1725_; lean_object* v___x_1726_; 
v___x_1723_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1724_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10));
v___x_1725_ = 125;
v___x_1726_ = l_Lake_Toml_chAtom(v___x_1725_, v___x_1724_, v___x_1723_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(lean_object* v_val_1727_){
_start:
{
lean_object* v___x_1728_; lean_object* v___x_1729_; lean_object* v___x_1730_; lean_object* v___x_1731_; lean_object* v___x_1732_; lean_object* v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; uint8_t v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1728_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0));
v___x_1729_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1));
v___x_1730_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4);
v___x_1731_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(v_val_1727_);
v___x_1732_ = l_Lake_Toml_trailingWs;
v___x_1733_ = l_Lean_Parser_andthen(v___x_1731_, v___x_1732_);
v___x_1734_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5));
v___x_1735_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8);
v___x_1736_ = 0;
v___x_1737_ = l_Lean_Parser_sepBy(v___x_1733_, v___x_1734_, v___x_1735_, v___x_1736_);
v___x_1738_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11);
v___x_1739_ = l_Lean_Parser_andthen(v___x_1737_, v___x_1738_);
v___x_1740_ = l_Lean_Parser_andthen(v___x_1730_, v___x_1739_);
v___x_1741_ = l_Lean_Parser_nodeWithAntiquot(v___x_1728_, v___x_1729_, v___x_1740_, v___x_1736_);
return v___x_1741_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3(void){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; uint32_t v___x_1752_; lean_object* v___x_1753_; 
v___x_1750_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1751_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__2));
v___x_1752_ = 91;
v___x_1753_ = l_Lake_Toml_chAtom(v___x_1752_, v___x_1751_, v___x_1750_);
return v___x_1753_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4(void){
_start:
{
lean_object* v___x_1754_; lean_object* v___x_1755_; uint32_t v___x_1756_; lean_object* v___x_1757_; 
v___x_1754_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1755_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7));
v___x_1756_ = 44;
v___x_1757_ = l_Lake_Toml_chAtom(v___x_1756_, v___x_1755_, v___x_1754_);
return v___x_1757_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(lean_object* v_val_1758_){
_start:
{
lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; uint8_t v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; uint8_t v___x_1771_; lean_object* v___x_1772_; 
v___x_1759_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0));
v___x_1760_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1));
v___x_1761_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3, &l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3);
v___x_1762_ = l_Lake_Toml_trailingSep;
v___x_1763_ = l_Lean_Parser_andthen(v_val_1758_, v___x_1762_);
v___x_1764_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5));
v___x_1765_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4, &l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4);
v___x_1766_ = 1;
v___x_1767_ = l_Lean_Parser_sepBy(v___x_1763_, v___x_1764_, v___x_1765_, v___x_1766_);
v___x_1768_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__13, &l_Lake_Toml_stdTable___closed__13_once, _init_l_Lake_Toml_stdTable___closed__13);
v___x_1769_ = l_Lean_Parser_andthen(v___x_1767_, v___x_1768_);
v___x_1770_ = l_Lean_Parser_andthen(v___x_1761_, v___x_1769_);
v___x_1771_ = 0;
v___x_1772_ = l_Lean_Parser_nodeWithAntiquot(v___x_1759_, v___x_1760_, v___x_1770_, v___x_1771_);
return v___x_1772_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__3(void){
_start:
{
lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; 
v___x_1781_ = l_Lake_Toml_literalString;
v___x_1782_ = l_Lake_Toml_mlLiteralString;
v___x_1783_ = l_Lean_Parser_orelse(v___x_1782_, v___x_1781_);
return v___x_1783_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__4(void){
_start:
{
lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1784_ = lean_obj_once(&l_Lake_Toml_string___closed__3, &l_Lake_Toml_string___closed__3_once, _init_l_Lake_Toml_string___closed__3);
v___x_1785_ = l_Lake_Toml_basicString;
v___x_1786_ = l_Lean_Parser_orelse(v___x_1785_, v___x_1784_);
return v___x_1786_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__5(void){
_start:
{
lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v___x_1787_ = lean_obj_once(&l_Lake_Toml_string___closed__4, &l_Lake_Toml_string___closed__4_once, _init_l_Lake_Toml_string___closed__4);
v___x_1788_ = l_Lake_Toml_mlBasicString;
v___x_1789_ = l_Lean_Parser_orelse(v___x_1788_, v___x_1787_);
return v___x_1789_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__6(void){
_start:
{
lean_object* v___x_1790_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1790_ = lean_obj_once(&l_Lake_Toml_string___closed__5, &l_Lake_Toml_string___closed__5_once, _init_l_Lake_Toml_string___closed__5);
v___x_1791_ = ((lean_object*)(l_Lake_Toml_string___closed__2));
v___x_1792_ = l_Lean_Parser_setExpected(v___x_1791_, v___x_1790_);
return v___x_1792_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__7(void){
_start:
{
uint8_t v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; lean_object* v___x_1797_; 
v___x_1793_ = 0;
v___x_1794_ = lean_obj_once(&l_Lake_Toml_string___closed__6, &l_Lake_Toml_string___closed__6_once, _init_l_Lake_Toml_string___closed__6);
v___x_1795_ = ((lean_object*)(l_Lake_Toml_string___closed__1));
v___x_1796_ = ((lean_object*)(l_Lake_Toml_string___closed__0));
v___x_1797_ = l_Lean_Parser_nodeWithAntiquot(v___x_1796_, v___x_1795_, v___x_1794_, v___x_1793_);
return v___x_1797_;
}
}
static lean_object* _init_l_Lake_Toml_string(void){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = lean_obj_once(&l_Lake_Toml_string___closed__7, &l_Lake_Toml_string___closed__7_once, _init_l_Lake_Toml_string___closed__7);
return v___x_1798_;
}
}
static lean_object* _init_l_Lake_Toml_true___closed__5(void){
_start:
{
lean_object* v___x_1811_; lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1811_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1812_ = ((lean_object*)(l_Lake_Toml_true___closed__4));
v___x_1813_ = ((lean_object*)(l_Lake_Toml_true___closed__1));
v___x_1814_ = l_Lake_Toml_lit(v___x_1813_, v___x_1812_, v___x_1811_);
return v___x_1814_;
}
}
static lean_object* _init_l_Lake_Toml_true(void){
_start:
{
lean_object* v___x_1815_; 
v___x_1815_ = lean_obj_once(&l_Lake_Toml_true___closed__5, &l_Lake_Toml_true___closed__5_once, _init_l_Lake_Toml_true___closed__5);
return v___x_1815_;
}
}
static lean_object* _init_l_Lake_Toml_false___closed__5(void){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; 
v___x_1828_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1829_ = ((lean_object*)(l_Lake_Toml_false___closed__4));
v___x_1830_ = ((lean_object*)(l_Lake_Toml_false___closed__1));
v___x_1831_ = l_Lake_Toml_lit(v___x_1830_, v___x_1829_, v___x_1828_);
return v___x_1831_;
}
}
static lean_object* _init_l_Lake_Toml_false(void){
_start:
{
lean_object* v___x_1832_; 
v___x_1832_ = lean_obj_once(&l_Lake_Toml_false___closed__5, &l_Lake_Toml_false___closed__5_once, _init_l_Lake_Toml_false___closed__5);
return v___x_1832_;
}
}
static lean_object* _init_l_Lake_Toml_boolean___closed__2(void){
_start:
{
lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1838_ = l_Lake_Toml_false;
v___x_1839_ = l_Lake_Toml_true;
v___x_1840_ = l_Lean_Parser_orelse(v___x_1839_, v___x_1838_);
return v___x_1840_;
}
}
static lean_object* _init_l_Lake_Toml_boolean___closed__3(void){
_start:
{
uint8_t v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1841_ = 0;
v___x_1842_ = lean_obj_once(&l_Lake_Toml_boolean___closed__2, &l_Lake_Toml_boolean___closed__2_once, _init_l_Lake_Toml_boolean___closed__2);
v___x_1843_ = ((lean_object*)(l_Lake_Toml_boolean___closed__1));
v___x_1844_ = ((lean_object*)(l_Lake_Toml_boolean___closed__0));
v___x_1845_ = l_Lean_Parser_nodeWithAntiquot(v___x_1844_, v___x_1843_, v___x_1842_, v___x_1841_);
return v___x_1845_;
}
}
static lean_object* _init_l_Lake_Toml_boolean(void){
_start:
{
lean_object* v___x_1846_; 
v___x_1846_ = lean_obj_once(&l_Lake_Toml_boolean___closed__3, &l_Lake_Toml_boolean___closed__3_once, _init_l_Lake_Toml_boolean___closed__3);
return v___x_1846_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__0(void){
_start:
{
uint8_t v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; lean_object* v___x_1850_; 
v___x_1847_ = 0;
v___x_1848_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_1849_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2));
v___x_1850_ = l_Lean_Parser_mkAntiquot(v___x_1849_, v___x_1848_, v___x_1847_, v___x_1847_);
return v___x_1850_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__1(void){
_start:
{
uint8_t v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1851_ = 0;
v___x_1852_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1853_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5));
v___x_1854_ = l_Lean_Parser_mkAntiquot(v___x_1853_, v___x_1852_, v___x_1851_, v___x_1851_);
return v___x_1854_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__2(void){
_start:
{
uint8_t v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1855_ = 0;
v___x_1856_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__19));
v___x_1857_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__18));
v___x_1858_ = l_Lean_Parser_mkAntiquot(v___x_1857_, v___x_1856_, v___x_1855_, v___x_1855_);
return v___x_1858_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__3(void){
_start:
{
uint8_t v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; lean_object* v___x_1862_; 
v___x_1859_ = 0;
v___x_1860_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__14));
v___x_1861_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__13));
v___x_1862_ = l_Lean_Parser_mkAntiquot(v___x_1861_, v___x_1860_, v___x_1859_, v___x_1859_);
return v___x_1862_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__4(void){
_start:
{
uint8_t v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1863_ = 0;
v___x_1864_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__9));
v___x_1865_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__8));
v___x_1866_ = l_Lean_Parser_mkAntiquot(v___x_1865_, v___x_1864_, v___x_1863_, v___x_1863_);
return v___x_1866_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__5(void){
_start:
{
uint8_t v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; 
v___x_1867_ = 0;
v___x_1868_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_1869_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0));
v___x_1870_ = l_Lean_Parser_mkAntiquot(v___x_1869_, v___x_1868_, v___x_1867_, v___x_1867_);
return v___x_1870_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__8(void){
_start:
{
uint8_t v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; 
v___x_1876_ = 1;
v___x_1877_ = ((lean_object*)(l_Lake_Toml_numeralAntiquot___closed__7));
v___x_1878_ = ((lean_object*)(l_Lake_Toml_numeralAntiquot___closed__6));
v___x_1879_ = l_Lean_Parser_mkAntiquot(v___x_1878_, v___x_1877_, v___x_1876_, v___x_1876_);
return v___x_1879_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__9(void){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; lean_object* v___x_1882_; 
v___x_1880_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__8, &l_Lake_Toml_numeralAntiquot___closed__8_once, _init_l_Lake_Toml_numeralAntiquot___closed__8);
v___x_1881_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__5, &l_Lake_Toml_numeralAntiquot___closed__5_once, _init_l_Lake_Toml_numeralAntiquot___closed__5);
v___x_1882_ = l_Lean_Parser_orelse(v___x_1881_, v___x_1880_);
return v___x_1882_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__10(void){
_start:
{
lean_object* v___x_1883_; lean_object* v___x_1884_; lean_object* v___x_1885_; 
v___x_1883_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__9, &l_Lake_Toml_numeralAntiquot___closed__9_once, _init_l_Lake_Toml_numeralAntiquot___closed__9);
v___x_1884_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__4, &l_Lake_Toml_numeralAntiquot___closed__4_once, _init_l_Lake_Toml_numeralAntiquot___closed__4);
v___x_1885_ = l_Lean_Parser_orelse(v___x_1884_, v___x_1883_);
return v___x_1885_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__11(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; lean_object* v___x_1888_; 
v___x_1886_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__10, &l_Lake_Toml_numeralAntiquot___closed__10_once, _init_l_Lake_Toml_numeralAntiquot___closed__10);
v___x_1887_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__3, &l_Lake_Toml_numeralAntiquot___closed__3_once, _init_l_Lake_Toml_numeralAntiquot___closed__3);
v___x_1888_ = l_Lean_Parser_orelse(v___x_1887_, v___x_1886_);
return v___x_1888_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__12(void){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1889_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__11, &l_Lake_Toml_numeralAntiquot___closed__11_once, _init_l_Lake_Toml_numeralAntiquot___closed__11);
v___x_1890_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__2, &l_Lake_Toml_numeralAntiquot___closed__2_once, _init_l_Lake_Toml_numeralAntiquot___closed__2);
v___x_1891_ = l_Lean_Parser_orelse(v___x_1890_, v___x_1889_);
return v___x_1891_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__13(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__12, &l_Lake_Toml_numeralAntiquot___closed__12_once, _init_l_Lake_Toml_numeralAntiquot___closed__12);
v___x_1893_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__1, &l_Lake_Toml_numeralAntiquot___closed__1_once, _init_l_Lake_Toml_numeralAntiquot___closed__1);
v___x_1894_ = l_Lean_Parser_orelse(v___x_1893_, v___x_1892_);
return v___x_1894_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__14(void){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1895_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__13, &l_Lake_Toml_numeralAntiquot___closed__13_once, _init_l_Lake_Toml_numeralAntiquot___closed__13);
v___x_1896_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__0, &l_Lake_Toml_numeralAntiquot___closed__0_once, _init_l_Lake_Toml_numeralAntiquot___closed__0);
v___x_1897_ = l_Lean_Parser_orelse(v___x_1896_, v___x_1895_);
return v___x_1897_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot(void){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__14, &l_Lake_Toml_numeralAntiquot___closed__14_once, _init_l_Lake_Toml_numeralAntiquot___closed__14);
return v___x_1898_;
}
}
static lean_object* _init_l_Lake_Toml_numeral___closed__0(void){
_start:
{
lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1899_ = lean_alloc_closure((void*)(l_Lake_Toml_numeralFn), 2, 0);
v___x_1900_ = l_Lake_Toml_dynamicNode(v___x_1899_);
return v___x_1900_;
}
}
static lean_object* _init_l_Lake_Toml_numeral___closed__1(void){
_start:
{
lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; 
v___x_1901_ = lean_obj_once(&l_Lake_Toml_numeral___closed__0, &l_Lake_Toml_numeral___closed__0_once, _init_l_Lake_Toml_numeral___closed__0);
v___x_1902_ = l_Lake_Toml_numeralAntiquot;
v___x_1903_ = l_Lean_Parser_withAntiquot(v___x_1902_, v___x_1901_);
return v___x_1903_;
}
}
static lean_object* _init_l_Lake_Toml_numeral(void){
_start:
{
lean_object* v___x_1904_; 
v___x_1904_ = lean_obj_once(&l_Lake_Toml_numeral___closed__1, &l_Lake_Toml_numeral___closed__1_once, _init_l_Lake_Toml_numeral___closed__1);
return v___x_1904_;
}
}
uint8_t l_Lake_Toml_numeralOfKind___lam__0(lean_object* v_kind_1905_, lean_object* v_x_1906_){
_start:
{
uint8_t v___x_1907_; 
v___x_1907_ = l_Lean_Syntax_isOfKind(v_x_1906_, v_kind_1905_);
return v___x_1907_;
}
}
LEAN_EXPORT void l_Lake_Toml_numeralOfKind___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_kind_1905_ = stack[0].m_obj;
lean_object* v_x_1906_ = stack[1].m_obj;
uint8_t v_res_1908_;
v_res_1908_ = l_Lake_Toml_numeralOfKind___lam__0(v_kind_1905_, v_x_1906_);
stack->m_num = v_res_1908_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralOfKind___lam__0___boxed(lean_object* v_kind_1909_, lean_object* v_x_1910_){
_start:
{
uint8_t v_res_1911_; lean_object* v_r_1912_; 
v_res_1911_ = l_Lake_Toml_numeralOfKind___lam__0(v_kind_1909_, v_x_1910_);
lean_dec(v_kind_1909_);
v_r_1912_ = lean_box(v_res_1911_);
return v_r_1912_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralOfKind(lean_object* v_name_1914_, lean_object* v_kind_1915_){
_start:
{
lean_object* v___f_1916_; lean_object* v___x_1917_; lean_object* v___x_1918_; lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___f_1916_ = lean_alloc_closure((void*)(l_Lake_Toml_numeralOfKind___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1916_, 0, v_kind_1915_);
v___x_1917_ = l_Lake_Toml_numeral;
v___x_1918_ = lean_box(0);
v___x_1919_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1919_, 0, v_name_1914_);
lean_ctor_set(v___x_1919_, 1, v___x_1918_);
v___x_1920_ = ((lean_object*)(l_Lake_Toml_numeralOfKind___closed__0));
v___x_1921_ = l_Lean_Parser_checkStackTop(v___f_1916_, v___x_1920_);
v___x_1922_ = l_Lean_Parser_setExpected(v___x_1919_, v___x_1921_);
v___x_1923_ = l_Lean_Parser_andthen(v___x_1917_, v___x_1922_);
return v___x_1923_;
}
}
static lean_object* _init_l_Lake_Toml_float___closed__0(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1924_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_1925_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2));
v___x_1926_ = l_Lake_Toml_numeralOfKind(v___x_1925_, v___x_1924_);
return v___x_1926_;
}
}
static lean_object* _init_l_Lake_Toml_float(void){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = lean_obj_once(&l_Lake_Toml_float___closed__0, &l_Lake_Toml_float___closed__0_once, _init_l_Lake_Toml_float___closed__0);
return v___x_1927_;
}
}
static lean_object* _init_l_Lake_Toml_decInt___closed__0(void){
_start:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; lean_object* v___x_1930_; 
v___x_1928_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1929_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0));
v___x_1930_ = l_Lake_Toml_numeralOfKind(v___x_1929_, v___x_1928_);
return v___x_1930_;
}
}
static lean_object* _init_l_Lake_Toml_decInt(void){
_start:
{
lean_object* v___x_1931_; 
v___x_1931_ = lean_obj_once(&l_Lake_Toml_decInt___closed__0, &l_Lake_Toml_decInt___closed__0_once, _init_l_Lake_Toml_decInt___closed__0);
return v___x_1931_;
}
}
static lean_object* _init_l_Lake_Toml_binNum___closed__1(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1933_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__19));
v___x_1934_ = ((lean_object*)(l_Lake_Toml_binNum___closed__0));
v___x_1935_ = l_Lake_Toml_numeralOfKind(v___x_1934_, v___x_1933_);
return v___x_1935_;
}
}
static lean_object* _init_l_Lake_Toml_binNum(void){
_start:
{
lean_object* v___x_1936_; 
v___x_1936_ = lean_obj_once(&l_Lake_Toml_binNum___closed__1, &l_Lake_Toml_binNum___closed__1_once, _init_l_Lake_Toml_binNum___closed__1);
return v___x_1936_;
}
}
static lean_object* _init_l_Lake_Toml_octNum___closed__1(void){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; 
v___x_1938_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__14));
v___x_1939_ = ((lean_object*)(l_Lake_Toml_octNum___closed__0));
v___x_1940_ = l_Lake_Toml_numeralOfKind(v___x_1939_, v___x_1938_);
return v___x_1940_;
}
}
static lean_object* _init_l_Lake_Toml_octNum(void){
_start:
{
lean_object* v___x_1941_; 
v___x_1941_ = lean_obj_once(&l_Lake_Toml_octNum___closed__1, &l_Lake_Toml_octNum___closed__1_once, _init_l_Lake_Toml_octNum___closed__1);
return v___x_1941_;
}
}
static lean_object* _init_l_Lake_Toml_hexNum___closed__1(void){
_start:
{
lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; 
v___x_1943_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__9));
v___x_1944_ = ((lean_object*)(l_Lake_Toml_hexNum___closed__0));
v___x_1945_ = l_Lake_Toml_numeralOfKind(v___x_1944_, v___x_1943_);
return v___x_1945_;
}
}
static lean_object* _init_l_Lake_Toml_hexNum(void){
_start:
{
lean_object* v___x_1946_; 
v___x_1946_ = lean_obj_once(&l_Lake_Toml_hexNum___closed__1, &l_Lake_Toml_hexNum___closed__1_once, _init_l_Lake_Toml_hexNum___closed__1);
return v___x_1946_;
}
}
static lean_object* _init_l_Lake_Toml_dateTime___closed__0(void){
_start:
{
lean_object* v___x_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; 
v___x_1947_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_1948_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2));
v___x_1949_ = l_Lake_Toml_numeralOfKind(v___x_1948_, v___x_1947_);
return v___x_1949_;
}
}
static lean_object* _init_l_Lake_Toml_dateTime(void){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = lean_obj_once(&l_Lake_Toml_dateTime___closed__0, &l_Lake_Toml_dateTime___closed__0_once, _init_l_Lake_Toml_dateTime___closed__0);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_valCore(lean_object* v_val_1951_){
_start:
{
lean_object* v___x_1952_; lean_object* v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1952_ = l_Lake_Toml_string;
v___x_1953_ = l_Lake_Toml_boolean;
v___x_1954_ = l_Lake_Toml_numeral;
lean_inc_ref(v_val_1951_);
v___x_1955_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(v_val_1951_);
v___x_1956_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(v_val_1951_);
v___x_1957_ = l_Lean_Parser_orelse(v___x_1955_, v___x_1956_);
v___x_1958_ = l_Lean_Parser_orelse(v___x_1954_, v___x_1957_);
v___x_1959_ = l_Lean_Parser_orelse(v___x_1953_, v___x_1958_);
v___x_1960_ = l_Lean_Parser_orelse(v___x_1952_, v___x_1959_);
return v___x_1960_;
}
}
static lean_object* _init_l_Lake_Toml_val___closed__3(void){
_start:
{
uint8_t v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1967_ = 1;
v___x_1968_ = ((lean_object*)(l_Lake_Toml_val___closed__2));
v___x_1969_ = ((lean_object*)(l_Lake_Toml_val___closed__1));
v___x_1970_ = ((lean_object*)(l_Lake_Toml_val___closed__0));
v___x_1971_ = l_Lake_Toml_recNodeWithAntiquot(v___x_1970_, v___x_1969_, v___x_1968_, v___x_1967_);
return v___x_1971_;
}
}
static lean_object* _init_l_Lake_Toml_val(void){
_start:
{
lean_object* v___x_1972_; 
v___x_1972_ = lean_obj_once(&l_Lake_Toml_val___closed__3, &l_Lake_Toml_val___closed__3_once, _init_l_Lake_Toml_val___closed__3);
return v___x_1972_;
}
}
static lean_object* _init_l_Lake_Toml_array___closed__0(void){
_start:
{
lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1973_ = l_Lake_Toml_val;
v___x_1974_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(v___x_1973_);
return v___x_1974_;
}
}
static lean_object* _init_l_Lake_Toml_array(void){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = lean_obj_once(&l_Lake_Toml_array___closed__0, &l_Lake_Toml_array___closed__0_once, _init_l_Lake_Toml_array___closed__0);
return v___x_1975_;
}
}
static lean_object* _init_l_Lake_Toml_inlineTable___closed__0(void){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; 
v___x_1976_ = l_Lake_Toml_val;
v___x_1977_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(v___x_1976_);
return v___x_1977_;
}
}
static lean_object* _init_l_Lake_Toml_inlineTable(void){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = lean_obj_once(&l_Lake_Toml_inlineTable___closed__0, &l_Lake_Toml_inlineTable___closed__0_once, _init_l_Lake_Toml_inlineTable___closed__0);
return v___x_1978_;
}
}
static lean_object* _init_l_Lake_Toml_keyval___closed__0(void){
_start:
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
v___x_1979_ = l_Lake_Toml_val;
v___x_1980_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(v___x_1979_);
return v___x_1980_;
}
}
static lean_object* _init_l_Lake_Toml_keyval(void){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = lean_obj_once(&l_Lake_Toml_keyval___closed__0, &l_Lake_Toml_keyval___closed__0_once, _init_l_Lake_Toml_keyval___closed__0);
return v___x_1981_;
}
}
static lean_object* _init_l_Lake_Toml_expression___closed__0(void){
_start:
{
lean_object* v___x_1982_; lean_object* v___x_1983_; 
v___x_1982_ = l_Lake_Toml_val;
v___x_1983_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(v___x_1982_);
return v___x_1983_;
}
}
static lean_object* _init_l_Lake_Toml_expression(void){
_start:
{
lean_object* v___x_1984_; 
v___x_1984_ = lean_obj_once(&l_Lake_Toml_expression___closed__0, &l_Lake_Toml_expression___closed__0_once, _init_l_Lake_Toml_expression___closed__0);
return v___x_1984_;
}
}
lean_object* l_Lake_Toml_header_formatter(lean_object* v_a_1985_, lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_){
_start:
{
lean_object* v___x_1990_; lean_object* v___x_1991_; uint8_t v___x_1992_; lean_object* v___x_1993_; 
v___x_1990_ = ((lean_object*)(l_Lake_Toml_header___closed__0));
v___x_1991_ = ((lean_object*)(l_Lake_Toml_header___closed__1));
v___x_1992_ = 0;
v___x_1993_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v___x_1990_, v___x_1991_, v___x_1992_, v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
return v___x_1993_;
}
}
LEAN_EXPORT void l_Lake_Toml_header_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_1985_ = stack[0].m_obj;
lean_object* v_a_1986_ = stack[1].m_obj;
lean_object* v_a_1987_ = stack[2].m_obj;
lean_object* v_a_1988_ = stack[3].m_obj;
lean_object* v_res_1994_;
v_res_1994_ = l_Lake_Toml_header_formatter(v_a_1985_, v_a_1986_, v_a_1987_, v_a_1988_);
stack->m_obj
 = v_res_1994_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_header_formatter___boxed(lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_Lake_Toml_header_formatter(v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
lean_dec(v_a_1996_);
lean_dec_ref(v_a_1995_);
return v_res_2000_;
}
}
lean_object* l_Lake_Toml_unquotedKey_formatter(lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; lean_object* v___x_2009_; 
v___x_2006_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__0));
v___x_2007_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__1));
v___x_2008_ = 0;
v___x_2009_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v___x_2006_, v___x_2007_, v___x_2008_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
return v___x_2009_;
}
}
LEAN_EXPORT void l_Lake_Toml_unquotedKey_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2001_ = stack[0].m_obj;
lean_object* v_a_2002_ = stack[1].m_obj;
lean_object* v_a_2003_ = stack[2].m_obj;
lean_object* v_a_2004_ = stack[3].m_obj;
lean_object* v_res_2010_;
v_res_2010_ = l_Lake_Toml_unquotedKey_formatter(v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
stack->m_obj
 = v_res_2010_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_formatter___boxed(lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_){
_start:
{
lean_object* v_res_2016_; 
v_res_2016_ = l_Lake_Toml_unquotedKey_formatter(v_a_2011_, v_a_2012_, v_a_2013_, v_a_2014_);
lean_dec(v_a_2014_);
lean_dec_ref(v_a_2013_);
lean_dec(v_a_2012_);
lean_dec_ref(v_a_2011_);
return v_res_2016_;
}
}
lean_object* l_Lake_Toml_basicString_formatter(lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; uint8_t v___x_2024_; lean_object* v___x_2025_; 
v___x_2022_ = ((lean_object*)(l_Lake_Toml_basicString___closed__0));
v___x_2023_ = ((lean_object*)(l_Lake_Toml_basicString___closed__1));
v___x_2024_ = 0;
v___x_2025_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v___x_2022_, v___x_2023_, v___x_2024_, v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
return v___x_2025_;
}
}
LEAN_EXPORT void l_Lake_Toml_basicString_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2017_ = stack[0].m_obj;
lean_object* v_a_2018_ = stack[1].m_obj;
lean_object* v_a_2019_ = stack[2].m_obj;
lean_object* v_a_2020_ = stack[3].m_obj;
lean_object* v_res_2026_;
v_res_2026_ = l_Lake_Toml_basicString_formatter(v_a_2017_, v_a_2018_, v_a_2019_, v_a_2020_);
stack->m_obj
 = v_res_2026_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_formatter___boxed(lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_, lean_object* v_a_2030_, lean_object* v_a_2031_){
_start:
{
lean_object* v_res_2032_; 
v_res_2032_ = l_Lake_Toml_basicString_formatter(v_a_2027_, v_a_2028_, v_a_2029_, v_a_2030_);
lean_dec(v_a_2030_);
lean_dec_ref(v_a_2029_);
lean_dec(v_a_2028_);
lean_dec_ref(v_a_2027_);
return v_res_2032_;
}
}
lean_object* l_Lake_Toml_literalString_formatter(lean_object* v_a_2033_, lean_object* v_a_2034_, lean_object* v_a_2035_, lean_object* v_a_2036_){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; uint8_t v___x_2040_; lean_object* v___x_2041_; 
v___x_2038_ = ((lean_object*)(l_Lake_Toml_literalString___closed__0));
v___x_2039_ = ((lean_object*)(l_Lake_Toml_literalString___closed__1));
v___x_2040_ = 0;
v___x_2041_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v___x_2038_, v___x_2039_, v___x_2040_, v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_);
return v___x_2041_;
}
}
LEAN_EXPORT void l_Lake_Toml_literalString_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2033_ = stack[0].m_obj;
lean_object* v_a_2034_ = stack[1].m_obj;
lean_object* v_a_2035_ = stack[2].m_obj;
lean_object* v_a_2036_ = stack[3].m_obj;
lean_object* v_res_2042_;
v_res_2042_ = l_Lake_Toml_literalString_formatter(v_a_2033_, v_a_2034_, v_a_2035_, v_a_2036_);
stack->m_obj
 = v_res_2042_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_formatter___boxed(lean_object* v_a_2043_, lean_object* v_a_2044_, lean_object* v_a_2045_, lean_object* v_a_2046_, lean_object* v_a_2047_){
_start:
{
lean_object* v_res_2048_; 
v_res_2048_ = l_Lake_Toml_literalString_formatter(v_a_2043_, v_a_2044_, v_a_2045_, v_a_2046_);
lean_dec(v_a_2046_);
lean_dec_ref(v_a_2045_);
lean_dec(v_a_2044_);
lean_dec_ref(v_a_2043_);
return v_res_2048_;
}
}
lean_object* l_Lake_Toml_quotedKey_formatter(lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_, lean_object* v_a_2052_){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = lean_alloc_closure((void*)(l_Lake_Toml_basicString_formatter___boxed), 5, 0);
v___x_2055_ = lean_alloc_closure((void*)(l_Lake_Toml_literalString_formatter___boxed), 5, 0);
v___x_2056_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2054_, v___x_2055_, v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_);
return v___x_2056_;
}
}
LEAN_EXPORT void l_Lake_Toml_quotedKey_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2049_ = stack[0].m_obj;
lean_object* v_a_2050_ = stack[1].m_obj;
lean_object* v_a_2051_ = stack[2].m_obj;
lean_object* v_a_2052_ = stack[3].m_obj;
lean_object* v_res_2057_;
v_res_2057_ = l_Lake_Toml_quotedKey_formatter(v_a_2049_, v_a_2050_, v_a_2051_, v_a_2052_);
stack->m_obj
 = v_res_2057_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_formatter___boxed(lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Lake_Toml_quotedKey_formatter(v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_);
lean_dec(v_a_2061_);
lean_dec_ref(v_a_2060_);
lean_dec(v_a_2059_);
lean_dec_ref(v_a_2058_);
return v_res_2063_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey_formatter___closed__0(void){
_start:
{
lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; 
v___x_2064_ = lean_alloc_closure((void*)(l_Lake_Toml_quotedKey_formatter___boxed), 5, 0);
v___x_2065_ = lean_alloc_closure((void*)(l_Lake_Toml_unquotedKey_formatter___boxed), 5, 0);
v___x_2066_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2066_, 0, v___x_2065_);
lean_closure_set(v___x_2066_, 1, v___x_2064_);
return v___x_2066_;
}
}
lean_object* l_Lake_Toml_simpleKey_formatter(lean_object* v_a_2067_, lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_){
_start:
{
lean_object* v___x_2072_; lean_object* v___x_2073_; lean_object* v___x_2074_; uint8_t v___x_2075_; lean_object* v___x_2076_; 
v___x_2072_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__0));
v___x_2073_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__1));
v___x_2074_ = lean_obj_once(&l_Lake_Toml_simpleKey_formatter___closed__0, &l_Lake_Toml_simpleKey_formatter___closed__0_once, _init_l_Lake_Toml_simpleKey_formatter___closed__0);
v___x_2075_ = 1;
v___x_2076_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2072_, v___x_2073_, v___x_2074_, v___x_2075_, v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
return v___x_2076_;
}
}
LEAN_EXPORT void l_Lake_Toml_simpleKey_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2067_ = stack[0].m_obj;
lean_object* v_a_2068_ = stack[1].m_obj;
lean_object* v_a_2069_ = stack[2].m_obj;
lean_object* v_a_2070_ = stack[3].m_obj;
lean_object* v_res_2077_;
v_res_2077_ = l_Lake_Toml_simpleKey_formatter(v_a_2067_, v_a_2068_, v_a_2069_, v_a_2070_);
stack->m_obj
 = v_res_2077_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_formatter___boxed(lean_object* v_a_2078_, lean_object* v_a_2079_, lean_object* v_a_2080_, lean_object* v_a_2081_, lean_object* v_a_2082_){
_start:
{
lean_object* v_res_2083_; 
v_res_2083_ = l_Lake_Toml_simpleKey_formatter(v_a_2078_, v_a_2079_, v_a_2080_, v_a_2081_);
lean_dec(v_a_2081_);
lean_dec_ref(v_a_2080_);
lean_dec(v_a_2079_);
lean_dec_ref(v_a_2078_);
return v_res_2083_;
}
}
lean_object* l_Lake_Toml_trailingWs_formatter___redArg(){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_2085_;
}
}
LEAN_EXPORT void l_Lake_Toml_trailingWs_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2086_;
v_res_2086_ = l_Lake_Toml_trailingWs_formatter___redArg();
stack->m_obj
 = v_res_2086_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter___redArg___boxed(lean_object* v_a_2087_){
_start:
{
lean_object* v_res_2088_; 
v_res_2088_ = l_Lake_Toml_trailingWs_formatter___redArg();
return v_res_2088_;
}
}
lean_object* l_Lake_Toml_trailingWs_formatter(lean_object* v_a_2089_, lean_object* v_a_2090_, lean_object* v_a_2091_, lean_object* v_a_2092_){
_start:
{
lean_object* v___x_2094_; 
v___x_2094_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_2094_;
}
}
LEAN_EXPORT void l_Lake_Toml_trailingWs_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2089_ = stack[0].m_obj;
lean_object* v_a_2090_ = stack[1].m_obj;
lean_object* v_a_2091_ = stack[2].m_obj;
lean_object* v_a_2092_ = stack[3].m_obj;
lean_object* v_res_2095_;
v_res_2095_ = l_Lake_Toml_trailingWs_formatter(v_a_2089_, v_a_2090_, v_a_2091_, v_a_2092_);
stack->m_obj
 = v_res_2095_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter___boxed(lean_object* v_a_2096_, lean_object* v_a_2097_, lean_object* v_a_2098_, lean_object* v_a_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v_res_2101_; 
v_res_2101_ = l_Lake_Toml_trailingWs_formatter(v_a_2096_, v_a_2097_, v_a_2098_, v_a_2099_);
lean_dec(v_a_2099_);
lean_dec_ref(v_a_2098_);
lean_dec(v_a_2097_);
lean_dec_ref(v_a_2096_);
return v_res_2101_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_2102_; lean_object* v___x_2103_; 
v___x_2102_ = 46;
v___x_2103_ = lean_box_uint32(v___x_2102_);
return v___x_2103_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__0(void){
_start:
{
lean_object* v___x_2104_; lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2104_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2105_ = ((lean_object*)(l_Lake_Toml_key___closed__5));
v___x_2106_ = l_Lake_Toml_key_formatter___closed__0___boxed__const__1;
v___x_2107_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2107_, 0, v___x_2106_);
lean_closure_set(v___x_2107_, 1, v___x_2105_);
lean_closure_set(v___x_2107_, 2, v___x_2104_);
return v___x_2107_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__1(void){
_start:
{
lean_object* v___x_2108_; lean_object* v___x_2109_; lean_object* v___x_2110_; 
v___x_2108_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2109_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__0, &l_Lake_Toml_key_formatter___closed__0_once, _init_l_Lake_Toml_key_formatter___closed__0);
v___x_2110_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2110_, 0, v___x_2109_);
lean_closure_set(v___x_2110_, 1, v___x_2108_);
return v___x_2110_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__2(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
v___x_2111_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__1, &l_Lake_Toml_key_formatter___closed__1_once, _init_l_Lake_Toml_key_formatter___closed__1);
v___x_2112_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2113_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2113_, 0, v___x_2112_);
lean_closure_set(v___x_2113_, 1, v___x_2111_);
return v___x_2113_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__3(void){
_start:
{
uint8_t v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2118_; lean_object* v___x_2119_; 
v___x_2114_ = 0;
v___x_2115_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__2, &l_Lake_Toml_key_formatter___closed__2_once, _init_l_Lake_Toml_key_formatter___closed__2);
v___x_2116_ = ((lean_object*)(l_Lake_Toml_key___closed__3));
v___x_2117_ = lean_alloc_closure((void*)(l_Lake_Toml_simpleKey_formatter___boxed), 5, 0);
v___x_2118_ = lean_box(v___x_2114_);
v___x_2119_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_formatter___boxed), 9, 4);
lean_closure_set(v___x_2119_, 0, v___x_2117_);
lean_closure_set(v___x_2119_, 1, v___x_2116_);
lean_closure_set(v___x_2119_, 2, v___x_2115_);
lean_closure_set(v___x_2119_, 3, v___x_2118_);
return v___x_2119_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__4(void){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2120_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__3, &l_Lake_Toml_key_formatter___closed__3_once, _init_l_Lake_Toml_key_formatter___closed__3);
v___x_2121_ = ((lean_object*)(l_Lake_Toml_key___closed__2));
v___x_2122_ = lean_alloc_closure((void*)(l_Lean_Parser_setExpected_formatter___boxed), 7, 2);
lean_closure_set(v___x_2122_, 0, v___x_2121_);
lean_closure_set(v___x_2122_, 1, v___x_2120_);
return v___x_2122_;
}
}
lean_object* l_Lake_Toml_key_formatter(lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; lean_object* v___x_2130_; uint8_t v___x_2131_; lean_object* v___x_2132_; 
v___x_2128_ = ((lean_object*)(l_Lake_Toml_key___closed__0));
v___x_2129_ = ((lean_object*)(l_Lake_Toml_key___closed__1));
v___x_2130_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__4, &l_Lake_Toml_key_formatter___closed__4_once, _init_l_Lake_Toml_key_formatter___closed__4);
v___x_2131_ = 1;
v___x_2132_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2128_, v___x_2129_, v___x_2130_, v___x_2131_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
return v___x_2132_;
}
}
LEAN_EXPORT void l_Lake_Toml_key_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2123_ = stack[0].m_obj;
lean_object* v_a_2124_ = stack[1].m_obj;
lean_object* v_a_2125_ = stack[2].m_obj;
lean_object* v_a_2126_ = stack[3].m_obj;
lean_object* v_res_2133_;
v_res_2133_ = l_Lake_Toml_key_formatter(v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
stack->m_obj
 = v_res_2133_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_key_formatter___boxed(lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_, lean_object* v_a_2137_, lean_object* v_a_2138_){
_start:
{
lean_object* v_res_2139_; 
v_res_2139_ = l_Lake_Toml_key_formatter(v_a_2134_, v_a_2135_, v_a_2136_, v_a_2137_);
lean_dec(v_a_2137_);
lean_dec_ref(v_a_2136_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
return v_res_2139_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_2140_; lean_object* v___x_2141_; 
v___x_2140_ = 61;
v___x_2141_ = lean_box_uint32(v___x_2140_);
return v___x_2141_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0(void){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2144_; lean_object* v___x_2145_; 
v___x_2142_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2143_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3));
v___x_2144_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1;
v___x_2145_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2145_, 0, v___x_2144_);
lean_closure_set(v___x_2145_, 1, v___x_2143_);
lean_closure_set(v___x_2145_, 2, v___x_2142_);
return v___x_2145_;
}
}
lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter(lean_object* v_val_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; lean_object* v___x_2160_; uint8_t v___x_2161_; lean_object* v___x_2162_; 
v___x_2152_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0));
v___x_2153_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1));
v___x_2154_ = lean_alloc_closure((void*)(l_Lake_Toml_key_formatter___boxed), 5, 0);
v___x_2155_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2156_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0);
lean_inc_ref(v___x_2155_);
v___x_2157_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2157_, 0, v___x_2155_);
lean_closure_set(v___x_2157_, 1, v_val_2146_);
v___x_2158_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2158_, 0, v___x_2156_);
lean_closure_set(v___x_2158_, 1, v___x_2157_);
v___x_2159_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2159_, 0, v___x_2155_);
lean_closure_set(v___x_2159_, 1, v___x_2158_);
v___x_2160_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2160_, 0, v___x_2154_);
lean_closure_set(v___x_2160_, 1, v___x_2159_);
v___x_2161_ = 1;
v___x_2162_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2152_, v___x_2153_, v___x_2160_, v___x_2161_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
return v___x_2162_;
}
}
LEAN_EXPORT void l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2146_ = stack[0].m_obj;
lean_object* v_a_2147_ = stack[1].m_obj;
lean_object* v_a_2148_ = stack[2].m_obj;
lean_object* v_a_2149_ = stack[3].m_obj;
lean_object* v_a_2150_ = stack[4].m_obj;
lean_object* v_res_2163_;
v_res_2163_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter(v_val_2146_, v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
stack->m_obj
 = v_res_2163_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___boxed(lean_object* v_val_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_, lean_object* v_a_2167_, lean_object* v_a_2168_, lean_object* v_a_2169_){
_start:
{
lean_object* v_res_2170_; 
v_res_2170_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter(v_val_2164_, v_a_2165_, v_a_2166_, v_a_2167_, v_a_2168_);
lean_dec(v_a_2168_);
lean_dec_ref(v_a_2167_);
lean_dec(v_a_2166_);
lean_dec_ref(v_a_2165_);
return v_res_2170_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_2171_; lean_object* v___x_2172_; 
v___x_2171_ = 91;
v___x_2172_ = lean_box_uint32(v___x_2171_);
return v___x_2172_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__0(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; 
v___x_2173_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2174_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__3));
v___x_2175_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
v___x_2176_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2176_, 0, v___x_2175_);
lean_closure_set(v___x_2176_, 1, v___x_2174_);
lean_closure_set(v___x_2176_, 2, v___x_2173_);
return v___x_2176_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__1(void){
_start:
{
lean_object* v___x_2177_; lean_object* v___x_2178_; lean_object* v___x_2179_; lean_object* v___x_2180_; 
v___x_2177_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2178_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__6));
v___x_2179_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
v___x_2180_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2180_, 0, v___x_2179_);
lean_closure_set(v___x_2180_, 1, v___x_2178_);
lean_closure_set(v___x_2180_, 2, v___x_2177_);
return v___x_2180_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__2(void){
_start:
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
v___x_2181_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__1, &l_Lake_Toml_stdTable_formatter___closed__1_once, _init_l_Lake_Toml_stdTable_formatter___closed__1);
v___x_2182_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed), 6, 1);
lean_closure_set(v___x_2182_, 0, v___x_2181_);
return v___x_2182_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__3(void){
_start:
{
lean_object* v___x_2183_; lean_object* v___x_2184_; lean_object* v___x_2185_; 
v___x_2183_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__2, &l_Lake_Toml_stdTable_formatter___closed__2_once, _init_l_Lake_Toml_stdTable_formatter___closed__2);
v___x_2184_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__0, &l_Lake_Toml_stdTable_formatter___closed__0_once, _init_l_Lake_Toml_stdTable_formatter___closed__0);
v___x_2185_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2185_, 0, v___x_2184_);
lean_closure_set(v___x_2185_, 1, v___x_2183_);
return v___x_2185_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__4(void){
_start:
{
lean_object* v___x_2186_; lean_object* v___x_2187_; 
v___x_2186_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__3, &l_Lake_Toml_stdTable_formatter___closed__3_once, _init_l_Lake_Toml_stdTable_formatter___closed__3);
v___x_2187_ = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter___boxed), 6, 1);
lean_closure_set(v___x_2187_, 0, v___x_2186_);
return v___x_2187_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1(void){
_start:
{
uint32_t v___x_2188_; lean_object* v___x_2189_; 
v___x_2188_ = 93;
v___x_2189_ = lean_box_uint32(v___x_2188_);
return v___x_2189_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__5(void){
_start:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; lean_object* v___x_2192_; lean_object* v___x_2193_; 
v___x_2190_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2191_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__12));
v___x_2192_ = l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1;
v___x_2193_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2193_, 0, v___x_2192_);
lean_closure_set(v___x_2193_, 1, v___x_2191_);
lean_closure_set(v___x_2193_, 2, v___x_2190_);
return v___x_2193_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__6(void){
_start:
{
lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; 
v___x_2194_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__5, &l_Lake_Toml_stdTable_formatter___closed__5_once, _init_l_Lake_Toml_stdTable_formatter___closed__5);
v___x_2195_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2196_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2196_, 0, v___x_2195_);
lean_closure_set(v___x_2196_, 1, v___x_2194_);
return v___x_2196_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__7(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__6, &l_Lake_Toml_stdTable_formatter___closed__6_once, _init_l_Lake_Toml_stdTable_formatter___closed__6);
v___x_2198_ = lean_alloc_closure((void*)(l_Lake_Toml_key_formatter___boxed), 5, 0);
v___x_2199_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2199_, 0, v___x_2198_);
lean_closure_set(v___x_2199_, 1, v___x_2197_);
return v___x_2199_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__8(void){
_start:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2200_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__7, &l_Lake_Toml_stdTable_formatter___closed__7_once, _init_l_Lake_Toml_stdTable_formatter___closed__7);
v___x_2201_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2202_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2202_, 0, v___x_2201_);
lean_closure_set(v___x_2202_, 1, v___x_2200_);
return v___x_2202_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__9(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
v___x_2203_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__8, &l_Lake_Toml_stdTable_formatter___closed__8_once, _init_l_Lake_Toml_stdTable_formatter___closed__8);
v___x_2204_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__4, &l_Lake_Toml_stdTable_formatter___closed__4_once, _init_l_Lake_Toml_stdTable_formatter___closed__4);
v___x_2205_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2205_, 0, v___x_2204_);
lean_closure_set(v___x_2205_, 1, v___x_2203_);
return v___x_2205_;
}
}
lean_object* l_Lake_Toml_stdTable_formatter(lean_object* v_a_2206_, lean_object* v_a_2207_, lean_object* v_a_2208_, lean_object* v_a_2209_){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; uint8_t v___x_2214_; lean_object* v___x_2215_; 
v___x_2211_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__0));
v___x_2212_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__1));
v___x_2213_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__9, &l_Lake_Toml_stdTable_formatter___closed__9_once, _init_l_Lake_Toml_stdTable_formatter___closed__9);
v___x_2214_ = 0;
v___x_2215_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2211_, v___x_2212_, v___x_2213_, v___x_2214_, v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_);
return v___x_2215_;
}
}
LEAN_EXPORT void l_Lake_Toml_stdTable_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2206_ = stack[0].m_obj;
lean_object* v_a_2207_ = stack[1].m_obj;
lean_object* v_a_2208_ = stack[2].m_obj;
lean_object* v_a_2209_ = stack[3].m_obj;
lean_object* v_res_2216_;
v_res_2216_ = l_Lake_Toml_stdTable_formatter(v_a_2206_, v_a_2207_, v_a_2208_, v_a_2209_);
stack->m_obj
 = v_res_2216_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_formatter___boxed(lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_){
_start:
{
lean_object* v_res_2222_; 
v_res_2222_ = l_Lake_Toml_stdTable_formatter(v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
lean_dec(v_a_2220_);
lean_dec_ref(v_a_2219_);
lean_dec(v_a_2218_);
lean_dec_ref(v_a_2217_);
return v_res_2222_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__0(void){
_start:
{
lean_object* v___x_2223_; lean_object* v___x_2224_; lean_object* v___x_2225_; 
v___x_2223_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__1, &l_Lake_Toml_stdTable_formatter___closed__1_once, _init_l_Lake_Toml_stdTable_formatter___closed__1);
v___x_2224_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__0, &l_Lake_Toml_stdTable_formatter___closed__0_once, _init_l_Lake_Toml_stdTable_formatter___closed__0);
v___x_2225_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2225_, 0, v___x_2224_);
lean_closure_set(v___x_2225_, 1, v___x_2223_);
return v___x_2225_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__1(void){
_start:
{
lean_object* v___x_2226_; lean_object* v___x_2227_; 
v___x_2226_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__0, &l_Lake_Toml_arrayTable_formatter___closed__0_once, _init_l_Lake_Toml_arrayTable_formatter___closed__0);
v___x_2227_ = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter___boxed), 6, 1);
lean_closure_set(v___x_2227_, 0, v___x_2226_);
return v___x_2227_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__2(void){
_start:
{
lean_object* v___x_2228_; lean_object* v___x_2229_; 
v___x_2228_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__5, &l_Lake_Toml_stdTable_formatter___closed__5_once, _init_l_Lake_Toml_stdTable_formatter___closed__5);
v___x_2229_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2229_, 0, v___x_2228_);
lean_closure_set(v___x_2229_, 1, v___x_2228_);
return v___x_2229_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__3(void){
_start:
{
lean_object* v___x_2230_; lean_object* v___x_2231_; lean_object* v___x_2232_; 
v___x_2230_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__2, &l_Lake_Toml_arrayTable_formatter___closed__2_once, _init_l_Lake_Toml_arrayTable_formatter___closed__2);
v___x_2231_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2232_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2232_, 0, v___x_2231_);
lean_closure_set(v___x_2232_, 1, v___x_2230_);
return v___x_2232_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__4(void){
_start:
{
lean_object* v___x_2233_; lean_object* v___x_2234_; lean_object* v___x_2235_; 
v___x_2233_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__3, &l_Lake_Toml_arrayTable_formatter___closed__3_once, _init_l_Lake_Toml_arrayTable_formatter___closed__3);
v___x_2234_ = lean_alloc_closure((void*)(l_Lake_Toml_key_formatter___boxed), 5, 0);
v___x_2235_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2235_, 0, v___x_2234_);
lean_closure_set(v___x_2235_, 1, v___x_2233_);
return v___x_2235_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__5(void){
_start:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; 
v___x_2236_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__4, &l_Lake_Toml_arrayTable_formatter___closed__4_once, _init_l_Lake_Toml_arrayTable_formatter___closed__4);
v___x_2237_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2238_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2238_, 0, v___x_2237_);
lean_closure_set(v___x_2238_, 1, v___x_2236_);
return v___x_2238_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__6(void){
_start:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; 
v___x_2239_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__5, &l_Lake_Toml_arrayTable_formatter___closed__5_once, _init_l_Lake_Toml_arrayTable_formatter___closed__5);
v___x_2240_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__1, &l_Lake_Toml_arrayTable_formatter___closed__1_once, _init_l_Lake_Toml_arrayTable_formatter___closed__1);
v___x_2241_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2241_, 0, v___x_2240_);
lean_closure_set(v___x_2241_, 1, v___x_2239_);
return v___x_2241_;
}
}
lean_object* l_Lake_Toml_arrayTable_formatter(lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; uint8_t v___x_2250_; lean_object* v___x_2251_; 
v___x_2247_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__0));
v___x_2248_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__1));
v___x_2249_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__6, &l_Lake_Toml_arrayTable_formatter___closed__6_once, _init_l_Lake_Toml_arrayTable_formatter___closed__6);
v___x_2250_ = 0;
v___x_2251_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2247_, v___x_2248_, v___x_2249_, v___x_2250_, v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_);
return v___x_2251_;
}
}
LEAN_EXPORT void l_Lake_Toml_arrayTable_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2242_ = stack[0].m_obj;
lean_object* v_a_2243_ = stack[1].m_obj;
lean_object* v_a_2244_ = stack[2].m_obj;
lean_object* v_a_2245_ = stack[3].m_obj;
lean_object* v_res_2252_;
v_res_2252_ = l_Lake_Toml_arrayTable_formatter(v_a_2242_, v_a_2243_, v_a_2244_, v_a_2245_);
stack->m_obj
 = v_res_2252_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_formatter___boxed(lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v_res_2258_; 
v_res_2258_ = l_Lake_Toml_arrayTable_formatter(v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
lean_dec(v_a_2256_);
lean_dec_ref(v_a_2255_);
lean_dec(v_a_2254_);
lean_dec_ref(v_a_2253_);
return v_res_2258_;
}
}
lean_object* l_Lake_Toml_table_formatter(lean_object* v_a_2259_, lean_object* v_a_2260_, lean_object* v_a_2261_, lean_object* v_a_2262_){
_start:
{
lean_object* v___x_2264_; lean_object* v___x_2265_; lean_object* v___x_2266_; 
v___x_2264_ = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_formatter___boxed), 5, 0);
v___x_2265_ = lean_alloc_closure((void*)(l_Lake_Toml_arrayTable_formatter___boxed), 5, 0);
v___x_2266_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2264_, v___x_2265_, v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
return v___x_2266_;
}
}
LEAN_EXPORT void l_Lake_Toml_table_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2259_ = stack[0].m_obj;
lean_object* v_a_2260_ = stack[1].m_obj;
lean_object* v_a_2261_ = stack[2].m_obj;
lean_object* v_a_2262_ = stack[3].m_obj;
lean_object* v_res_2267_;
v_res_2267_ = l_Lake_Toml_table_formatter(v_a_2259_, v_a_2260_, v_a_2261_, v_a_2262_);
stack->m_obj
 = v_res_2267_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_table_formatter___boxed(lean_object* v_a_2268_, lean_object* v_a_2269_, lean_object* v_a_2270_, lean_object* v_a_2271_, lean_object* v_a_2272_){
_start:
{
lean_object* v_res_2273_; 
v_res_2273_ = l_Lake_Toml_table_formatter(v_a_2268_, v_a_2269_, v_a_2270_, v_a_2271_);
lean_dec(v_a_2271_);
lean_dec_ref(v_a_2270_);
lean_dec(v_a_2269_);
lean_dec_ref(v_a_2268_);
return v_res_2273_;
}
}
lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter(lean_object* v_val_2280_, lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_){
_start:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2286_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___closed__0));
v___x_2287_ = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___boxed), 6, 1);
lean_closure_set(v___x_2287_, 0, v_val_2280_);
v___x_2288_ = lean_alloc_closure((void*)(l_Lake_Toml_table_formatter___boxed), 5, 0);
v___x_2289_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2289_, 0, v___x_2287_);
lean_closure_set(v___x_2289_, 1, v___x_2288_);
v___x_2290_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2286_, v___x_2289_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_);
return v___x_2290_;
}
}
LEAN_EXPORT void l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2280_ = stack[0].m_obj;
lean_object* v_a_2281_ = stack[1].m_obj;
lean_object* v_a_2282_ = stack[2].m_obj;
lean_object* v_a_2283_ = stack[3].m_obj;
lean_object* v_a_2284_ = stack[4].m_obj;
lean_object* v_res_2291_;
v_res_2291_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter(v_val_2280_, v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_);
stack->m_obj
 = v_res_2291_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___boxed(lean_object* v_val_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter(v_val_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
return v_res_2298_;
}
}
lean_object* l_Lake_Toml_trailingSep_formatter___redArg(){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_2300_;
}
}
LEAN_EXPORT void l_Lake_Toml_trailingSep_formatter___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2301_;
v_res_2301_ = l_Lake_Toml_trailingSep_formatter___redArg();
stack->m_obj
 = v_res_2301_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter___redArg___boxed(lean_object* v_a_2302_){
_start:
{
lean_object* v_res_2303_; 
v_res_2303_ = l_Lake_Toml_trailingSep_formatter___redArg();
return v_res_2303_;
}
}
lean_object* l_Lake_Toml_trailingSep_formatter(lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_){
_start:
{
lean_object* v___x_2309_; 
v___x_2309_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_2309_;
}
}
LEAN_EXPORT void l_Lake_Toml_trailingSep_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2304_ = stack[0].m_obj;
lean_object* v_a_2305_ = stack[1].m_obj;
lean_object* v_a_2306_ = stack[2].m_obj;
lean_object* v_a_2307_ = stack[3].m_obj;
lean_object* v_res_2310_;
v_res_2310_ = l_Lake_Toml_trailingSep_formatter(v_a_2304_, v_a_2305_, v_a_2306_, v_a_2307_);
stack->m_obj
 = v_res_2310_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter___boxed(lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_){
_start:
{
lean_object* v_res_2316_; 
v_res_2316_ = l_Lake_Toml_trailingSep_formatter(v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
lean_dec(v_a_2312_);
lean_dec_ref(v_a_2311_);
return v_res_2316_;
}
}
lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(lean_object* v_val_2317_, lean_object* v_a_2318_, lean_object* v_a_2319_, lean_object* v_a_2320_, lean_object* v_a_2321_){
_start:
{
lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; uint8_t v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2323_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0));
v___x_2324_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1));
v___x_2325_ = lean_alloc_closure((void*)(l_Lake_Toml_header_formatter___boxed), 5, 0);
v___x_2326_ = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___boxed), 6, 1);
lean_closure_set(v___x_2326_, 0, v_val_2317_);
v___x_2327_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingSep_formatter___boxed), 5, 0);
v___x_2328_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2328_, 0, v___x_2326_);
lean_closure_set(v___x_2328_, 1, v___x_2327_);
v___x_2329_ = 1;
v___x_2330_ = lean_box(v___x_2329_);
v___x_2331_ = lean_alloc_closure((void*)(l_Lake_Toml_sepByLinebreak_formatter___boxed), 7, 2);
lean_closure_set(v___x_2331_, 0, v___x_2328_);
lean_closure_set(v___x_2331_, 1, v___x_2330_);
v___x_2332_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2332_, 0, v___x_2325_);
lean_closure_set(v___x_2332_, 1, v___x_2331_);
v___x_2333_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2323_, v___x_2324_, v___x_2332_, v___x_2329_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_);
return v___x_2333_;
}
}
LEAN_EXPORT void l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2317_ = stack[0].m_obj;
lean_object* v_a_2318_ = stack[1].m_obj;
lean_object* v_a_2319_ = stack[2].m_obj;
lean_object* v_a_2320_ = stack[3].m_obj;
lean_object* v_a_2321_ = stack[4].m_obj;
lean_object* v_res_2334_;
v_res_2334_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(v_val_2317_, v_a_2318_, v_a_2319_, v_a_2320_, v_a_2321_);
stack->m_obj
 = v_res_2334_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter___boxed(lean_object* v_val_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_){
_start:
{
lean_object* v_res_2341_; 
v_res_2341_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(v_val_2335_, v_a_2336_, v_a_2337_, v_a_2338_, v_a_2339_);
lean_dec(v_a_2339_);
lean_dec_ref(v_a_2338_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2336_);
return v_res_2341_;
}
}
lean_object* l_Lake_Toml_val_formatter(lean_object* v_a_2342_, lean_object* v_a_2343_, lean_object* v_a_2344_, lean_object* v_a_2345_){
_start:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; lean_object* v___x_2349_; uint8_t v___x_2350_; lean_object* v___x_2351_; 
v___x_2347_ = ((lean_object*)(l_Lake_Toml_val___closed__0));
v___x_2348_ = ((lean_object*)(l_Lake_Toml_val___closed__1));
v___x_2349_ = ((lean_object*)(l_Lake_Toml_val___closed__2));
v___x_2350_ = 1;
v___x_2351_ = l_Lake_Toml_recNodeWithAntiquot_formatter(v___x_2347_, v___x_2348_, v___x_2349_, v___x_2350_, v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
return v___x_2351_;
}
}
LEAN_EXPORT void l_Lake_Toml_val_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2342_ = stack[0].m_obj;
lean_object* v_a_2343_ = stack[1].m_obj;
lean_object* v_a_2344_ = stack[2].m_obj;
lean_object* v_a_2345_ = stack[3].m_obj;
lean_object* v_res_2352_;
v_res_2352_ = l_Lake_Toml_val_formatter(v_a_2342_, v_a_2343_, v_a_2344_, v_a_2345_);
stack->m_obj
 = v_res_2352_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_val_formatter___boxed(lean_object* v_a_2353_, lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_Lake_Toml_val_formatter(v_a_2353_, v_a_2354_, v_a_2355_, v_a_2356_);
lean_dec(v_a_2356_);
lean_dec_ref(v_a_2355_);
lean_dec(v_a_2354_);
lean_dec_ref(v_a_2353_);
return v_res_2358_;
}
}
lean_object* l_Lake_Toml_toml_formatter(lean_object* v_a_2359_, lean_object* v_a_2360_, lean_object* v_a_2361_, lean_object* v_a_2362_){
_start:
{
lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2364_ = lean_alloc_closure((void*)(l_Lake_Toml_val_formatter___boxed), 5, 0);
v___x_2365_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(v___x_2364_, v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
return v___x_2365_;
}
}
LEAN_EXPORT void l_Lake_Toml_toml_formatter_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2359_ = stack[0].m_obj;
lean_object* v_a_2360_ = stack[1].m_obj;
lean_object* v_a_2361_ = stack[2].m_obj;
lean_object* v_a_2362_ = stack[3].m_obj;
lean_object* v_res_2366_;
v_res_2366_ = l_Lake_Toml_toml_formatter(v_a_2359_, v_a_2360_, v_a_2361_, v_a_2362_);
stack->m_obj
 = v_res_2366_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_toml_formatter___boxed(lean_object* v_a_2367_, lean_object* v_a_2368_, lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_){
_start:
{
lean_object* v_res_2372_; 
v_res_2372_ = l_Lake_Toml_toml_formatter(v_a_2367_, v_a_2368_, v_a_2369_, v_a_2370_);
lean_dec(v_a_2370_);
lean_dec_ref(v_a_2369_);
lean_dec(v_a_2368_);
lean_dec_ref(v_a_2367_);
return v_res_2372_;
}
}
lean_object* l_Lake_Toml_header_parenthesizer(lean_object* v_a_2373_, lean_object* v_a_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_){
_start:
{
lean_object* v___x_2378_; lean_object* v___x_2379_; uint8_t v___x_2380_; lean_object* v___x_2381_; 
v___x_2378_ = ((lean_object*)(l_Lake_Toml_header___closed__0));
v___x_2379_ = ((lean_object*)(l_Lake_Toml_header___closed__1));
v___x_2380_ = 0;
v___x_2381_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v___x_2378_, v___x_2379_, v___x_2380_, v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
return v___x_2381_;
}
}
LEAN_EXPORT void l_Lake_Toml_header_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2373_ = stack[0].m_obj;
lean_object* v_a_2374_ = stack[1].m_obj;
lean_object* v_a_2375_ = stack[2].m_obj;
lean_object* v_a_2376_ = stack[3].m_obj;
lean_object* v_res_2382_;
v_res_2382_ = l_Lake_Toml_header_parenthesizer(v_a_2373_, v_a_2374_, v_a_2375_, v_a_2376_);
stack->m_obj
 = v_res_2382_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_header_parenthesizer___boxed(lean_object* v_a_2383_, lean_object* v_a_2384_, lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_){
_start:
{
lean_object* v_res_2388_; 
v_res_2388_ = l_Lake_Toml_header_parenthesizer(v_a_2383_, v_a_2384_, v_a_2385_, v_a_2386_);
lean_dec(v_a_2386_);
lean_dec_ref(v_a_2385_);
lean_dec(v_a_2384_);
lean_dec_ref(v_a_2383_);
return v_res_2388_;
}
}
lean_object* l_Lake_Toml_unquotedKey_parenthesizer(lean_object* v_a_2389_, lean_object* v_a_2390_, lean_object* v_a_2391_, lean_object* v_a_2392_){
_start:
{
lean_object* v___x_2394_; lean_object* v___x_2395_; uint8_t v___x_2396_; lean_object* v___x_2397_; 
v___x_2394_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__0));
v___x_2395_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__1));
v___x_2396_ = 0;
v___x_2397_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v___x_2394_, v___x_2395_, v___x_2396_, v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
return v___x_2397_;
}
}
LEAN_EXPORT void l_Lake_Toml_unquotedKey_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2389_ = stack[0].m_obj;
lean_object* v_a_2390_ = stack[1].m_obj;
lean_object* v_a_2391_ = stack[2].m_obj;
lean_object* v_a_2392_ = stack[3].m_obj;
lean_object* v_res_2398_;
v_res_2398_ = l_Lake_Toml_unquotedKey_parenthesizer(v_a_2389_, v_a_2390_, v_a_2391_, v_a_2392_);
stack->m_obj
 = v_res_2398_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_parenthesizer___boxed(lean_object* v_a_2399_, lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v_res_2404_; 
v_res_2404_ = l_Lake_Toml_unquotedKey_parenthesizer(v_a_2399_, v_a_2400_, v_a_2401_, v_a_2402_);
lean_dec(v_a_2402_);
lean_dec_ref(v_a_2401_);
lean_dec(v_a_2400_);
lean_dec_ref(v_a_2399_);
return v_res_2404_;
}
}
lean_object* l_Lake_Toml_basicString_parenthesizer(lean_object* v_a_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_){
_start:
{
lean_object* v___x_2410_; lean_object* v___x_2411_; uint8_t v___x_2412_; lean_object* v___x_2413_; 
v___x_2410_ = ((lean_object*)(l_Lake_Toml_basicString___closed__0));
v___x_2411_ = ((lean_object*)(l_Lake_Toml_basicString___closed__1));
v___x_2412_ = 0;
v___x_2413_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v___x_2410_, v___x_2411_, v___x_2412_, v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
return v___x_2413_;
}
}
LEAN_EXPORT void l_Lake_Toml_basicString_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2405_ = stack[0].m_obj;
lean_object* v_a_2406_ = stack[1].m_obj;
lean_object* v_a_2407_ = stack[2].m_obj;
lean_object* v_a_2408_ = stack[3].m_obj;
lean_object* v_res_2414_;
v_res_2414_ = l_Lake_Toml_basicString_parenthesizer(v_a_2405_, v_a_2406_, v_a_2407_, v_a_2408_);
stack->m_obj
 = v_res_2414_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_parenthesizer___boxed(lean_object* v_a_2415_, lean_object* v_a_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_Lake_Toml_basicString_parenthesizer(v_a_2415_, v_a_2416_, v_a_2417_, v_a_2418_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
lean_dec(v_a_2416_);
lean_dec_ref(v_a_2415_);
return v_res_2420_;
}
}
lean_object* l_Lake_Toml_literalString_parenthesizer(lean_object* v_a_2421_, lean_object* v_a_2422_, lean_object* v_a_2423_, lean_object* v_a_2424_){
_start:
{
lean_object* v___x_2426_; lean_object* v___x_2427_; uint8_t v___x_2428_; lean_object* v___x_2429_; 
v___x_2426_ = ((lean_object*)(l_Lake_Toml_literalString___closed__0));
v___x_2427_ = ((lean_object*)(l_Lake_Toml_literalString___closed__1));
v___x_2428_ = 0;
v___x_2429_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v___x_2426_, v___x_2427_, v___x_2428_, v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
return v___x_2429_;
}
}
LEAN_EXPORT void l_Lake_Toml_literalString_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2421_ = stack[0].m_obj;
lean_object* v_a_2422_ = stack[1].m_obj;
lean_object* v_a_2423_ = stack[2].m_obj;
lean_object* v_a_2424_ = stack[3].m_obj;
lean_object* v_res_2430_;
v_res_2430_ = l_Lake_Toml_literalString_parenthesizer(v_a_2421_, v_a_2422_, v_a_2423_, v_a_2424_);
stack->m_obj
 = v_res_2430_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_parenthesizer___boxed(lean_object* v_a_2431_, lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lake_Toml_literalString_parenthesizer(v_a_2431_, v_a_2432_, v_a_2433_, v_a_2434_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
lean_dec(v_a_2432_);
lean_dec_ref(v_a_2431_);
return v_res_2436_;
}
}
lean_object* l_Lake_Toml_quotedKey_parenthesizer(lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v___x_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; 
v___x_2442_ = lean_alloc_closure((void*)(l_Lake_Toml_basicString_parenthesizer___boxed), 5, 0);
v___x_2443_ = lean_alloc_closure((void*)(l_Lake_Toml_literalString_parenthesizer___boxed), 5, 0);
v___x_2444_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___x_2442_, v___x_2443_, v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
return v___x_2444_;
}
}
LEAN_EXPORT void l_Lake_Toml_quotedKey_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2437_ = stack[0].m_obj;
lean_object* v_a_2438_ = stack[1].m_obj;
lean_object* v_a_2439_ = stack[2].m_obj;
lean_object* v_a_2440_ = stack[3].m_obj;
lean_object* v_res_2445_;
v_res_2445_ = l_Lake_Toml_quotedKey_parenthesizer(v_a_2437_, v_a_2438_, v_a_2439_, v_a_2440_);
stack->m_obj
 = v_res_2445_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_parenthesizer___boxed(lean_object* v_a_2446_, lean_object* v_a_2447_, lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lake_Toml_quotedKey_parenthesizer(v_a_2446_, v_a_2447_, v_a_2448_, v_a_2449_);
lean_dec(v_a_2449_);
lean_dec_ref(v_a_2448_);
lean_dec(v_a_2447_);
lean_dec_ref(v_a_2446_);
return v_res_2451_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2452_ = lean_alloc_closure((void*)(l_Lake_Toml_quotedKey_parenthesizer___boxed), 5, 0);
v___x_2453_ = lean_alloc_closure((void*)(l_Lake_Toml_unquotedKey_parenthesizer___boxed), 5, 0);
v___x_2454_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2454_, 0, v___x_2453_);
lean_closure_set(v___x_2454_, 1, v___x_2452_);
return v___x_2454_;
}
}
lean_object* l_Lake_Toml_simpleKey_parenthesizer(lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_){
_start:
{
lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; uint8_t v___x_2463_; lean_object* v___x_2464_; 
v___x_2460_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__0));
v___x_2461_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__1));
v___x_2462_ = lean_obj_once(&l_Lake_Toml_simpleKey_parenthesizer___closed__0, &l_Lake_Toml_simpleKey_parenthesizer___closed__0_once, _init_l_Lake_Toml_simpleKey_parenthesizer___closed__0);
v___x_2463_ = 1;
v___x_2464_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2460_, v___x_2461_, v___x_2462_, v___x_2463_, v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_);
return v___x_2464_;
}
}
LEAN_EXPORT void l_Lake_Toml_simpleKey_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2455_ = stack[0].m_obj;
lean_object* v_a_2456_ = stack[1].m_obj;
lean_object* v_a_2457_ = stack[2].m_obj;
lean_object* v_a_2458_ = stack[3].m_obj;
lean_object* v_res_2465_;
v_res_2465_ = l_Lake_Toml_simpleKey_parenthesizer(v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_);
stack->m_obj
 = v_res_2465_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_parenthesizer___boxed(lean_object* v_a_2466_, lean_object* v_a_2467_, lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_){
_start:
{
lean_object* v_res_2471_; 
v_res_2471_ = l_Lake_Toml_simpleKey_parenthesizer(v_a_2466_, v_a_2467_, v_a_2468_, v_a_2469_);
lean_dec(v_a_2469_);
lean_dec_ref(v_a_2468_);
lean_dec(v_a_2467_);
lean_dec_ref(v_a_2466_);
return v_res_2471_;
}
}
lean_object* l_Lake_Toml_trailingWs_parenthesizer___redArg(){
_start:
{
lean_object* v___x_2473_; 
v___x_2473_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_2473_;
}
}
LEAN_EXPORT void l_Lake_Toml_trailingWs_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2474_;
v_res_2474_ = l_Lake_Toml_trailingWs_parenthesizer___redArg();
stack->m_obj
 = v_res_2474_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer___redArg___boxed(lean_object* v_a_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Lake_Toml_trailingWs_parenthesizer___redArg();
return v_res_2476_;
}
}
lean_object* l_Lake_Toml_trailingWs_parenthesizer(lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_){
_start:
{
lean_object* v___x_2482_; 
v___x_2482_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_2482_;
}
}
LEAN_EXPORT void l_Lake_Toml_trailingWs_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2477_ = stack[0].m_obj;
lean_object* v_a_2478_ = stack[1].m_obj;
lean_object* v_a_2479_ = stack[2].m_obj;
lean_object* v_a_2480_ = stack[3].m_obj;
lean_object* v_res_2483_;
v_res_2483_ = l_Lake_Toml_trailingWs_parenthesizer(v_a_2477_, v_a_2478_, v_a_2479_, v_a_2480_);
stack->m_obj
 = v_res_2483_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer___boxed(lean_object* v_a_2484_, lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_Lake_Toml_trailingWs_parenthesizer(v_a_2484_, v_a_2485_, v_a_2486_, v_a_2487_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
lean_dec(v_a_2485_);
lean_dec_ref(v_a_2484_);
return v_res_2489_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; lean_object* v___x_2493_; 
v___x_2490_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2491_ = ((lean_object*)(l_Lake_Toml_key___closed__5));
v___x_2492_ = l_Lake_Toml_key_formatter___closed__0___boxed__const__1;
v___x_2493_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2493_, 0, v___x_2492_);
lean_closure_set(v___x_2493_, 1, v___x_2491_);
lean_closure_set(v___x_2493_, 2, v___x_2490_);
return v___x_2493_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; 
v___x_2494_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2495_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__0, &l_Lake_Toml_key_parenthesizer___closed__0_once, _init_l_Lake_Toml_key_parenthesizer___closed__0);
v___x_2496_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2496_, 0, v___x_2495_);
lean_closure_set(v___x_2496_, 1, v___x_2494_);
return v___x_2496_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; 
v___x_2497_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__1, &l_Lake_Toml_key_parenthesizer___closed__1_once, _init_l_Lake_Toml_key_parenthesizer___closed__1);
v___x_2498_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2499_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2499_, 0, v___x_2498_);
lean_closure_set(v___x_2499_, 1, v___x_2497_);
return v___x_2499_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__3(void){
_start:
{
uint8_t v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; lean_object* v___x_2503_; lean_object* v___x_2504_; lean_object* v___x_2505_; 
v___x_2500_ = 0;
v___x_2501_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__2, &l_Lake_Toml_key_parenthesizer___closed__2_once, _init_l_Lake_Toml_key_parenthesizer___closed__2);
v___x_2502_ = ((lean_object*)(l_Lake_Toml_key___closed__3));
v___x_2503_ = lean_alloc_closure((void*)(l_Lake_Toml_simpleKey_parenthesizer___boxed), 5, 0);
v___x_2504_ = lean_box(v___x_2500_);
v___x_2505_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_2505_, 0, v___x_2503_);
lean_closure_set(v___x_2505_, 1, v___x_2502_);
lean_closure_set(v___x_2505_, 2, v___x_2501_);
lean_closure_set(v___x_2505_, 3, v___x_2504_);
return v___x_2505_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2506_; lean_object* v___x_2507_; lean_object* v___x_2508_; 
v___x_2506_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__3, &l_Lake_Toml_key_parenthesizer___closed__3_once, _init_l_Lake_Toml_key_parenthesizer___closed__3);
v___x_2507_ = ((lean_object*)(l_Lake_Toml_key___closed__2));
v___x_2508_ = lean_alloc_closure((void*)(l_Lean_Parser_setExpected_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2508_, 0, v___x_2507_);
lean_closure_set(v___x_2508_, 1, v___x_2506_);
return v___x_2508_;
}
}
lean_object* l_Lake_Toml_key_parenthesizer(lean_object* v_a_2509_, lean_object* v_a_2510_, lean_object* v_a_2511_, lean_object* v_a_2512_){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; uint8_t v___x_2517_; lean_object* v___x_2518_; 
v___x_2514_ = ((lean_object*)(l_Lake_Toml_key___closed__0));
v___x_2515_ = ((lean_object*)(l_Lake_Toml_key___closed__1));
v___x_2516_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__4, &l_Lake_Toml_key_parenthesizer___closed__4_once, _init_l_Lake_Toml_key_parenthesizer___closed__4);
v___x_2517_ = 1;
v___x_2518_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2514_, v___x_2515_, v___x_2516_, v___x_2517_, v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
return v___x_2518_;
}
}
LEAN_EXPORT void l_Lake_Toml_key_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2509_ = stack[0].m_obj;
lean_object* v_a_2510_ = stack[1].m_obj;
lean_object* v_a_2511_ = stack[2].m_obj;
lean_object* v_a_2512_ = stack[3].m_obj;
lean_object* v_res_2519_;
v_res_2519_ = l_Lake_Toml_key_parenthesizer(v_a_2509_, v_a_2510_, v_a_2511_, v_a_2512_);
stack->m_obj
 = v_res_2519_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_key_parenthesizer___boxed(lean_object* v_a_2520_, lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l_Lake_Toml_key_parenthesizer(v_a_2520_, v_a_2521_, v_a_2522_, v_a_2523_);
lean_dec(v_a_2523_);
lean_dec_ref(v_a_2522_);
lean_dec(v_a_2521_);
lean_dec_ref(v_a_2520_);
return v_res_2525_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2526_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2527_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3));
v___x_2528_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1;
v___x_2529_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2529_, 0, v___x_2528_);
lean_closure_set(v___x_2529_, 1, v___x_2527_);
lean_closure_set(v___x_2529_, 2, v___x_2526_);
return v___x_2529_;
}
}
lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer(lean_object* v_val_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; uint8_t v___x_2545_; lean_object* v___x_2546_; 
v___x_2536_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0));
v___x_2537_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1));
v___x_2538_ = lean_alloc_closure((void*)(l_Lake_Toml_key_parenthesizer___boxed), 5, 0);
v___x_2539_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2540_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0);
lean_inc_ref(v___x_2539_);
v___x_2541_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2541_, 0, v___x_2539_);
lean_closure_set(v___x_2541_, 1, v_val_2530_);
v___x_2542_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2542_, 0, v___x_2540_);
lean_closure_set(v___x_2542_, 1, v___x_2541_);
v___x_2543_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2543_, 0, v___x_2539_);
lean_closure_set(v___x_2543_, 1, v___x_2542_);
v___x_2544_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2544_, 0, v___x_2538_);
lean_closure_set(v___x_2544_, 1, v___x_2543_);
v___x_2545_ = 1;
v___x_2546_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2536_, v___x_2537_, v___x_2544_, v___x_2545_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
return v___x_2546_;
}
}
LEAN_EXPORT void l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2530_ = stack[0].m_obj;
lean_object* v_a_2531_ = stack[1].m_obj;
lean_object* v_a_2532_ = stack[2].m_obj;
lean_object* v_a_2533_ = stack[3].m_obj;
lean_object* v_a_2534_ = stack[4].m_obj;
lean_object* v_res_2547_;
v_res_2547_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer(v_val_2530_, v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
stack->m_obj
 = v_res_2547_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___boxed(lean_object* v_val_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_, lean_object* v_a_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer(v_val_2548_, v_a_2549_, v_a_2550_, v_a_2551_, v_a_2552_);
lean_dec(v_a_2552_);
lean_dec_ref(v_a_2551_);
lean_dec(v_a_2550_);
lean_dec_ref(v_a_2549_);
return v_res_2554_;
}
}
lean_object* l_Lake_Toml_stdTable_parenthesizer___lam__0(lean_object* v___x_2555_, lean_object* v___x_2556_, lean_object* v___y_2557_, lean_object* v___y_2558_, lean_object* v___y_2559_, lean_object* v___y_2560_){
_start:
{
lean_object* v___x_2562_; 
v___x_2562_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(v___x_2555_, v___x_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
return v___x_2562_;
}
}
LEAN_EXPORT void l_Lake_Toml_stdTable_parenthesizer___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_2555_ = stack[0].m_obj;
lean_object* v___x_2556_ = stack[1].m_obj;
lean_object* v___y_2557_ = stack[2].m_obj;
lean_object* v___y_2558_ = stack[3].m_obj;
lean_object* v___y_2559_ = stack[4].m_obj;
lean_object* v___y_2560_ = stack[5].m_obj;
lean_object* v_res_2563_;
v_res_2563_ = l_Lake_Toml_stdTable_parenthesizer___lam__0(v___x_2555_, v___x_2556_, v___y_2557_, v___y_2558_, v___y_2559_, v___y_2560_);
stack->m_obj
 = v_res_2563_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer___lam__0___boxed(lean_object* v___x_2564_, lean_object* v___x_2565_, lean_object* v___y_2566_, lean_object* v___y_2567_, lean_object* v___y_2568_, lean_object* v___y_2569_, lean_object* v___y_2570_){
_start:
{
lean_object* v_res_2571_; 
v_res_2571_ = l_Lake_Toml_stdTable_parenthesizer___lam__0(v___x_2564_, v___x_2565_, v___y_2566_, v___y_2567_, v___y_2568_, v___y_2569_);
lean_dec(v___y_2569_);
lean_dec_ref(v___y_2568_);
lean_dec(v___y_2567_);
lean_dec_ref(v___y_2566_);
return v_res_2571_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___x_2575_; 
v___x_2572_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2573_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__3));
v___x_2574_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
v___x_2575_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2575_, 0, v___x_2574_);
lean_closure_set(v___x_2575_, 1, v___x_2573_);
lean_closure_set(v___x_2575_, 2, v___x_2572_);
return v___x_2575_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2576_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2577_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__6));
v___x_2578_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
v___x_2579_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2579_, 0, v___x_2578_);
lean_closure_set(v___x_2579_, 1, v___x_2577_);
lean_closure_set(v___x_2579_, 2, v___x_2576_);
return v___x_2579_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2580_; lean_object* v___x_2581_; 
v___x_2580_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__1, &l_Lake_Toml_stdTable_parenthesizer___closed__1_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__1);
v___x_2581_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2581_, 0, v___x_2580_);
return v___x_2581_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___f_2584_; 
v___x_2582_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__2, &l_Lake_Toml_stdTable_parenthesizer___closed__2_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__2);
v___x_2583_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__0, &l_Lake_Toml_stdTable_parenthesizer___closed__0_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__0);
v___f_2584_ = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_parenthesizer___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2584_, 0, v___x_2583_);
lean_closure_set(v___f_2584_, 1, v___x_2582_);
return v___f_2584_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2585_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2586_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__12));
v___x_2587_ = l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1;
v___x_2588_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2588_, 0, v___x_2587_);
lean_closure_set(v___x_2588_, 1, v___x_2586_);
lean_closure_set(v___x_2588_, 2, v___x_2585_);
return v___x_2588_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; 
v___x_2589_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__4, &l_Lake_Toml_stdTable_parenthesizer___closed__4_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__4);
v___x_2590_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2591_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2591_, 0, v___x_2590_);
lean_closure_set(v___x_2591_, 1, v___x_2589_);
return v___x_2591_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_2592_; lean_object* v___x_2593_; lean_object* v___x_2594_; 
v___x_2592_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__5, &l_Lake_Toml_stdTable_parenthesizer___closed__5_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__5);
v___x_2593_ = lean_alloc_closure((void*)(l_Lake_Toml_key_parenthesizer___boxed), 5, 0);
v___x_2594_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2594_, 0, v___x_2593_);
lean_closure_set(v___x_2594_, 1, v___x_2592_);
return v___x_2594_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; 
v___x_2595_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__6, &l_Lake_Toml_stdTable_parenthesizer___closed__6_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__6);
v___x_2596_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2597_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2597_, 0, v___x_2596_);
lean_closure_set(v___x_2597_, 1, v___x_2595_);
return v___x_2597_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_2598_; lean_object* v___f_2599_; lean_object* v___x_2600_; 
v___x_2598_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__7, &l_Lake_Toml_stdTable_parenthesizer___closed__7_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__7);
v___f_2599_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__3, &l_Lake_Toml_stdTable_parenthesizer___closed__3_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__3);
v___x_2600_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2600_, 0, v___f_2599_);
lean_closure_set(v___x_2600_, 1, v___x_2598_);
return v___x_2600_;
}
}
lean_object* l_Lake_Toml_stdTable_parenthesizer(lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; uint8_t v___x_2609_; lean_object* v___x_2610_; 
v___x_2606_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__0));
v___x_2607_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__1));
v___x_2608_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__8, &l_Lake_Toml_stdTable_parenthesizer___closed__8_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__8);
v___x_2609_ = 0;
v___x_2610_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2606_, v___x_2607_, v___x_2608_, v___x_2609_, v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_);
return v___x_2610_;
}
}
LEAN_EXPORT void l_Lake_Toml_stdTable_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2601_ = stack[0].m_obj;
lean_object* v_a_2602_ = stack[1].m_obj;
lean_object* v_a_2603_ = stack[2].m_obj;
lean_object* v_a_2604_ = stack[3].m_obj;
lean_object* v_res_2611_;
v_res_2611_ = l_Lake_Toml_stdTable_parenthesizer(v_a_2601_, v_a_2602_, v_a_2603_, v_a_2604_);
stack->m_obj
 = v_res_2611_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer___boxed(lean_object* v_a_2612_, lean_object* v_a_2613_, lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_Lake_Toml_stdTable_parenthesizer(v_a_2612_, v_a_2613_, v_a_2614_, v_a_2615_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
lean_dec(v_a_2613_);
lean_dec_ref(v_a_2612_);
return v_res_2617_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___f_2620_; 
v___x_2618_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__1, &l_Lake_Toml_stdTable_parenthesizer___closed__1_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__1);
v___x_2619_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__0, &l_Lake_Toml_stdTable_parenthesizer___closed__0_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__0);
v___f_2620_ = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_parenthesizer___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2620_, 0, v___x_2619_);
lean_closure_set(v___f_2620_, 1, v___x_2618_);
return v___f_2620_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2621_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__4, &l_Lake_Toml_stdTable_parenthesizer___closed__4_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__4);
v___x_2622_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2622_, 0, v___x_2621_);
lean_closure_set(v___x_2622_, 1, v___x_2621_);
return v___x_2622_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; lean_object* v___x_2625_; 
v___x_2623_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__1, &l_Lake_Toml_arrayTable_parenthesizer___closed__1_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__1);
v___x_2624_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2625_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2625_, 0, v___x_2624_);
lean_closure_set(v___x_2625_, 1, v___x_2623_);
return v___x_2625_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v___x_2626_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__2, &l_Lake_Toml_arrayTable_parenthesizer___closed__2_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__2);
v___x_2627_ = lean_alloc_closure((void*)(l_Lake_Toml_key_parenthesizer___boxed), 5, 0);
v___x_2628_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2628_, 0, v___x_2627_);
lean_closure_set(v___x_2628_, 1, v___x_2626_);
return v___x_2628_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2631_; 
v___x_2629_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__3, &l_Lake_Toml_arrayTable_parenthesizer___closed__3_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__3);
v___x_2630_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2631_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2631_, 0, v___x_2630_);
lean_closure_set(v___x_2631_, 1, v___x_2629_);
return v___x_2631_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_2632_; lean_object* v___f_2633_; lean_object* v___x_2634_; 
v___x_2632_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__4, &l_Lake_Toml_arrayTable_parenthesizer___closed__4_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__4);
v___f_2633_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__0, &l_Lake_Toml_arrayTable_parenthesizer___closed__0_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__0);
v___x_2634_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2634_, 0, v___f_2633_);
lean_closure_set(v___x_2634_, 1, v___x_2632_);
return v___x_2634_;
}
}
lean_object* l_Lake_Toml_arrayTable_parenthesizer(lean_object* v_a_2635_, lean_object* v_a_2636_, lean_object* v_a_2637_, lean_object* v_a_2638_){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; uint8_t v___x_2643_; lean_object* v___x_2644_; 
v___x_2640_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__0));
v___x_2641_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__1));
v___x_2642_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__5, &l_Lake_Toml_arrayTable_parenthesizer___closed__5_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__5);
v___x_2643_ = 0;
v___x_2644_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2640_, v___x_2641_, v___x_2642_, v___x_2643_, v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_);
return v___x_2644_;
}
}
LEAN_EXPORT void l_Lake_Toml_arrayTable_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2635_ = stack[0].m_obj;
lean_object* v_a_2636_ = stack[1].m_obj;
lean_object* v_a_2637_ = stack[2].m_obj;
lean_object* v_a_2638_ = stack[3].m_obj;
lean_object* v_res_2645_;
v_res_2645_ = l_Lake_Toml_arrayTable_parenthesizer(v_a_2635_, v_a_2636_, v_a_2637_, v_a_2638_);
stack->m_obj
 = v_res_2645_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_parenthesizer___boxed(lean_object* v_a_2646_, lean_object* v_a_2647_, lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_){
_start:
{
lean_object* v_res_2651_; 
v_res_2651_ = l_Lake_Toml_arrayTable_parenthesizer(v_a_2646_, v_a_2647_, v_a_2648_, v_a_2649_);
lean_dec(v_a_2649_);
lean_dec_ref(v_a_2648_);
lean_dec(v_a_2647_);
lean_dec_ref(v_a_2646_);
return v_res_2651_;
}
}
lean_object* l_Lake_Toml_table_parenthesizer(lean_object* v_a_2652_, lean_object* v_a_2653_, lean_object* v_a_2654_, lean_object* v_a_2655_){
_start:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; 
v___x_2657_ = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_parenthesizer___boxed), 5, 0);
v___x_2658_ = lean_alloc_closure((void*)(l_Lake_Toml_arrayTable_parenthesizer___boxed), 5, 0);
v___x_2659_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___x_2657_, v___x_2658_, v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
return v___x_2659_;
}
}
LEAN_EXPORT void l_Lake_Toml_table_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2652_ = stack[0].m_obj;
lean_object* v_a_2653_ = stack[1].m_obj;
lean_object* v_a_2654_ = stack[2].m_obj;
lean_object* v_a_2655_ = stack[3].m_obj;
lean_object* v_res_2660_;
v_res_2660_ = l_Lake_Toml_table_parenthesizer(v_a_2652_, v_a_2653_, v_a_2654_, v_a_2655_);
stack->m_obj
 = v_res_2660_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_table_parenthesizer___boxed(lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_){
_start:
{
lean_object* v_res_2666_; 
v_res_2666_ = l_Lake_Toml_table_parenthesizer(v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_);
lean_dec(v_a_2664_);
lean_dec_ref(v_a_2663_);
lean_dec(v_a_2662_);
lean_dec_ref(v_a_2661_);
return v_res_2666_;
}
}
lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer(lean_object* v_val_2673_, lean_object* v_a_2674_, lean_object* v_a_2675_, lean_object* v_a_2676_, lean_object* v_a_2677_){
_start:
{
lean_object* v___x_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2679_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___closed__0));
v___x_2680_ = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2680_, 0, v_val_2673_);
v___x_2681_ = lean_alloc_closure((void*)(l_Lake_Toml_table_parenthesizer___boxed), 5, 0);
v___x_2682_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2682_, 0, v___x_2680_);
lean_closure_set(v___x_2682_, 1, v___x_2681_);
v___x_2683_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2679_, v___x_2682_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
return v___x_2683_;
}
}
LEAN_EXPORT void l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2673_ = stack[0].m_obj;
lean_object* v_a_2674_ = stack[1].m_obj;
lean_object* v_a_2675_ = stack[2].m_obj;
lean_object* v_a_2676_ = stack[3].m_obj;
lean_object* v_a_2677_ = stack[4].m_obj;
lean_object* v_res_2684_;
v_res_2684_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer(v_val_2673_, v_a_2674_, v_a_2675_, v_a_2676_, v_a_2677_);
stack->m_obj
 = v_res_2684_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___boxed(lean_object* v_val_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_, lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer(v_val_2685_, v_a_2686_, v_a_2687_, v_a_2688_, v_a_2689_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
lean_dec(v_a_2687_);
lean_dec_ref(v_a_2686_);
return v_res_2691_;
}
}
lean_object* l_Lake_Toml_trailingSep_parenthesizer___redArg(){
_start:
{
lean_object* v___x_2693_; 
v___x_2693_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_2693_;
}
}
LEAN_EXPORT void l_Lake_Toml_trailingSep_parenthesizer___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2694_;
v_res_2694_ = l_Lake_Toml_trailingSep_parenthesizer___redArg();
stack->m_obj
 = v_res_2694_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer___redArg___boxed(lean_object* v_a_2695_){
_start:
{
lean_object* v_res_2696_; 
v_res_2696_ = l_Lake_Toml_trailingSep_parenthesizer___redArg();
return v_res_2696_;
}
}
lean_object* l_Lake_Toml_trailingSep_parenthesizer(lean_object* v_a_2697_, lean_object* v_a_2698_, lean_object* v_a_2699_, lean_object* v_a_2700_){
_start:
{
lean_object* v___x_2702_; 
v___x_2702_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_2702_;
}
}
LEAN_EXPORT void l_Lake_Toml_trailingSep_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2697_ = stack[0].m_obj;
lean_object* v_a_2698_ = stack[1].m_obj;
lean_object* v_a_2699_ = stack[2].m_obj;
lean_object* v_a_2700_ = stack[3].m_obj;
lean_object* v_res_2703_;
v_res_2703_ = l_Lake_Toml_trailingSep_parenthesizer(v_a_2697_, v_a_2698_, v_a_2699_, v_a_2700_);
stack->m_obj
 = v_res_2703_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer___boxed(lean_object* v_a_2704_, lean_object* v_a_2705_, lean_object* v_a_2706_, lean_object* v_a_2707_, lean_object* v_a_2708_){
_start:
{
lean_object* v_res_2709_; 
v_res_2709_ = l_Lake_Toml_trailingSep_parenthesizer(v_a_2704_, v_a_2705_, v_a_2706_, v_a_2707_);
lean_dec(v_a_2707_);
lean_dec_ref(v_a_2706_);
lean_dec(v_a_2705_);
lean_dec_ref(v_a_2704_);
return v_res_2709_;
}
}
lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(lean_object* v_val_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; uint8_t v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; 
v___x_2716_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0));
v___x_2717_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1));
v___x_2718_ = lean_alloc_closure((void*)(l_Lake_Toml_header_parenthesizer___boxed), 5, 0);
v___x_2719_ = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2719_, 0, v_val_2710_);
v___x_2720_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingSep_parenthesizer___boxed), 5, 0);
v___x_2721_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2721_, 0, v___x_2719_);
lean_closure_set(v___x_2721_, 1, v___x_2720_);
v___x_2722_ = 1;
v___x_2723_ = lean_box(v___x_2722_);
v___x_2724_ = lean_alloc_closure((void*)(l_Lake_Toml_sepByLinebreak_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2724_, 0, v___x_2721_);
lean_closure_set(v___x_2724_, 1, v___x_2723_);
v___x_2725_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2725_, 0, v___x_2718_);
lean_closure_set(v___x_2725_, 1, v___x_2724_);
v___x_2726_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2716_, v___x_2717_, v___x_2725_, v___x_2722_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
return v___x_2726_;
}
}
LEAN_EXPORT void l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_val_2710_ = stack[0].m_obj;
lean_object* v_a_2711_ = stack[1].m_obj;
lean_object* v_a_2712_ = stack[2].m_obj;
lean_object* v_a_2713_ = stack[3].m_obj;
lean_object* v_a_2714_ = stack[4].m_obj;
lean_object* v_res_2727_;
v_res_2727_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(v_val_2710_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
stack->m_obj
 = v_res_2727_;
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer___boxed(lean_object* v_val_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_, lean_object* v_a_2731_, lean_object* v_a_2732_, lean_object* v_a_2733_){
_start:
{
lean_object* v_res_2734_; 
v_res_2734_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(v_val_2728_, v_a_2729_, v_a_2730_, v_a_2731_, v_a_2732_);
lean_dec(v_a_2732_);
lean_dec_ref(v_a_2731_);
lean_dec(v_a_2730_);
lean_dec_ref(v_a_2729_);
return v_res_2734_;
}
}
lean_object* l_Lake_Toml_val_parenthesizer(lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_){
_start:
{
lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; lean_object* v___x_2744_; 
v___x_2740_ = ((lean_object*)(l_Lake_Toml_val___closed__0));
v___x_2741_ = ((lean_object*)(l_Lake_Toml_val___closed__1));
v___x_2742_ = ((lean_object*)(l_Lake_Toml_val___closed__2));
v___x_2743_ = 1;
v___x_2744_ = l_Lake_Toml_recNodeWithAntiquot_parenthesizer(v___x_2740_, v___x_2741_, v___x_2742_, v___x_2743_, v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_);
return v___x_2744_;
}
}
LEAN_EXPORT void l_Lake_Toml_val_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2735_ = stack[0].m_obj;
lean_object* v_a_2736_ = stack[1].m_obj;
lean_object* v_a_2737_ = stack[2].m_obj;
lean_object* v_a_2738_ = stack[3].m_obj;
lean_object* v_res_2745_;
v_res_2745_ = l_Lake_Toml_val_parenthesizer(v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_);
stack->m_obj
 = v_res_2745_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_val_parenthesizer___boxed(lean_object* v_a_2746_, lean_object* v_a_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_){
_start:
{
lean_object* v_res_2751_; 
v_res_2751_ = l_Lake_Toml_val_parenthesizer(v_a_2746_, v_a_2747_, v_a_2748_, v_a_2749_);
lean_dec(v_a_2749_);
lean_dec_ref(v_a_2748_);
lean_dec(v_a_2747_);
lean_dec_ref(v_a_2746_);
return v_res_2751_;
}
}
lean_object* l_Lake_Toml_toml_parenthesizer(lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_){
_start:
{
lean_object* v___x_2757_; lean_object* v___x_2758_; 
v___x_2757_ = lean_alloc_closure((void*)(l_Lake_Toml_val_parenthesizer___boxed), 5, 0);
v___x_2758_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(v___x_2757_, v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_);
return v___x_2758_;
}
}
LEAN_EXPORT void l_Lake_Toml_toml_parenthesizer_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_2752_ = stack[0].m_obj;
lean_object* v_a_2753_ = stack[1].m_obj;
lean_object* v_a_2754_ = stack[2].m_obj;
lean_object* v_a_2755_ = stack[3].m_obj;
lean_object* v_res_2759_;
v_res_2759_ = l_Lake_Toml_toml_parenthesizer(v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_);
stack->m_obj
 = v_res_2759_;
}
LEAN_EXPORT lean_object* l_Lake_Toml_toml_parenthesizer___boxed(lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_, lean_object* v_a_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_Lake_Toml_toml_parenthesizer(v_a_2760_, v_a_2761_, v_a_2762_, v_a_2763_);
lean_dec(v_a_2763_);
lean_dec_ref(v_a_2762_);
lean_dec(v_a_2761_);
lean_dec_ref(v_a_2760_);
return v_res_2765_;
}
}
static lean_object* _init_l_Lake_Toml_toml___closed__0(void){
_start:
{
lean_object* v___x_2766_; lean_object* v___x_2767_; 
v___x_2766_ = l_Lake_Toml_val;
v___x_2767_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore(v___x_2766_);
return v___x_2767_;
}
}
static lean_object* _init_l_Lake_Toml_toml___closed__1(void){
_start:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; 
v___x_2768_ = lean_obj_once(&l_Lake_Toml_toml___closed__0, &l_Lake_Toml_toml___closed__0_once, _init_l_Lake_Toml_toml___closed__0);
v___x_2769_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1));
v___x_2770_ = l_Lean_Parser_withCache(v___x_2769_, v___x_2768_);
return v___x_2770_;
}
}
static lean_object* _init_l_Lake_Toml_toml(void){
_start:
{
lean_object* v___x_2771_; 
v___x_2771_ = lean_obj_once(&l_Lake_Toml_toml___closed__1, &l_Lake_Toml_toml___closed__1_once, _init_l_Lake_Toml_toml___closed__1);
return v___x_2771_;
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
