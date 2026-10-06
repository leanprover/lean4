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
LEAN_EXPORT uint8_t l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(lean_object* v_x_83_, lean_object* v_x_84_){
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
LEAN_EXPORT lean_object* l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0___boxed(lean_object* v_x_91_, lean_object* v_x_92_){
_start:
{
uint8_t v_res_93_; lean_object* v_r_94_; 
v_res_93_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_x_91_, v_x_92_);
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
v___x_105_ = lean_box(0);
v___x_106_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_104_, v___x_105_);
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
v___x_132_ = lean_box(0);
v___x_133_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_131_, v___x_132_);
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
v___x_161_ = lean_box(0);
v___x_162_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_160_, v___x_161_);
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
v___x_167_ = lean_box(0);
v___x_168_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_166_, v___x_167_);
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
v___x_196_ = lean_box(0);
v___x_197_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_195_, v___x_196_);
if (v___x_197_ == 0)
{
return v_s_194_;
}
else
{
lean_object* v_s_198_; lean_object* v_errorMsg_199_; uint8_t v___x_200_; 
v_s_198_ = l_Lake_Toml_newlineFn(v___y_192_, v_s_194_);
v_errorMsg_199_ = lean_ctor_get(v_s_198_, 4);
v___x_200_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_199_, v___x_196_);
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
v___x_209_ = lean_box(0);
v___x_210_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_208_, v___x_209_);
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
v___x_222_ = lean_box(0);
v___x_223_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_221_, v___x_222_);
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
v___x_309_ = lean_box(0);
v___x_310_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_308_, v___x_309_);
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
v___x_326_ = lean_box(0);
v___x_327_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_325_, v___x_326_);
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
v___x_363_ = lean_box(0);
v___x_364_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_362_, v___x_363_);
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
v___x_398_ = lean_box(0);
v___x_399_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_397_, v___x_398_);
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
v___x_436_ = lean_box(0);
v___x_437_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_435_, v___x_436_);
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
v___x_461_ = lean_box(0);
v___x_462_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_460_, v___x_461_);
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
v___x_495_ = lean_box(0);
v___x_496_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_494_, v___x_495_);
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
v___x_502_ = lean_box(0);
v___x_503_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_501_, v___x_502_);
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
v___x_535_ = lean_box(0);
v___x_536_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_534_, v___x_535_);
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
v___x_560_ = lean_box(0);
v___x_561_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_559_, v___x_560_);
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
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(lean_object* v_a_576_, lean_object* v_a_577_){
_start:
{
lean_object* v___x_578_; lean_object* v_s_579_; lean_object* v_errorMsg_580_; lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_578_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__1));
v_s_579_ = l_Lake_Toml_digitPairFn(v___x_578_, v_a_576_, v_a_577_);
v_errorMsg_580_ = lean_ctor_get(v_s_579_, 4);
v___x_581_ = lean_box(0);
v___x_582_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_580_, v___x_581_);
if (v___x_582_ == 0)
{
return v_s_579_;
}
else
{
uint32_t v___x_583_; lean_object* v___x_584_; lean_object* v_s_585_; lean_object* v_errorMsg_586_; uint8_t v___x_587_; 
v___x_583_ = 58;
v___x_584_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v_s_585_ = l_Lake_Toml_chFn(v___x_583_, v___x_584_, v_a_576_, v_s_579_);
v_errorMsg_586_ = lean_ctor_get(v_s_585_, 4);
v___x_587_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_586_, v___x_581_);
if (v___x_587_ == 0)
{
return v_s_585_;
}
else
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5));
v___x_589_ = l_Lake_Toml_digitPairFn(v___x_588_, v_a_576_, v_s_585_);
return v___x_589_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___boxed(lean_object* v_a_590_, lean_object* v_a_591_){
_start:
{
lean_object* v_res_592_; 
v_res_592_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(v_a_590_, v_a_591_);
lean_dec_ref(v_a_590_);
return v_res_592_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn(uint8_t v_allowOffset_594_, uint32_t v_curr_595_, lean_object* v_nextPos_596_, lean_object* v_c_597_, lean_object* v_s_598_){
_start:
{
uint32_t v___x_605_; uint8_t v___x_606_; 
v___x_605_ = 90;
v___x_606_ = lean_uint32_dec_eq(v_curr_595_, v___x_605_);
if (v___x_606_ == 0)
{
uint32_t v___x_607_; uint8_t v___x_608_; 
v___x_607_ = 122;
v___x_608_ = lean_uint32_dec_eq(v_curr_595_, v___x_607_);
if (v___x_608_ == 0)
{
uint8_t v___x_609_; uint32_t v___x_616_; uint8_t v___x_617_; 
v___x_609_ = 1;
v___x_616_ = 43;
v___x_617_ = lean_uint32_dec_eq(v_curr_595_, v___x_616_);
if (v___x_617_ == 0)
{
uint32_t v___x_618_; uint8_t v___x_619_; 
v___x_618_ = 45;
v___x_619_ = lean_uint32_dec_eq(v_curr_595_, v___x_618_);
if (v___x_619_ == 0)
{
lean_dec(v_nextPos_596_);
return v_s_598_;
}
else
{
goto v___jp_610_;
}
}
else
{
goto v___jp_610_;
}
v___jp_610_:
{
if (v_allowOffset_594_ == 0)
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
lean_dec(v_nextPos_596_);
v___x_611_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_612_ = lean_box(0);
v___x_613_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_598_, v___x_611_, v___x_612_, v___x_609_);
return v___x_613_;
}
else
{
lean_object* v___x_614_; lean_object* v___x_615_; 
v___x_614_ = l_Lean_Parser_ParserState_setPos(v_s_598_, v_nextPos_596_);
v___x_615_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(v_c_597_, v___x_614_);
return v___x_615_;
}
}
}
else
{
goto v___jp_599_;
}
}
else
{
goto v___jp_599_;
}
v___jp_599_:
{
if (v_allowOffset_594_ == 0)
{
uint8_t v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
lean_dec(v_nextPos_596_);
v___x_600_ = 1;
v___x_601_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_602_ = lean_box(0);
v___x_603_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_598_, v___x_601_, v___x_602_, v___x_600_);
return v___x_603_;
}
else
{
lean_object* v___x_604_; 
v___x_604_ = l_Lean_Parser_ParserState_setPos(v_s_598_, v_nextPos_596_);
return v___x_604_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___boxed(lean_object* v_allowOffset_620_, lean_object* v_curr_621_, lean_object* v_nextPos_622_, lean_object* v_c_623_, lean_object* v_s_624_){
_start:
{
uint8_t v_allowOffset_boxed_625_; uint32_t v_curr_boxed_626_; lean_object* v_res_627_; 
v_allowOffset_boxed_625_ = lean_unbox(v_allowOffset_620_);
v_curr_boxed_626_ = lean_unbox_uint32(v_curr_621_);
lean_dec(v_curr_621_);
v_res_627_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn(v_allowOffset_boxed_625_, v_curr_boxed_626_, v_nextPos_622_, v_c_623_, v_s_624_);
lean_dec_ref(v_c_623_);
return v_res_627_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0(uint32_t v_x_628_){
_start:
{
uint32_t v___x_629_; uint8_t v___x_630_; 
v___x_629_ = 48;
v___x_630_ = lean_uint32_dec_le(v___x_629_, v_x_628_);
if (v___x_630_ == 0)
{
return v___x_630_;
}
else
{
uint32_t v___x_631_; uint8_t v___x_632_; 
v___x_631_ = 57;
v___x_632_ = lean_uint32_dec_le(v_x_628_, v___x_631_);
return v___x_632_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0___boxed(lean_object* v_x_633_){
_start:
{
uint32_t v_x_270__boxed_634_; uint8_t v_res_635_; lean_object* v_r_636_; 
v_x_270__boxed_634_ = lean_unbox_uint32(v_x_633_);
lean_dec(v_x_633_);
v_res_635_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0(v_x_270__boxed_634_);
v_r_636_ = lean_box(v_res_635_);
return v_r_636_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(uint8_t v_allowOffset_642_, lean_object* v_c_643_, lean_object* v_s_644_){
_start:
{
lean_object* v_toInputContext_645_; lean_object* v_pos_646_; uint8_t v___x_647_; 
v_toInputContext_645_ = lean_ctor_get(v_c_643_, 0);
v_pos_646_ = lean_ctor_get(v_s_644_, 2);
v___x_647_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_645_, v_pos_646_);
if (v___x_647_ == 0)
{
lean_object* v_inputString_648_; uint32_t v_curr_649_; uint32_t v___x_650_; uint8_t v___x_651_; 
v_inputString_648_ = lean_ctor_get(v_toInputContext_645_, 0);
v_curr_649_ = lean_string_utf8_get_fast(v_inputString_648_, v_pos_646_);
v___x_650_ = 46;
v___x_651_ = lean_uint32_dec_eq(v_curr_649_, v___x_650_);
if (v___x_651_ == 0)
{
lean_object* v___x_652_; uint32_t v___x_659_; uint8_t v___x_660_; 
v___x_652_ = lean_string_utf8_next_fast(v_inputString_648_, v_pos_646_);
v___x_659_ = 90;
v___x_660_ = lean_uint32_dec_eq(v_curr_649_, v___x_659_);
if (v___x_660_ == 0)
{
uint32_t v___x_661_; uint8_t v___x_662_; 
v___x_661_ = 122;
v___x_662_ = lean_uint32_dec_eq(v_curr_649_, v___x_661_);
if (v___x_662_ == 0)
{
uint8_t v___x_663_; uint32_t v___x_670_; uint8_t v___x_671_; 
v___x_663_ = 1;
v___x_670_ = 43;
v___x_671_ = lean_uint32_dec_eq(v_curr_649_, v___x_670_);
if (v___x_671_ == 0)
{
uint32_t v___x_672_; uint8_t v___x_673_; 
v___x_672_ = 45;
v___x_673_ = lean_uint32_dec_eq(v_curr_649_, v___x_672_);
if (v___x_673_ == 0)
{
return v_s_644_;
}
else
{
goto v___jp_664_;
}
}
else
{
goto v___jp_664_;
}
v___jp_664_:
{
if (v_allowOffset_642_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; 
v___x_665_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_666_ = lean_box(0);
v___x_667_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_644_, v___x_665_, v___x_666_, v___x_663_);
return v___x_667_;
}
else
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = l_Lean_Parser_ParserState_setPos(v_s_644_, v___x_652_);
v___x_669_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(v_c_643_, v___x_668_);
return v___x_669_;
}
}
}
else
{
goto v___jp_653_;
}
}
else
{
goto v___jp_653_;
}
v___jp_653_:
{
if (v_allowOffset_642_ == 0)
{
uint8_t v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; 
v___x_654_ = 1;
v___x_655_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_656_ = lean_box(0);
v___x_657_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_644_, v___x_655_, v___x_656_, v___x_654_);
return v___x_657_;
}
else
{
lean_object* v___x_658_; 
v___x_658_ = l_Lean_Parser_ParserState_setPos(v_s_644_, v___x_652_);
return v___x_658_;
}
}
}
else
{
lean_object* v___f_674_; lean_object* v_s_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v_s_678_; lean_object* v_pos_679_; lean_object* v_errorMsg_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
lean_inc(v_pos_646_);
v___f_674_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0));
v_s_675_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_644_, v_c_643_, v_pos_646_);
lean_dec(v_pos_646_);
v___x_676_ = lean_box(0);
v___x_677_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__2));
v_s_678_ = l_Lake_Toml_takeWhile1Fn(v___f_674_, v___x_677_, v_c_643_, v_s_675_);
v_pos_679_ = lean_ctor_get(v_s_678_, 2);
v_errorMsg_680_ = lean_ctor_get(v_s_678_, 4);
v___x_681_ = lean_box(0);
v___x_682_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_680_, v___x_681_);
if (v___x_682_ == 0)
{
return v_s_678_;
}
else
{
if (v___x_647_ == 0)
{
uint8_t v___x_683_; 
v___x_683_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_645_, v_pos_679_);
if (v___x_683_ == 0)
{
uint32_t v___x_684_; lean_object* v___x_685_; uint32_t v___x_695_; uint8_t v___x_696_; 
v___x_684_ = lean_string_utf8_get_fast(v_inputString_648_, v_pos_679_);
v___x_685_ = lean_string_utf8_next_fast(v_inputString_648_, v_pos_679_);
v___x_695_ = 90;
v___x_696_ = lean_uint32_dec_eq(v___x_684_, v___x_695_);
if (v___x_696_ == 0)
{
uint32_t v___x_697_; uint8_t v___x_698_; 
v___x_697_ = 122;
v___x_698_ = lean_uint32_dec_eq(v___x_684_, v___x_697_);
if (v___x_698_ == 0)
{
uint32_t v___x_699_; uint8_t v___x_700_; 
v___x_699_ = 43;
v___x_700_ = lean_uint32_dec_eq(v___x_684_, v___x_699_);
if (v___x_700_ == 0)
{
uint32_t v___x_701_; uint8_t v___x_702_; 
v___x_701_ = 45;
v___x_702_ = lean_uint32_dec_eq(v___x_684_, v___x_701_);
if (v___x_702_ == 0)
{
return v_s_678_;
}
else
{
goto v___jp_686_;
}
}
else
{
goto v___jp_686_;
}
}
else
{
goto v___jp_691_;
}
}
else
{
goto v___jp_691_;
}
v___jp_686_:
{
if (v_allowOffset_642_ == 0)
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_688_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_678_, v___x_687_, v___x_676_, v___x_651_);
return v___x_688_;
}
else
{
lean_object* v___x_689_; lean_object* v___x_690_; 
v___x_689_ = l_Lean_Parser_ParserState_setPos(v_s_678_, v___x_685_);
v___x_690_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(v_c_643_, v___x_689_);
return v___x_690_;
}
}
v___jp_691_:
{
if (v_allowOffset_642_ == 0)
{
lean_object* v___x_692_; lean_object* v___x_693_; 
v___x_692_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_693_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_678_, v___x_692_, v___x_676_, v___x_651_);
return v___x_693_;
}
else
{
lean_object* v___x_694_; 
v___x_694_ = l_Lean_Parser_ParserState_setPos(v_s_678_, v___x_685_);
return v___x_694_;
}
}
}
else
{
return v_s_678_;
}
}
else
{
return v_s_678_;
}
}
}
}
else
{
return v_s_644_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___boxed(lean_object* v_allowOffset_703_, lean_object* v_c_704_, lean_object* v_s_705_){
_start:
{
uint8_t v_allowOffset_boxed_706_; lean_object* v_res_707_; 
v_allowOffset_boxed_706_ = lean_unbox(v_allowOffset_703_);
v_res_707_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(v_allowOffset_boxed_706_, v_c_704_, v_s_705_);
lean_dec_ref(v_c_704_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(uint8_t v_allowOffset_712_, lean_object* v_a_713_, lean_object* v_a_714_){
_start:
{
lean_object* v___x_715_; lean_object* v_s_716_; lean_object* v_errorMsg_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_715_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5));
v_s_716_ = l_Lake_Toml_digitPairFn(v___x_715_, v_a_713_, v_a_714_);
v_errorMsg_717_ = lean_ctor_get(v_s_716_, 4);
v___x_718_ = lean_box(0);
v___x_719_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_717_, v___x_718_);
if (v___x_719_ == 0)
{
return v_s_716_;
}
else
{
uint32_t v___x_720_; lean_object* v___x_721_; lean_object* v_s_722_; lean_object* v_errorMsg_723_; uint8_t v___x_724_; 
v___x_720_ = 58;
v___x_721_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v_s_722_ = l_Lake_Toml_chFn(v___x_720_, v___x_721_, v_a_713_, v_s_716_);
v_errorMsg_723_ = lean_ctor_get(v_s_722_, 4);
v___x_724_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_723_, v___x_718_);
if (v___x_724_ == 0)
{
return v_s_722_;
}
else
{
lean_object* v___x_725_; lean_object* v_s_726_; lean_object* v_errorMsg_727_; uint8_t v___x_728_; 
v___x_725_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__1));
v_s_726_ = l_Lake_Toml_digitPairFn(v___x_725_, v_a_713_, v_s_722_);
v_errorMsg_727_ = lean_ctor_get(v_s_726_, 4);
v___x_728_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_727_, v___x_718_);
if (v___x_728_ == 0)
{
return v_s_726_;
}
else
{
lean_object* v___x_729_; 
v___x_729_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(v_allowOffset_712_, v_a_713_, v_s_726_);
return v___x_729_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___boxed(lean_object* v_allowOffset_730_, lean_object* v_a_731_, lean_object* v_a_732_){
_start:
{
uint8_t v_allowOffset_boxed_733_; lean_object* v_res_734_; 
v_allowOffset_boxed_733_ = lean_unbox(v_allowOffset_730_);
v_res_734_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(v_allowOffset_boxed_733_, v_a_731_, v_a_732_);
lean_dec_ref(v_a_731_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_timeFn(uint8_t v_allowOffset_739_, lean_object* v_a_740_, lean_object* v_a_741_){
_start:
{
lean_object* v___x_742_; lean_object* v_s_743_; lean_object* v_errorMsg_744_; lean_object* v___x_745_; uint8_t v___x_746_; 
v___x_742_ = ((lean_object*)(l_Lake_Toml_timeFn___closed__1));
v_s_743_ = l_Lake_Toml_digitPairFn(v___x_742_, v_a_740_, v_a_741_);
v_errorMsg_744_ = lean_ctor_get(v_s_743_, 4);
v___x_745_ = lean_box(0);
v___x_746_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_744_, v___x_745_);
if (v___x_746_ == 0)
{
return v_s_743_;
}
else
{
uint32_t v___x_747_; lean_object* v___x_748_; lean_object* v_s_749_; lean_object* v_errorMsg_750_; uint8_t v___x_751_; 
v___x_747_ = 58;
v___x_748_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v_s_749_ = l_Lake_Toml_chFn(v___x_747_, v___x_748_, v_a_740_, v_s_743_);
v_errorMsg_750_ = lean_ctor_get(v_s_749_, 4);
v___x_751_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_750_, v___x_745_);
if (v___x_751_ == 0)
{
return v_s_749_;
}
else
{
lean_object* v___x_752_; 
v___x_752_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(v_allowOffset_739_, v_a_740_, v_s_749_);
return v___x_752_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_timeFn___boxed(lean_object* v_allowOffset_753_, lean_object* v_a_754_, lean_object* v_a_755_){
_start:
{
uint8_t v_allowOffset_boxed_756_; lean_object* v_res_757_; 
v_allowOffset_boxed_756_ = lean_unbox(v_allowOffset_753_);
v_res_757_ = l_Lake_Toml_timeFn(v_allowOffset_boxed_756_, v_a_754_, v_a_755_);
lean_dec_ref(v_a_754_);
return v_res_757_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(lean_object* v_c_758_, lean_object* v_s_759_){
_start:
{
lean_object* v_pos_760_; lean_object* v_toInputContext_761_; uint8_t v___x_762_; 
v_pos_760_ = lean_ctor_get(v_s_759_, 2);
v_toInputContext_761_ = lean_ctor_get(v_c_758_, 0);
v___x_762_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_761_, v_pos_760_);
if (v___x_762_ == 0)
{
lean_object* v_inputString_763_; uint8_t v___x_764_; uint32_t v_curr_768_; uint32_t v___x_769_; uint8_t v___x_770_; 
v_inputString_763_ = lean_ctor_get(v_toInputContext_761_, 0);
v___x_764_ = 1;
v_curr_768_ = lean_string_utf8_get_fast(v_inputString_763_, v_pos_760_);
v___x_769_ = 84;
v___x_770_ = lean_uint32_dec_eq(v_curr_768_, v___x_769_);
if (v___x_770_ == 0)
{
uint32_t v___x_771_; uint8_t v___x_772_; 
v___x_771_ = 116;
v___x_772_ = lean_uint32_dec_eq(v_curr_768_, v___x_771_);
if (v___x_772_ == 0)
{
uint32_t v___x_773_; uint8_t v___x_774_; 
v___x_773_ = 32;
v___x_774_ = lean_uint32_dec_eq(v_curr_768_, v___x_773_);
if (v___x_774_ == 0)
{
return v_s_759_;
}
else
{
lean_object* v_tPos_775_; lean_object* v___x_776_; lean_object* v_s_777_; lean_object* v_pos_778_; lean_object* v_errorMsg_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
lean_inc(v_pos_760_);
v_tPos_775_ = lean_string_utf8_next_fast(v_inputString_763_, v_pos_760_);
v___x_776_ = l_Lean_Parser_ParserState_setPos(v_s_759_, v_tPos_775_);
v_s_777_ = l_Lake_Toml_timeFn(v___x_764_, v_c_758_, v___x_776_);
v_pos_778_ = lean_ctor_get(v_s_777_, 2);
v_errorMsg_779_ = lean_ctor_get(v_s_777_, 4);
v___x_780_ = lean_box(0);
v___x_781_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_779_, v___x_780_);
if (v___x_781_ == 0)
{
uint8_t v_decide_782_; 
v_decide_782_ = lean_nat_dec_eq(v_pos_778_, v_tPos_775_);
if (v_decide_782_ == 0)
{
lean_dec(v_pos_760_);
return v_s_777_;
}
else
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_783_ = l_Lean_Parser_ParserState_stackSize(v_s_777_);
v___x_784_ = lean_unsigned_to_nat(1u);
v___x_785_ = lean_nat_sub(v___x_783_, v___x_784_);
lean_dec(v___x_783_);
v___x_786_ = l_Lean_Parser_ParserState_restore(v_s_777_, v___x_785_, v_pos_760_);
lean_dec(v___x_785_);
return v___x_786_;
}
}
else
{
lean_dec(v_pos_760_);
return v_s_777_;
}
}
}
else
{
lean_inc(v_pos_760_);
goto v___jp_765_;
}
}
else
{
lean_inc(v_pos_760_);
goto v___jp_765_;
}
v___jp_765_:
{
lean_object* v___x_766_; lean_object* v___x_767_; 
v___x_766_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_759_, v_c_758_, v_pos_760_);
lean_dec(v_pos_760_);
v___x_767_ = l_Lake_Toml_timeFn(v___x_764_, v_c_758_, v___x_766_);
return v___x_767_;
}
}
else
{
return v_s_759_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn___boxed(lean_object* v_c_787_, lean_object* v_s_788_){
_start:
{
lean_object* v_res_789_; 
v_res_789_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(v_c_787_, v_s_788_);
lean_dec_ref(v_c_787_);
return v_res_789_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(lean_object* v_a_802_, lean_object* v_a_803_){
_start:
{
lean_object* v___x_804_; lean_object* v_s_805_; lean_object* v_errorMsg_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v___x_804_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__1));
v_s_805_ = l_Lake_Toml_digitPairFn(v___x_804_, v_a_802_, v_a_803_);
v_errorMsg_806_ = lean_ctor_get(v_s_805_, 4);
v___x_807_ = lean_box(0);
v___x_808_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_806_, v___x_807_);
if (v___x_808_ == 0)
{
return v_s_805_;
}
else
{
uint32_t v___x_809_; lean_object* v___x_810_; lean_object* v_s_811_; lean_object* v_errorMsg_812_; uint8_t v___x_813_; 
v___x_809_ = 45;
v___x_810_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3));
v_s_811_ = l_Lake_Toml_chFn(v___x_809_, v___x_810_, v_a_802_, v_s_805_);
v_errorMsg_812_ = lean_ctor_get(v_s_811_, 4);
v___x_813_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_812_, v___x_807_);
if (v___x_813_ == 0)
{
return v_s_811_;
}
else
{
lean_object* v___x_814_; lean_object* v_s_815_; lean_object* v_errorMsg_816_; uint8_t v___x_817_; 
v___x_814_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5));
v_s_815_ = l_Lake_Toml_digitPairFn(v___x_814_, v_a_802_, v_s_811_);
v_errorMsg_816_ = lean_ctor_get(v_s_815_, 4);
v___x_817_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_816_, v___x_807_);
if (v___x_817_ == 0)
{
return v_s_815_;
}
else
{
lean_object* v___x_818_; 
v___x_818_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(v_a_802_, v_s_815_);
return v___x_818_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___boxed(lean_object* v_a_819_, lean_object* v_a_820_){
_start:
{
lean_object* v_res_821_; 
v_res_821_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(v_a_819_, v_a_820_);
lean_dec_ref(v_a_819_);
return v_res_821_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0(lean_object* v_c_826_, lean_object* v_x_827_, lean_object* v_x_828_){
_start:
{
lean_object* v_zero_829_; uint8_t v_isZero_830_; 
v_zero_829_ = lean_unsigned_to_nat(0u);
v_isZero_830_ = lean_nat_dec_eq(v_x_827_, v_zero_829_);
if (v_isZero_830_ == 1)
{
lean_dec(v_x_827_);
return v_x_828_;
}
else
{
lean_object* v___x_831_; lean_object* v_s_832_; lean_object* v_errorMsg_833_; lean_object* v___x_834_; uint8_t v___x_835_; 
v___x_831_ = ((lean_object*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__1));
v_s_832_ = l_Lake_Toml_digitFn(v___x_831_, v_c_826_, v_x_828_);
v_errorMsg_833_ = lean_ctor_get(v_s_832_, 4);
v___x_834_ = lean_box(0);
v___x_835_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_833_, v___x_834_);
if (v___x_835_ == 0)
{
lean_dec(v_x_827_);
return v_s_832_;
}
else
{
lean_object* v_one_836_; lean_object* v_n_837_; 
v_one_836_ = lean_unsigned_to_nat(1u);
v_n_837_ = lean_nat_sub(v_x_827_, v_one_836_);
lean_dec(v_x_827_);
v_x_827_ = v_n_837_;
v_x_828_ = v_s_832_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___boxed(lean_object* v_c_839_, lean_object* v_x_840_, lean_object* v_x_841_){
_start:
{
lean_object* v_res_842_; 
v_res_842_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0(v_c_839_, v_x_840_, v_x_841_);
lean_dec_ref(v_c_839_);
return v_res_842_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dateTimeFn(lean_object* v_a_843_, lean_object* v_a_844_){
_start:
{
lean_object* v___x_845_; lean_object* v_s_846_; lean_object* v_errorMsg_847_; lean_object* v___x_848_; uint8_t v___x_849_; 
v___x_845_ = lean_unsigned_to_nat(4u);
v_s_846_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0(v_a_843_, v___x_845_, v_a_844_);
v_errorMsg_847_ = lean_ctor_get(v_s_846_, 4);
v___x_848_ = lean_box(0);
v___x_849_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_847_, v___x_848_);
if (v___x_849_ == 0)
{
return v_s_846_;
}
else
{
uint32_t v___x_850_; lean_object* v___x_851_; lean_object* v_s_852_; lean_object* v_errorMsg_853_; uint8_t v___x_854_; 
v___x_850_ = 45;
v___x_851_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3));
v_s_852_ = l_Lake_Toml_chFn(v___x_850_, v___x_851_, v_a_843_, v_s_846_);
v_errorMsg_853_ = lean_ctor_get(v_s_852_, 4);
v___x_854_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_853_, v___x_848_);
if (v___x_854_ == 0)
{
return v_s_852_;
}
else
{
lean_object* v___x_855_; 
v___x_855_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(v_a_843_, v_s_852_);
return v___x_855_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dateTimeFn___boxed(lean_object* v_a_856_, lean_object* v_a_857_){
_start:
{
lean_object* v_res_858_; 
v_res_858_ = l_Lake_Toml_dateTimeFn(v_a_856_, v_a_857_);
lean_dec_ref(v_a_856_);
return v_res_858_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(lean_object* v_c_863_, lean_object* v_s_864_){
_start:
{
lean_object* v_toInputContext_865_; lean_object* v_pos_866_; lean_object* v_expected_867_; uint8_t v___x_868_; 
v_toInputContext_865_ = lean_ctor_get(v_c_863_, 0);
v_pos_866_ = lean_ctor_get(v_s_864_, 2);
v_expected_867_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__1));
v___x_868_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_865_, v_pos_866_);
if (v___x_868_ == 0)
{
lean_object* v_inputString_869_; lean_object* v___f_870_; uint32_t v_curr_875_; uint32_t v___x_876_; uint8_t v___x_877_; 
v_inputString_869_ = lean_ctor_get(v_toInputContext_865_, 0);
v___f_870_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0));
v_curr_875_ = lean_string_utf8_get_fast(v_inputString_869_, v_pos_866_);
v___x_876_ = 45;
v___x_877_ = lean_uint32_dec_eq(v_curr_875_, v___x_876_);
if (v___x_877_ == 0)
{
uint32_t v___x_878_; uint8_t v___x_879_; 
v___x_878_ = 43;
v___x_879_ = lean_uint32_dec_eq(v_curr_875_, v___x_878_);
if (v___x_879_ == 0)
{
uint8_t v___x_880_; uint32_t v___x_881_; uint8_t v___x_882_; 
v___x_880_ = 1;
v___x_881_ = 48;
v___x_882_ = lean_uint32_dec_le(v___x_881_, v_curr_875_);
if (v___x_882_ == 0)
{
lean_object* v___x_883_; 
v___x_883_ = l_Lake_Toml_mkUnexpectedCharError(v_s_864_, v_curr_875_, v_expected_867_, v___x_880_);
return v___x_883_;
}
else
{
uint32_t v___x_884_; uint8_t v___x_885_; 
v___x_884_ = 57;
v___x_885_ = lean_uint32_dec_le(v_curr_875_, v___x_884_);
if (v___x_885_ == 0)
{
lean_object* v___x_886_; 
v___x_886_ = l_Lake_Toml_mkUnexpectedCharError(v_s_864_, v_curr_875_, v_expected_867_, v___x_880_);
return v___x_886_;
}
else
{
lean_object* v_s_887_; uint32_t v___x_888_; lean_object* v___x_889_; 
lean_inc(v_pos_866_);
v_s_887_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_864_, v_c_863_, v_pos_866_);
lean_dec(v_pos_866_);
v___x_888_ = 95;
v___x_889_ = l_Lake_Toml_sepByChar1AuxFn(v___f_870_, v___x_888_, v_expected_867_, v_c_863_, v_s_887_);
return v___x_889_;
}
}
}
else
{
lean_inc(v_pos_866_);
goto v___jp_871_;
}
}
else
{
lean_inc(v_pos_866_);
goto v___jp_871_;
}
v___jp_871_:
{
lean_object* v_s_872_; uint32_t v___x_873_; lean_object* v___x_874_; 
v_s_872_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_864_, v_c_863_, v_pos_866_);
lean_dec(v_pos_866_);
v___x_873_ = 95;
v___x_874_ = l_Lake_Toml_sepByChar1Fn(v___f_870_, v___x_873_, v_expected_867_, v_c_863_, v_s_872_);
return v___x_874_;
}
}
else
{
lean_object* v___x_890_; 
v___x_890_ = l_Lean_Parser_ParserState_mkEOIError(v_s_864_, v_expected_867_);
return v___x_890_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___boxed(lean_object* v_c_891_, lean_object* v_s_892_){
_start:
{
lean_object* v_res_893_; 
v_res_893_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(v_c_891_, v_s_892_);
lean_dec_ref(v_c_891_);
return v_res_893_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(lean_object* v_c_894_, lean_object* v_s_895_){
_start:
{
lean_object* v_toInputContext_896_; lean_object* v_pos_897_; uint8_t v___x_901_; 
v_toInputContext_896_ = lean_ctor_get(v_c_894_, 0);
v_pos_897_ = lean_ctor_get(v_s_895_, 2);
v___x_901_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_896_, v_pos_897_);
if (v___x_901_ == 0)
{
lean_object* v_inputString_902_; uint32_t v_curr_903_; uint32_t v___x_904_; uint8_t v___x_905_; 
v_inputString_902_ = lean_ctor_get(v_toInputContext_896_, 0);
v_curr_903_ = lean_string_utf8_get_fast(v_inputString_902_, v_pos_897_);
v___x_904_ = 101;
v___x_905_ = lean_uint32_dec_eq(v_curr_903_, v___x_904_);
if (v___x_905_ == 0)
{
uint32_t v___x_906_; uint8_t v___x_907_; 
v___x_906_ = 69;
v___x_907_ = lean_uint32_dec_eq(v_curr_903_, v___x_906_);
if (v___x_907_ == 0)
{
return v_s_895_;
}
else
{
lean_inc(v_pos_897_);
goto v___jp_898_;
}
}
else
{
lean_inc(v_pos_897_);
goto v___jp_898_;
}
}
else
{
return v_s_895_;
}
v___jp_898_:
{
lean_object* v___x_899_; lean_object* v___x_900_; 
v___x_899_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_895_, v_c_894_, v_pos_897_);
lean_dec(v_pos_897_);
v___x_900_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(v_c_894_, v___x_899_);
return v___x_900_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn___boxed(lean_object* v_c_908_, lean_object* v_s_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(v_c_908_, v_s_909_);
lean_dec_ref(v_c_908_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(lean_object* v_startPos_928_, uint32_t v_curr_929_, lean_object* v_nextPos_930_, lean_object* v_c_931_, lean_object* v_s_932_){
_start:
{
uint32_t v___x_942_; uint8_t v___x_943_; 
v___x_942_ = 46;
v___x_943_ = lean_uint32_dec_eq(v_curr_929_, v___x_942_);
if (v___x_943_ == 0)
{
uint32_t v___x_944_; uint8_t v___x_945_; 
v___x_944_ = 101;
v___x_945_ = lean_uint32_dec_eq(v_curr_929_, v___x_944_);
if (v___x_945_ == 0)
{
uint32_t v___x_946_; uint8_t v___x_947_; 
v___x_946_ = 69;
v___x_947_ = lean_uint32_dec_eq(v_curr_929_, v___x_946_);
if (v___x_947_ == 0)
{
lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; 
lean_dec(v_nextPos_930_);
v___x_948_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_949_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_950_ = l_Lake_Toml_pushLit(v___x_948_, v_startPos_928_, v___x_949_, v_c_931_, v_s_932_);
return v___x_950_;
}
else
{
goto v___jp_933_;
}
}
else
{
goto v___jp_933_;
}
}
else
{
lean_object* v___f_951_; lean_object* v_s_952_; uint32_t v___x_953_; lean_object* v___x_954_; lean_object* v_s_955_; lean_object* v_errorMsg_956_; lean_object* v___x_957_; uint8_t v___x_958_; 
v___f_951_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0));
v_s_952_ = l_Lean_Parser_ParserState_setPos(v_s_932_, v_nextPos_930_);
v___x_953_ = 95;
v___x_954_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__8));
v_s_955_ = l_Lake_Toml_sepByChar1Fn(v___f_951_, v___x_953_, v___x_954_, v_c_931_, v_s_952_);
v_errorMsg_956_ = lean_ctor_get(v_s_955_, 4);
v___x_957_ = lean_box(0);
v___x_958_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_956_, v___x_957_);
if (v___x_958_ == 0)
{
lean_dec_ref(v_c_931_);
lean_dec(v_startPos_928_);
return v_s_955_;
}
else
{
lean_object* v_s_959_; lean_object* v_errorMsg_960_; uint8_t v___x_961_; 
v_s_959_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(v_c_931_, v_s_955_);
v_errorMsg_960_ = lean_ctor_get(v_s_959_, 4);
v___x_961_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_960_, v___x_957_);
if (v___x_961_ == 0)
{
lean_dec_ref(v_c_931_);
lean_dec(v_startPos_928_);
return v_s_959_;
}
else
{
lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; 
v___x_962_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_963_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_964_ = l_Lake_Toml_pushLit(v___x_962_, v_startPos_928_, v___x_963_, v_c_931_, v_s_959_);
return v___x_964_;
}
}
}
v___jp_933_:
{
lean_object* v_s_934_; lean_object* v_s_935_; lean_object* v_errorMsg_936_; lean_object* v___x_937_; uint8_t v___x_938_; 
v_s_934_ = l_Lean_Parser_ParserState_setPos(v_s_932_, v_nextPos_930_);
v_s_935_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(v_c_931_, v_s_934_);
v_errorMsg_936_ = lean_ctor_get(v_s_935_, 4);
v___x_937_ = lean_box(0);
v___x_938_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_936_, v___x_937_);
if (v___x_938_ == 0)
{
lean_dec_ref(v_c_931_);
lean_dec(v_startPos_928_);
return v_s_935_;
}
else
{
lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; 
v___x_939_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_940_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_941_ = l_Lake_Toml_pushLit(v___x_939_, v_startPos_928_, v___x_940_, v_c_931_, v_s_935_);
return v___x_941_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___boxed(lean_object* v_startPos_965_, lean_object* v_curr_966_, lean_object* v_nextPos_967_, lean_object* v_c_968_, lean_object* v_s_969_){
_start:
{
uint32_t v_curr_boxed_970_; lean_object* v_res_971_; 
v_curr_boxed_970_ = lean_unbox_uint32(v_curr_966_);
lean_dec(v_curr_966_);
v_res_971_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(v_startPos_965_, v_curr_boxed_970_, v_nextPos_967_, v_c_968_, v_s_969_);
return v_res_971_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailFn(lean_object* v_startPos_972_, lean_object* v_c_973_, lean_object* v_s_974_){
_start:
{
lean_object* v_toInputContext_975_; lean_object* v_pos_976_; uint8_t v___x_977_; 
v_toInputContext_975_ = lean_ctor_get(v_c_973_, 0);
v_pos_976_ = lean_ctor_get(v_s_974_, 2);
v___x_977_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_975_, v_pos_976_);
if (v___x_977_ == 0)
{
lean_object* v_inputString_978_; uint32_t v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; 
v_inputString_978_ = lean_ctor_get(v_toInputContext_975_, 0);
v___x_979_ = lean_string_utf8_get_fast(v_inputString_978_, v_pos_976_);
v___x_980_ = lean_string_utf8_next_fast(v_inputString_978_, v_pos_976_);
v___x_981_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(v_startPos_972_, v___x_979_, v___x_980_, v_c_973_, v_s_974_);
return v___x_981_;
}
else
{
lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; 
v___x_982_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_983_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_984_ = l_Lake_Toml_pushLit(v___x_982_, v_startPos_972_, v___x_983_, v_c_973_, v_s_974_);
return v___x_984_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(lean_object* v_startPos_992_, lean_object* v_c_993_, lean_object* v_s_994_){
_start:
{
lean_object* v_toInputContext_995_; lean_object* v_pos_996_; uint8_t v___x_997_; 
v_toInputContext_995_ = lean_ctor_get(v_c_993_, 0);
v_pos_996_ = lean_ctor_get(v_s_994_, 2);
v___x_997_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_995_, v_pos_996_);
if (v___x_997_ == 0)
{
lean_object* v_inputString_998_; uint32_t v_curr_999_; uint32_t v___x_1003_; uint8_t v___x_1004_; 
v_inputString_998_ = lean_ctor_get(v_toInputContext_995_, 0);
v_curr_999_ = lean_string_utf8_get_fast(v_inputString_998_, v_pos_996_);
v___x_1003_ = 48;
v___x_1004_ = lean_uint32_dec_le(v___x_1003_, v_curr_999_);
if (v___x_1004_ == 0)
{
goto v___jp_1000_;
}
else
{
uint32_t v___x_1005_; uint8_t v___x_1006_; 
v___x_1005_ = 57;
v___x_1006_ = lean_uint32_dec_le(v_curr_999_, v___x_1005_);
if (v___x_1006_ == 0)
{
goto v___jp_1000_;
}
else
{
lean_object* v_s_1007_; 
lean_inc(v_pos_996_);
v_s_1007_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_994_, v_c_993_, v_pos_996_);
lean_dec(v_pos_996_);
v_s_994_ = v_s_1007_;
goto _start;
}
}
v___jp_1000_:
{
lean_object* v___x_1001_; lean_object* v___x_1002_; 
v___x_1001_ = lean_string_utf8_next_fast(v_inputString_998_, v_pos_996_);
v___x_1002_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_992_, v_curr_999_, v___x_1001_, v_c_993_, v_s_994_);
return v___x_1002_;
}
}
else
{
lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; 
v___x_1009_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1010_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1011_ = l_Lake_Toml_pushLit(v___x_1009_, v_startPos_992_, v___x_1010_, v_c_993_, v_s_994_);
return v___x_1011_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn(lean_object* v_startPos_1012_, lean_object* v_c_1013_, lean_object* v_s_1014_){
_start:
{
lean_object* v_pos_1015_; lean_object* v_toInputContext_1016_; lean_object* v_expected_1017_; uint8_t v___x_1018_; 
v_pos_1015_ = lean_ctor_get(v_s_1014_, 2);
v_toInputContext_1016_ = lean_ctor_get(v_c_1013_, 0);
v_expected_1017_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2));
v___x_1018_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1016_, v_pos_1015_);
if (v___x_1018_ == 0)
{
lean_object* v_inputString_1019_; uint8_t v___x_1020_; uint32_t v_curr_1021_; uint32_t v___x_1022_; uint8_t v___x_1023_; 
v_inputString_1019_ = lean_ctor_get(v_toInputContext_1016_, 0);
v___x_1020_ = 1;
v_curr_1021_ = lean_string_utf8_get_fast(v_inputString_1019_, v_pos_1015_);
v___x_1022_ = 48;
v___x_1023_ = lean_uint32_dec_le(v___x_1022_, v_curr_1021_);
if (v___x_1023_ == 0)
{
lean_object* v___x_1024_; 
lean_dec_ref(v_c_1013_);
lean_dec(v_startPos_1012_);
v___x_1024_ = l_Lake_Toml_mkUnexpectedCharError(v_s_1014_, v_curr_1021_, v_expected_1017_, v___x_1020_);
return v___x_1024_;
}
else
{
uint32_t v___x_1025_; uint8_t v___x_1026_; 
v___x_1025_ = 57;
v___x_1026_ = lean_uint32_dec_le(v_curr_1021_, v___x_1025_);
if (v___x_1026_ == 0)
{
lean_object* v___x_1027_; 
lean_dec_ref(v_c_1013_);
lean_dec(v_startPos_1012_);
v___x_1027_ = l_Lake_Toml_mkUnexpectedCharError(v_s_1014_, v_curr_1021_, v_expected_1017_, v___x_1020_);
return v___x_1027_;
}
else
{
lean_object* v_s_1028_; lean_object* v___x_1029_; 
lean_inc(v_pos_1015_);
v_s_1028_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1014_, v_c_1013_, v_pos_1015_);
lean_dec(v_pos_1015_);
v___x_1029_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(v_startPos_1012_, v_c_1013_, v_s_1028_);
return v___x_1029_;
}
}
}
else
{
lean_object* v___x_1030_; 
lean_dec_ref(v_c_1013_);
lean_dec(v_startPos_1012_);
v___x_1030_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1014_, v_expected_1017_);
return v___x_1030_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(lean_object* v_startPos_1031_, uint32_t v_curr_1032_, lean_object* v_nextPos_1033_, lean_object* v_c_1034_, lean_object* v_s_1035_){
_start:
{
uint32_t v___x_1036_; uint8_t v___x_1037_; 
v___x_1036_ = 95;
v___x_1037_ = lean_uint32_dec_eq(v_curr_1032_, v___x_1036_);
if (v___x_1037_ == 0)
{
lean_object* v___x_1038_; 
v___x_1038_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(v_startPos_1031_, v_curr_1032_, v_nextPos_1033_, v_c_1034_, v_s_1035_);
return v___x_1038_;
}
else
{
lean_object* v_s_1039_; lean_object* v___x_1040_; 
v_s_1039_ = l_Lean_Parser_ParserState_setPos(v_s_1035_, v_nextPos_1033_);
v___x_1040_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn(v_startPos_1031_, v_c_1034_, v_s_1039_);
return v___x_1040_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn___boxed(lean_object* v_startPos_1041_, lean_object* v_curr_1042_, lean_object* v_nextPos_1043_, lean_object* v_c_1044_, lean_object* v_s_1045_){
_start:
{
uint32_t v_curr_boxed_1046_; lean_object* v_res_1047_; 
v_curr_boxed_1046_ = lean_unbox_uint32(v_curr_1042_);
lean_dec(v_curr_1042_);
v_res_1047_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1041_, v_curr_boxed_1046_, v_nextPos_1043_, v_c_1044_, v_s_1045_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(lean_object* v_startPos_1053_, lean_object* v_a_1054_, lean_object* v_a_1055_){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v_s_1058_; lean_object* v_errorMsg_1059_; lean_object* v___x_1060_; uint8_t v___x_1061_; 
v___x_1056_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__0));
v___x_1057_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__2));
lean_inc_ref(v_a_1054_);
v_s_1058_ = l_Lake_Toml_strFn(v___x_1056_, v___x_1057_, v_a_1054_, v_a_1055_);
v_errorMsg_1059_ = lean_ctor_get(v_s_1058_, 4);
v___x_1060_ = lean_box(0);
v___x_1061_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1059_, v___x_1060_);
if (v___x_1061_ == 0)
{
lean_dec_ref(v_a_1054_);
lean_dec(v_startPos_1053_);
return v_s_1058_;
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; 
v___x_1062_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_1063_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1064_ = l_Lake_Toml_pushLit(v___x_1062_, v_startPos_1053_, v___x_1063_, v_a_1054_, v_s_1058_);
return v___x_1064_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(lean_object* v_startPos_1070_, lean_object* v_a_1071_, lean_object* v_a_1072_){
_start:
{
lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v_s_1075_; lean_object* v_errorMsg_1076_; lean_object* v___x_1077_; uint8_t v___x_1078_; 
v___x_1073_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__0));
v___x_1074_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__2));
lean_inc_ref(v_a_1071_);
v_s_1075_ = l_Lake_Toml_strFn(v___x_1073_, v___x_1074_, v_a_1071_, v_a_1072_);
v_errorMsg_1076_ = lean_ctor_get(v_s_1075_, 4);
v___x_1077_ = lean_box(0);
v___x_1078_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1076_, v___x_1077_);
if (v___x_1078_ == 0)
{
lean_dec_ref(v_a_1071_);
lean_dec(v_startPos_1070_);
return v_s_1075_;
}
else
{
lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; 
v___x_1079_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_1080_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1081_ = l_Lake_Toml_pushLit(v___x_1079_, v_startPos_1070_, v___x_1080_, v_a_1071_, v_s_1075_);
return v___x_1081_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decimalFn(lean_object* v_startPos_1082_, lean_object* v_c_1083_, lean_object* v_s_1084_){
_start:
{
lean_object* v_toInputContext_1085_; lean_object* v_pos_1086_; lean_object* v_expected_1087_; uint8_t v___x_1088_; 
v_toInputContext_1085_ = lean_ctor_get(v_c_1083_, 0);
v_pos_1086_ = lean_ctor_get(v_s_1084_, 2);
v_expected_1087_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2));
v___x_1088_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1085_, v_pos_1086_);
if (v___x_1088_ == 0)
{
lean_object* v_inputString_1089_; uint32_t v_curr_1090_; uint32_t v___x_1091_; uint8_t v___x_1092_; 
v_inputString_1089_ = lean_ctor_get(v_toInputContext_1085_, 0);
v_curr_1090_ = lean_string_utf8_get_fast(v_inputString_1089_, v_pos_1086_);
v___x_1091_ = 48;
v___x_1092_ = lean_uint32_dec_eq(v_curr_1090_, v___x_1091_);
if (v___x_1092_ == 0)
{
uint8_t v___x_1093_; uint8_t v___x_1104_; 
v___x_1093_ = 1;
v___x_1104_ = lean_uint32_dec_le(v___x_1091_, v_curr_1090_);
if (v___x_1104_ == 0)
{
goto v___jp_1094_;
}
else
{
uint32_t v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = 57;
v___x_1106_ = lean_uint32_dec_le(v_curr_1090_, v___x_1105_);
if (v___x_1106_ == 0)
{
goto v___jp_1094_;
}
else
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_inc(v_pos_1086_);
v___x_1107_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1084_, v_c_1083_, v_pos_1086_);
lean_dec(v_pos_1086_);
v___x_1108_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(v_startPos_1082_, v_c_1083_, v___x_1107_);
return v___x_1108_;
}
}
v___jp_1094_:
{
uint32_t v___x_1095_; uint8_t v___x_1096_; 
v___x_1095_ = 105;
v___x_1096_ = lean_uint32_dec_eq(v_curr_1090_, v___x_1095_);
if (v___x_1096_ == 0)
{
uint32_t v___x_1097_; uint8_t v___x_1098_; 
v___x_1097_ = 110;
v___x_1098_ = lean_uint32_dec_eq(v_curr_1090_, v___x_1097_);
if (v___x_1098_ == 0)
{
lean_object* v___x_1099_; 
lean_dec_ref(v_c_1083_);
lean_dec(v_startPos_1082_);
v___x_1099_ = l_Lake_Toml_mkUnexpectedCharError(v_s_1084_, v_curr_1090_, v_expected_1087_, v___x_1093_);
return v___x_1099_;
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; 
lean_inc(v_pos_1086_);
v___x_1100_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1084_, v_c_1083_, v_pos_1086_);
lean_dec(v_pos_1086_);
v___x_1101_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(v_startPos_1082_, v_c_1083_, v___x_1100_);
return v___x_1101_;
}
}
else
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
lean_inc(v_pos_1086_);
v___x_1102_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1084_, v_c_1083_, v_pos_1086_);
lean_dec(v_pos_1086_);
v___x_1103_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(v_startPos_1082_, v_c_1083_, v___x_1102_);
return v___x_1103_;
}
}
}
else
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
lean_inc(v_pos_1086_);
v___x_1109_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1084_, v_c_1083_, v_pos_1086_);
lean_dec(v_pos_1086_);
v___x_1110_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailFn(v_startPos_1082_, v_c_1083_, v___x_1109_);
return v___x_1110_;
}
}
else
{
lean_object* v___x_1111_; 
lean_dec_ref(v_c_1083_);
lean_dec(v_startPos_1082_);
v___x_1111_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1084_, v_expected_1087_);
return v___x_1111_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn(lean_object* v_startPos_1127_, lean_object* v_c_1128_, lean_object* v_s_1129_){
_start:
{
lean_object* v_toInputContext_1130_; lean_object* v_pos_1131_; uint8_t v___x_1132_; 
v_toInputContext_1130_ = lean_ctor_get(v_c_1128_, 0);
v_pos_1131_ = lean_ctor_get(v_s_1129_, 2);
v___x_1132_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1130_, v_pos_1131_);
if (v___x_1132_ == 0)
{
lean_object* v_inputString_1133_; uint32_t v_curr_1134_; lean_object* v_nextPos_1135_; uint32_t v___x_1136_; uint8_t v___x_1137_; 
v_inputString_1133_ = lean_ctor_get(v_toInputContext_1130_, 0);
v_curr_1134_ = lean_string_utf8_get_fast(v_inputString_1133_, v_pos_1131_);
v_nextPos_1135_ = lean_string_utf8_next_fast(v_inputString_1133_, v_pos_1131_);
v___x_1136_ = 48;
v___x_1137_ = lean_uint32_dec_le(v___x_1136_, v_curr_1134_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; 
v___x_1138_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1127_, v_curr_1134_, v_nextPos_1135_, v_c_1128_, v_s_1129_);
return v___x_1138_;
}
else
{
uint32_t v___x_1139_; uint8_t v___x_1140_; 
v___x_1139_ = 57;
v___x_1140_ = lean_uint32_dec_le(v_curr_1134_, v___x_1139_);
if (v___x_1140_ == 0)
{
lean_object* v___x_1141_; 
v___x_1141_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1127_, v_curr_1134_, v_nextPos_1135_, v_c_1128_, v_s_1129_);
return v___x_1141_;
}
else
{
lean_object* v_s_1142_; lean_object* v_pos_1143_; uint8_t v___x_1144_; 
v_s_1142_ = l_Lean_Parser_ParserState_setPos(v_s_1129_, v_nextPos_1135_);
v_pos_1143_ = lean_ctor_get(v_s_1142_, 2);
v___x_1144_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1130_, v_pos_1143_);
if (v___x_1144_ == 0)
{
uint32_t v_curr_1145_; lean_object* v_nextPos_1146_; uint32_t v___x_1147_; uint8_t v___x_1148_; 
v_curr_1145_ = lean_string_utf8_get_fast(v_inputString_1133_, v_pos_1143_);
v_nextPos_1146_ = lean_string_utf8_next_fast(v_inputString_1133_, v_pos_1143_);
v___x_1147_ = 58;
v___x_1148_ = lean_uint32_dec_eq(v_curr_1145_, v___x_1147_);
if (v___x_1148_ == 0)
{
uint8_t v___x_1149_; 
v___x_1149_ = lean_uint32_dec_le(v___x_1136_, v_curr_1145_);
if (v___x_1149_ == 0)
{
lean_object* v___x_1150_; 
v___x_1150_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1127_, v_curr_1145_, v_nextPos_1146_, v_c_1128_, v_s_1142_);
return v___x_1150_;
}
else
{
uint8_t v___x_1151_; 
v___x_1151_ = lean_uint32_dec_le(v_curr_1145_, v___x_1139_);
if (v___x_1151_ == 0)
{
lean_object* v___x_1152_; 
v___x_1152_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1127_, v_curr_1145_, v_nextPos_1146_, v_c_1128_, v_s_1142_);
return v___x_1152_;
}
else
{
lean_object* v_s_1153_; lean_object* v_pos_1154_; uint8_t v___x_1155_; 
v_s_1153_ = l_Lean_Parser_ParserState_setPos(v_s_1142_, v_nextPos_1146_);
v_pos_1154_ = lean_ctor_get(v_s_1153_, 2);
v___x_1155_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1130_, v_pos_1154_);
if (v___x_1155_ == 0)
{
uint32_t v_curr_1156_; lean_object* v_nextPos_1157_; uint8_t v___x_1158_; 
v_curr_1156_ = lean_string_utf8_get_fast(v_inputString_1133_, v_pos_1154_);
v_nextPos_1157_ = lean_string_utf8_next_fast(v_inputString_1133_, v_pos_1154_);
v___x_1158_ = lean_uint32_dec_le(v___x_1136_, v_curr_1156_);
if (v___x_1158_ == 0)
{
lean_object* v___x_1159_; 
v___x_1159_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1127_, v_curr_1156_, v_nextPos_1157_, v_c_1128_, v_s_1153_);
return v___x_1159_;
}
else
{
uint8_t v___x_1160_; 
v___x_1160_ = lean_uint32_dec_le(v_curr_1156_, v___x_1139_);
if (v___x_1160_ == 0)
{
lean_object* v___x_1161_; 
v___x_1161_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1127_, v_curr_1156_, v_nextPos_1157_, v_c_1128_, v_s_1153_);
return v___x_1161_;
}
else
{
lean_object* v_s_1162_; uint8_t v___x_1163_; 
v_s_1162_ = l_Lean_Parser_ParserState_setPos(v_s_1153_, v_nextPos_1157_);
v___x_1163_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1130_, v_nextPos_1157_);
if (v___x_1163_ == 0)
{
lean_object* v_pos_1164_; uint32_t v_curr_1165_; lean_object* v_nextPos_1166_; uint32_t v___x_1167_; uint8_t v___x_1168_; 
v_pos_1164_ = lean_ctor_get(v_s_1162_, 2);
v_curr_1165_ = lean_string_utf8_get_fast(v_inputString_1133_, v_pos_1164_);
v_nextPos_1166_ = lean_string_utf8_next_fast(v_inputString_1133_, v_pos_1164_);
v___x_1167_ = 45;
v___x_1168_ = lean_uint32_dec_eq(v_curr_1165_, v___x_1167_);
if (v___x_1168_ == 0)
{
uint8_t v___x_1169_; 
v___x_1169_ = lean_uint32_dec_le(v___x_1136_, v_curr_1165_);
if (v___x_1169_ == 0)
{
lean_object* v___x_1170_; 
v___x_1170_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1127_, v_curr_1165_, v_nextPos_1166_, v_c_1128_, v_s_1162_);
return v___x_1170_;
}
else
{
uint8_t v___x_1171_; 
v___x_1171_ = lean_uint32_dec_le(v_curr_1165_, v___x_1139_);
if (v___x_1171_ == 0)
{
lean_object* v___x_1172_; 
v___x_1172_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1127_, v_curr_1165_, v_nextPos_1166_, v_c_1128_, v_s_1162_);
return v___x_1172_;
}
else
{
lean_object* v_s_1173_; lean_object* v___x_1174_; 
v_s_1173_ = l_Lean_Parser_ParserState_setPos(v_s_1162_, v_nextPos_1166_);
v___x_1174_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(v_startPos_1127_, v_c_1128_, v_s_1173_);
return v___x_1174_;
}
}
}
else
{
lean_object* v_s_1175_; lean_object* v_s_1176_; lean_object* v_errorMsg_1177_; lean_object* v___x_1178_; uint8_t v___x_1179_; 
v_s_1175_ = l_Lean_Parser_ParserState_setPos(v_s_1162_, v_nextPos_1166_);
v_s_1176_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(v_c_1128_, v_s_1175_);
v_errorMsg_1177_ = lean_ctor_get(v_s_1176_, 4);
v___x_1178_ = lean_box(0);
v___x_1179_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1177_, v___x_1178_);
if (v___x_1179_ == 0)
{
lean_dec_ref(v_c_1128_);
lean_dec(v_startPos_1127_);
return v_s_1176_;
}
else
{
if (v___x_1163_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1180_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_1181_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1182_ = l_Lake_Toml_pushLit(v___x_1180_, v_startPos_1127_, v___x_1181_, v_c_1128_, v_s_1176_);
return v___x_1182_;
}
else
{
lean_dec_ref(v_c_1128_);
lean_dec(v_startPos_1127_);
return v_s_1176_;
}
}
}
}
else
{
lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1183_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1184_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1185_ = l_Lake_Toml_pushLit(v___x_1183_, v_startPos_1127_, v___x_1184_, v_c_1128_, v_s_1162_);
return v___x_1185_;
}
}
}
}
else
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1186_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1187_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1188_ = l_Lake_Toml_pushLit(v___x_1186_, v_startPos_1127_, v___x_1187_, v_c_1128_, v_s_1153_);
return v___x_1188_;
}
}
}
}
else
{
lean_object* v_s_1189_; lean_object* v_s_1190_; lean_object* v_errorMsg_1191_; lean_object* v___x_1192_; uint8_t v___x_1193_; 
v_s_1189_ = l_Lean_Parser_ParserState_setPos(v_s_1142_, v_nextPos_1146_);
v_s_1190_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(v___x_1144_, v_c_1128_, v_s_1189_);
v_errorMsg_1191_ = lean_ctor_get(v_s_1190_, 4);
v___x_1192_ = lean_box(0);
v___x_1193_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1191_, v___x_1192_);
if (v___x_1193_ == 0)
{
lean_dec_ref(v_c_1128_);
lean_dec(v_startPos_1127_);
return v_s_1190_;
}
else
{
if (v___x_1144_ == 0)
{
lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; 
v___x_1194_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_1195_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1196_ = l_Lake_Toml_pushLit(v___x_1194_, v_startPos_1127_, v___x_1195_, v_c_1128_, v_s_1190_);
return v___x_1196_;
}
else
{
lean_dec_ref(v_c_1128_);
lean_dec(v_startPos_1127_);
return v_s_1190_;
}
}
}
}
else
{
lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; 
v___x_1197_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1198_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1199_ = l_Lake_Toml_pushLit(v___x_1197_, v_startPos_1127_, v___x_1198_, v_c_1128_, v_s_1142_);
return v___x_1199_;
}
}
}
}
else
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
lean_dec_ref(v_c_1128_);
lean_dec(v_startPos_1127_);
v___x_1200_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__5));
v___x_1201_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1129_, v___x_1200_);
return v___x_1201_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralFn___lam__0(lean_object* v_c_1239_, lean_object* v_s_1240_){
_start:
{
lean_object* v_pos_1241_; lean_object* v___y_1246_; lean_object* v_toInputContext_1253_; lean_object* v_expected_1254_; uint8_t v___x_1255_; 
v_pos_1241_ = lean_ctor_get(v_s_1240_, 2);
v_toInputContext_1253_ = lean_ctor_get(v_c_1239_, 0);
v_expected_1254_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__1));
v___x_1255_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1253_, v_pos_1241_);
if (v___x_1255_ == 0)
{
lean_object* v_inputString_1256_; uint32_t v_curr_1257_; uint32_t v___x_1258_; uint8_t v___x_1259_; 
v_inputString_1256_ = lean_ctor_get(v_toInputContext_1253_, 0);
v_curr_1257_ = lean_string_utf8_get_fast(v_inputString_1256_, v_pos_1241_);
v___x_1258_ = 48;
v___x_1259_ = lean_uint32_dec_eq(v_curr_1257_, v___x_1258_);
if (v___x_1259_ == 0)
{
uint8_t v___x_1260_; uint8_t v___x_1281_; 
v___x_1260_ = 1;
v___x_1281_ = lean_uint32_dec_le(v___x_1258_, v_curr_1257_);
if (v___x_1281_ == 0)
{
goto v___jp_1261_;
}
else
{
uint32_t v___x_1282_; uint8_t v___x_1283_; 
v___x_1282_ = 57;
v___x_1283_ = lean_uint32_dec_le(v_curr_1257_, v___x_1282_);
if (v___x_1283_ == 0)
{
goto v___jp_1261_;
}
else
{
lean_object* v___x_1284_; lean_object* v___x_1285_; 
lean_inc(v_pos_1241_);
v___x_1284_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1240_, v_c_1239_, v_pos_1241_);
v___x_1285_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn(v_pos_1241_, v_c_1239_, v___x_1284_);
return v___x_1285_;
}
}
v___jp_1261_:
{
uint32_t v___x_1262_; uint8_t v___x_1263_; 
v___x_1262_ = 43;
v___x_1263_ = lean_uint32_dec_eq(v_curr_1257_, v___x_1262_);
if (v___x_1263_ == 0)
{
uint32_t v___x_1264_; uint8_t v___x_1265_; 
v___x_1264_ = 45;
v___x_1265_ = lean_uint32_dec_eq(v_curr_1257_, v___x_1264_);
if (v___x_1265_ == 0)
{
uint32_t v___x_1266_; uint8_t v___x_1267_; 
v___x_1266_ = 105;
v___x_1267_ = lean_uint32_dec_eq(v_curr_1257_, v___x_1266_);
if (v___x_1267_ == 0)
{
uint32_t v___x_1268_; uint8_t v___x_1269_; 
v___x_1268_ = 110;
v___x_1269_ = lean_uint32_dec_eq(v_curr_1257_, v___x_1268_);
if (v___x_1269_ == 0)
{
lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; lean_object* v___x_1275_; lean_object* v___x_1276_; 
lean_dec_ref(v_c_1239_);
v___x_1270_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__2));
v___x_1271_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__3));
v___x_1272_ = lean_string_push(v___x_1271_, v_curr_1257_);
v___x_1273_ = lean_string_append(v___x_1270_, v___x_1272_);
lean_dec_ref(v___x_1272_);
v___x_1274_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__4));
v___x_1275_ = lean_string_append(v___x_1273_, v___x_1274_);
v___x_1276_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1240_, v___x_1275_, v_expected_1254_, v___x_1260_);
return v___x_1276_;
}
else
{
lean_object* v___x_1277_; lean_object* v___x_1278_; 
lean_inc(v_pos_1241_);
v___x_1277_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1240_, v_c_1239_, v_pos_1241_);
v___x_1278_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(v_pos_1241_, v_c_1239_, v___x_1277_);
return v___x_1278_;
}
}
else
{
lean_object* v___x_1279_; lean_object* v___x_1280_; 
lean_inc(v_pos_1241_);
v___x_1279_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1240_, v_c_1239_, v_pos_1241_);
v___x_1280_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(v_pos_1241_, v_c_1239_, v___x_1279_);
return v___x_1280_;
}
}
else
{
lean_inc(v_pos_1241_);
goto v___jp_1242_;
}
}
else
{
lean_inc(v_pos_1241_);
goto v___jp_1242_;
}
}
}
else
{
lean_object* v_s_1286_; lean_object* v_pos_1287_; uint8_t v___x_1288_; 
lean_inc(v_pos_1241_);
v_s_1286_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1240_, v_c_1239_, v_pos_1241_);
v_pos_1287_ = lean_ctor_get(v_s_1286_, 2);
v___x_1288_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1253_, v_pos_1287_);
if (v___x_1288_ == 0)
{
uint32_t v_curr_1289_; uint32_t v___x_1293_; uint8_t v___x_1294_; 
v_curr_1289_ = lean_string_utf8_get_fast(v_inputString_1256_, v_pos_1287_);
v___x_1293_ = 98;
v___x_1294_ = lean_uint32_dec_eq(v_curr_1289_, v___x_1293_);
if (v___x_1294_ == 0)
{
uint32_t v___x_1295_; uint8_t v___x_1296_; 
v___x_1295_ = 111;
v___x_1296_ = lean_uint32_dec_eq(v_curr_1289_, v___x_1295_);
if (v___x_1296_ == 0)
{
uint32_t v___x_1297_; uint8_t v___x_1298_; 
v___x_1297_ = 120;
v___x_1298_ = lean_uint32_dec_eq(v_curr_1289_, v___x_1297_);
if (v___x_1298_ == 0)
{
uint8_t v___x_1299_; 
v___x_1299_ = lean_uint32_dec_le(v___x_1258_, v_curr_1289_);
if (v___x_1299_ == 0)
{
goto v___jp_1290_;
}
else
{
uint32_t v___x_1300_; uint8_t v___x_1301_; 
v___x_1300_ = 57;
v___x_1301_ = lean_uint32_dec_le(v_curr_1289_, v___x_1300_);
if (v___x_1301_ == 0)
{
goto v___jp_1290_;
}
else
{
lean_object* v_s_1302_; uint32_t v___x_1303_; lean_object* v___x_1304_; lean_object* v_s_1305_; lean_object* v_errorMsg_1306_; lean_object* v___x_1307_; uint8_t v___x_1308_; 
lean_inc(v_pos_1287_);
v_s_1302_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1286_, v_c_1239_, v_pos_1287_);
lean_dec(v_pos_1287_);
v___x_1303_ = 58;
v___x_1304_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v_s_1305_ = l_Lake_Toml_chFn(v___x_1303_, v___x_1304_, v_c_1239_, v_s_1302_);
v_errorMsg_1306_ = lean_ctor_get(v_s_1305_, 4);
v___x_1307_ = lean_box(0);
v___x_1308_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1306_, v___x_1307_);
if (v___x_1308_ == 0)
{
v___y_1246_ = v_s_1305_;
goto v___jp_1245_;
}
else
{
lean_object* v___x_1309_; 
v___x_1309_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(v___x_1298_, v_c_1239_, v_s_1305_);
v___y_1246_ = v___x_1309_;
goto v___jp_1245_;
}
}
}
}
else
{
lean_object* v_s_1310_; lean_object* v___x_1311_; uint32_t v___x_1312_; lean_object* v___x_1313_; lean_object* v_s_1314_; lean_object* v_errorMsg_1315_; lean_object* v___x_1316_; uint8_t v___x_1317_; 
lean_inc(v_pos_1287_);
v_s_1310_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1286_, v_c_1239_, v_pos_1287_);
lean_dec(v_pos_1287_);
v___x_1311_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__5));
v___x_1312_ = 95;
v___x_1313_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__7));
v_s_1314_ = l_Lake_Toml_sepByChar1Fn(v___x_1311_, v___x_1312_, v___x_1313_, v_c_1239_, v_s_1310_);
v_errorMsg_1315_ = lean_ctor_get(v_s_1314_, 4);
v___x_1316_ = lean_box(0);
v___x_1317_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1315_, v___x_1316_);
if (v___x_1317_ == 0)
{
lean_dec(v_pos_1241_);
lean_dec_ref(v_c_1239_);
return v_s_1314_;
}
else
{
lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___x_1318_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__9));
v___x_1319_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1320_ = l_Lake_Toml_pushLit(v___x_1318_, v_pos_1241_, v___x_1319_, v_c_1239_, v_s_1314_);
return v___x_1320_;
}
}
}
else
{
lean_object* v_s_1321_; lean_object* v___x_1322_; uint32_t v___x_1323_; lean_object* v___x_1324_; lean_object* v_s_1325_; lean_object* v_errorMsg_1326_; lean_object* v___x_1327_; uint8_t v___x_1328_; 
lean_inc(v_pos_1287_);
v_s_1321_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1286_, v_c_1239_, v_pos_1287_);
lean_dec(v_pos_1287_);
v___x_1322_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__10));
v___x_1323_ = 95;
v___x_1324_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__12));
v_s_1325_ = l_Lake_Toml_sepByChar1Fn(v___x_1322_, v___x_1323_, v___x_1324_, v_c_1239_, v_s_1321_);
v_errorMsg_1326_ = lean_ctor_get(v_s_1325_, 4);
v___x_1327_ = lean_box(0);
v___x_1328_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1326_, v___x_1327_);
if (v___x_1328_ == 0)
{
lean_dec(v_pos_1241_);
lean_dec_ref(v_c_1239_);
return v_s_1325_;
}
else
{
lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
v___x_1329_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__14));
v___x_1330_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1331_ = l_Lake_Toml_pushLit(v___x_1329_, v_pos_1241_, v___x_1330_, v_c_1239_, v_s_1325_);
return v___x_1331_;
}
}
}
else
{
lean_object* v_s_1332_; lean_object* v___x_1333_; uint32_t v___x_1334_; lean_object* v___x_1335_; lean_object* v_s_1336_; lean_object* v_errorMsg_1337_; lean_object* v___x_1338_; uint8_t v___x_1339_; 
lean_inc(v_pos_1287_);
v_s_1332_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1286_, v_c_1239_, v_pos_1287_);
lean_dec(v_pos_1287_);
v___x_1333_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__15));
v___x_1334_ = 95;
v___x_1335_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__17));
v_s_1336_ = l_Lake_Toml_sepByChar1Fn(v___x_1333_, v___x_1334_, v___x_1335_, v_c_1239_, v_s_1332_);
v_errorMsg_1337_ = lean_ctor_get(v_s_1336_, 4);
v___x_1338_ = lean_box(0);
v___x_1339_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1337_, v___x_1338_);
if (v___x_1339_ == 0)
{
lean_dec(v_pos_1241_);
lean_dec_ref(v_c_1239_);
return v_s_1336_;
}
else
{
if (v___x_1288_ == 0)
{
lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v___x_1340_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__19));
v___x_1341_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1342_ = l_Lake_Toml_pushLit(v___x_1340_, v_pos_1241_, v___x_1341_, v_c_1239_, v_s_1336_);
return v___x_1342_;
}
else
{
lean_dec(v_pos_1241_);
lean_dec_ref(v_c_1239_);
return v_s_1336_;
}
}
}
v___jp_1290_:
{
lean_object* v___x_1291_; lean_object* v___x_1292_; 
v___x_1291_ = lean_string_utf8_next_fast(v_inputString_1256_, v_pos_1287_);
v___x_1292_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(v_pos_1241_, v_curr_1289_, v___x_1291_, v_c_1239_, v_s_1286_);
return v___x_1292_;
}
}
else
{
lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1343_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1344_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1345_ = l_Lake_Toml_pushLit(v___x_1343_, v_pos_1241_, v___x_1344_, v_c_1239_, v_s_1286_);
return v___x_1345_;
}
}
}
else
{
lean_object* v___x_1346_; 
lean_dec_ref(v_c_1239_);
v___x_1346_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1240_, v_expected_1254_);
return v___x_1346_;
}
v___jp_1242_:
{
lean_object* v___x_1243_; lean_object* v___x_1244_; 
v___x_1243_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1240_, v_c_1239_, v_pos_1241_);
v___x_1244_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decimalFn(v_pos_1241_, v_c_1239_, v___x_1243_);
return v___x_1244_;
}
v___jp_1245_:
{
lean_object* v_errorMsg_1247_; lean_object* v___x_1248_; uint8_t v___x_1249_; 
v_errorMsg_1247_ = lean_ctor_get(v___y_1246_, 4);
v___x_1248_ = lean_box(0);
v___x_1249_ = l_instBEqOption_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1247_, v___x_1248_);
if (v___x_1249_ == 0)
{
lean_dec(v_pos_1241_);
lean_dec_ref(v_c_1239_);
return v___y_1246_;
}
else
{
lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; 
v___x_1250_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_1251_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1252_ = l_Lake_Toml_pushLit(v___x_1250_, v_pos_1241_, v___x_1251_, v_c_1239_, v___y_1246_);
return v___x_1252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralFn(lean_object* v_a_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v___f_1350_; lean_object* v___x_1351_; 
v___f_1350_ = ((lean_object*)(l_Lake_Toml_numeralFn___closed__0));
v___x_1351_ = l_Lean_Parser_atomicFn(v___f_1350_, v_a_1348_, v_a_1349_);
return v___x_1351_;
}
}
static lean_object* _init_l_Lake_Toml_trailingWs___closed__0(void){
_start:
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
v___x_1352_ = lean_alloc_closure((void*)(l_Lake_Toml_wsFn___boxed), 2, 0);
v___x_1353_ = l_Lake_Toml_trailing(v___x_1352_);
return v___x_1353_;
}
}
static lean_object* _init_l_Lake_Toml_trailingWs(void){
_start:
{
lean_object* v___x_1354_; 
v___x_1354_ = lean_obj_once(&l_Lake_Toml_trailingWs___closed__0, &l_Lake_Toml_trailingWs___closed__0_once, _init_l_Lake_Toml_trailingWs___closed__0);
return v___x_1354_;
}
}
static lean_object* _init_l_Lake_Toml_trailingSep___closed__1(void){
_start:
{
lean_object* v___x_1356_; lean_object* v___x_1357_; 
v___x_1356_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1357_ = l_Lake_Toml_trailing(v___x_1356_);
return v___x_1357_;
}
}
static lean_object* _init_l_Lake_Toml_trailingSep(void){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = lean_obj_once(&l_Lake_Toml_trailingSep___closed__1, &l_Lake_Toml_trailingSep___closed__1_once, _init_l_Lake_Toml_trailingSep___closed__1);
return v___x_1358_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_unquotedKeyFn___lam__0(uint32_t v_c_1359_){
_start:
{
uint32_t v___x_1375_; uint8_t v___x_1376_; 
v___x_1375_ = 65;
v___x_1376_ = lean_uint32_dec_le(v___x_1375_, v_c_1359_);
if (v___x_1376_ == 0)
{
goto v___jp_1370_;
}
else
{
uint32_t v___x_1377_; uint8_t v___x_1378_; 
v___x_1377_ = 90;
v___x_1378_ = lean_uint32_dec_le(v_c_1359_, v___x_1377_);
if (v___x_1378_ == 0)
{
goto v___jp_1370_;
}
else
{
return v___x_1378_;
}
}
v___jp_1360_:
{
uint32_t v___x_1361_; uint8_t v___x_1362_; 
v___x_1361_ = 95;
v___x_1362_ = lean_uint32_dec_eq(v_c_1359_, v___x_1361_);
if (v___x_1362_ == 0)
{
uint32_t v___x_1363_; uint8_t v___x_1364_; 
v___x_1363_ = 45;
v___x_1364_ = lean_uint32_dec_eq(v_c_1359_, v___x_1363_);
return v___x_1364_;
}
else
{
return v___x_1362_;
}
}
v___jp_1365_:
{
uint32_t v___x_1366_; uint8_t v___x_1367_; 
v___x_1366_ = 48;
v___x_1367_ = lean_uint32_dec_le(v___x_1366_, v_c_1359_);
if (v___x_1367_ == 0)
{
goto v___jp_1360_;
}
else
{
uint32_t v___x_1368_; uint8_t v___x_1369_; 
v___x_1368_ = 57;
v___x_1369_ = lean_uint32_dec_le(v_c_1359_, v___x_1368_);
if (v___x_1369_ == 0)
{
goto v___jp_1360_;
}
else
{
return v___x_1369_;
}
}
}
v___jp_1370_:
{
uint32_t v___x_1371_; uint8_t v___x_1372_; 
v___x_1371_ = 97;
v___x_1372_ = lean_uint32_dec_le(v___x_1371_, v_c_1359_);
if (v___x_1372_ == 0)
{
goto v___jp_1365_;
}
else
{
uint32_t v___x_1373_; uint8_t v___x_1374_; 
v___x_1373_ = 122;
v___x_1374_ = lean_uint32_dec_le(v_c_1359_, v___x_1373_);
if (v___x_1374_ == 0)
{
goto v___jp_1365_;
}
else
{
return v___x_1374_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn___lam__0___boxed(lean_object* v_c_1379_){
_start:
{
uint32_t v_c_boxed_1380_; uint8_t v_res_1381_; lean_object* v_r_1382_; 
v_c_boxed_1380_ = lean_unbox_uint32(v_c_1379_);
lean_dec(v_c_1379_);
v_res_1381_ = l_Lake_Toml_unquotedKeyFn___lam__0(v_c_boxed_1380_);
v_r_1382_ = lean_box(v_res_1381_);
return v_r_1382_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn(lean_object* v_a_1388_, lean_object* v_a_1389_){
_start:
{
lean_object* v___f_1390_; lean_object* v___x_1391_; lean_object* v___x_1392_; 
v___f_1390_ = ((lean_object*)(l_Lake_Toml_unquotedKeyFn___closed__0));
v___x_1391_ = ((lean_object*)(l_Lake_Toml_unquotedKeyFn___closed__2));
v___x_1392_ = l_Lake_Toml_takeWhile1Fn(v___f_1390_, v___x_1391_, v_a_1388_, v_a_1389_);
return v___x_1392_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn___boxed(lean_object* v_a_1393_, lean_object* v_a_1394_){
_start:
{
lean_object* v_res_1395_; 
v_res_1395_ = l_Lake_Toml_unquotedKeyFn(v_a_1393_, v_a_1394_);
lean_dec_ref(v_a_1393_);
return v_res_1395_;
}
}
static lean_object* _init_l_Lake_Toml_unquotedKey___closed__2(void){
_start:
{
uint8_t v___x_1401_; lean_object* v___x_1402_; lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; lean_object* v___x_1406_; 
v___x_1401_ = 0;
v___x_1402_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1403_ = lean_alloc_closure((void*)(l_Lake_Toml_unquotedKeyFn___boxed), 2, 0);
v___x_1404_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__1));
v___x_1405_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__0));
v___x_1406_ = l_Lake_Toml_litWithAntiquot(v___x_1405_, v___x_1404_, v___x_1403_, v___x_1402_, v___x_1401_);
return v___x_1406_;
}
}
static lean_object* _init_l_Lake_Toml_unquotedKey(void){
_start:
{
lean_object* v___x_1407_; 
v___x_1407_ = lean_obj_once(&l_Lake_Toml_unquotedKey___closed__2, &l_Lake_Toml_unquotedKey___closed__2_once, _init_l_Lake_Toml_unquotedKey___closed__2);
return v___x_1407_;
}
}
static lean_object* _init_l_Lake_Toml_basicString___closed__2(void){
_start:
{
uint8_t v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1413_ = 0;
v___x_1414_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1415_ = lean_alloc_closure((void*)(l_Lake_Toml_basicStringFn), 2, 0);
v___x_1416_ = ((lean_object*)(l_Lake_Toml_basicString___closed__1));
v___x_1417_ = ((lean_object*)(l_Lake_Toml_basicString___closed__0));
v___x_1418_ = l_Lake_Toml_litWithAntiquot(v___x_1417_, v___x_1416_, v___x_1415_, v___x_1414_, v___x_1413_);
return v___x_1418_;
}
}
static lean_object* _init_l_Lake_Toml_basicString(void){
_start:
{
lean_object* v___x_1419_; 
v___x_1419_ = lean_obj_once(&l_Lake_Toml_basicString___closed__2, &l_Lake_Toml_basicString___closed__2_once, _init_l_Lake_Toml_basicString___closed__2);
return v___x_1419_;
}
}
static lean_object* _init_l_Lake_Toml_literalString___closed__2(void){
_start:
{
uint8_t v___x_1425_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1428_; lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1425_ = 0;
v___x_1426_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1427_ = lean_alloc_closure((void*)(l_Lake_Toml_literalStringFn___boxed), 2, 0);
v___x_1428_ = ((lean_object*)(l_Lake_Toml_literalString___closed__1));
v___x_1429_ = ((lean_object*)(l_Lake_Toml_literalString___closed__0));
v___x_1430_ = l_Lake_Toml_litWithAntiquot(v___x_1429_, v___x_1428_, v___x_1427_, v___x_1426_, v___x_1425_);
return v___x_1430_;
}
}
static lean_object* _init_l_Lake_Toml_literalString(void){
_start:
{
lean_object* v___x_1431_; 
v___x_1431_ = lean_obj_once(&l_Lake_Toml_literalString___closed__2, &l_Lake_Toml_literalString___closed__2_once, _init_l_Lake_Toml_literalString___closed__2);
return v___x_1431_;
}
}
static lean_object* _init_l_Lake_Toml_mlBasicString___closed__2(void){
_start:
{
uint8_t v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; 
v___x_1437_ = 0;
v___x_1438_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1439_ = lean_alloc_closure((void*)(l_Lake_Toml_mlBasicStringFn), 2, 0);
v___x_1440_ = ((lean_object*)(l_Lake_Toml_mlBasicString___closed__1));
v___x_1441_ = ((lean_object*)(l_Lake_Toml_mlBasicString___closed__0));
v___x_1442_ = l_Lake_Toml_litWithAntiquot(v___x_1441_, v___x_1440_, v___x_1439_, v___x_1438_, v___x_1437_);
return v___x_1442_;
}
}
static lean_object* _init_l_Lake_Toml_mlBasicString(void){
_start:
{
lean_object* v___x_1443_; 
v___x_1443_ = lean_obj_once(&l_Lake_Toml_mlBasicString___closed__2, &l_Lake_Toml_mlBasicString___closed__2_once, _init_l_Lake_Toml_mlBasicString___closed__2);
return v___x_1443_;
}
}
static lean_object* _init_l_Lake_Toml_mlLiteralString___closed__2(void){
_start:
{
uint8_t v___x_1449_; lean_object* v___x_1450_; lean_object* v___x_1451_; lean_object* v___x_1452_; lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1449_ = 0;
v___x_1450_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1451_ = lean_alloc_closure((void*)(l_Lake_Toml_mlLiteralStringFn), 2, 0);
v___x_1452_ = ((lean_object*)(l_Lake_Toml_mlLiteralString___closed__1));
v___x_1453_ = ((lean_object*)(l_Lake_Toml_mlLiteralString___closed__0));
v___x_1454_ = l_Lake_Toml_litWithAntiquot(v___x_1453_, v___x_1452_, v___x_1451_, v___x_1450_, v___x_1449_);
return v___x_1454_;
}
}
static lean_object* _init_l_Lake_Toml_mlLiteralString(void){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = lean_obj_once(&l_Lake_Toml_mlLiteralString___closed__2, &l_Lake_Toml_mlLiteralString___closed__2_once, _init_l_Lake_Toml_mlLiteralString___closed__2);
return v___x_1455_;
}
}
static lean_object* _init_l_Lake_Toml_quotedKey___closed__0(void){
_start:
{
lean_object* v___x_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1456_ = l_Lake_Toml_literalString;
v___x_1457_ = l_Lake_Toml_basicString;
v___x_1458_ = l_Lean_Parser_orelse(v___x_1457_, v___x_1456_);
return v___x_1458_;
}
}
static lean_object* _init_l_Lake_Toml_quotedKey(void){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = lean_obj_once(&l_Lake_Toml_quotedKey___closed__0, &l_Lake_Toml_quotedKey___closed__0_once, _init_l_Lake_Toml_quotedKey___closed__0);
return v___x_1459_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey___closed__2(void){
_start:
{
lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; 
v___x_1465_ = l_Lake_Toml_quotedKey;
v___x_1466_ = l_Lake_Toml_unquotedKey;
v___x_1467_ = l_Lean_Parser_orelse(v___x_1466_, v___x_1465_);
return v___x_1467_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey___closed__3(void){
_start:
{
uint8_t v___x_1468_; lean_object* v___x_1469_; lean_object* v___x_1470_; lean_object* v___x_1471_; lean_object* v___x_1472_; 
v___x_1468_ = 1;
v___x_1469_ = lean_obj_once(&l_Lake_Toml_simpleKey___closed__2, &l_Lake_Toml_simpleKey___closed__2_once, _init_l_Lake_Toml_simpleKey___closed__2);
v___x_1470_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__1));
v___x_1471_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__0));
v___x_1472_ = l_Lean_Parser_nodeWithAntiquot(v___x_1471_, v___x_1470_, v___x_1469_, v___x_1468_);
return v___x_1472_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey(void){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = lean_obj_once(&l_Lake_Toml_simpleKey___closed__3, &l_Lake_Toml_simpleKey___closed__3_once, _init_l_Lake_Toml_simpleKey___closed__3);
return v___x_1473_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__6(void){
_start:
{
lean_object* v___x_1487_; lean_object* v___x_1488_; uint32_t v___x_1489_; lean_object* v___x_1490_; 
v___x_1487_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1488_ = ((lean_object*)(l_Lake_Toml_key___closed__5));
v___x_1489_ = 46;
v___x_1490_ = l_Lake_Toml_chAtom(v___x_1489_, v___x_1488_, v___x_1487_);
return v___x_1490_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__7(void){
_start:
{
lean_object* v___x_1491_; lean_object* v___x_1492_; lean_object* v___x_1493_; 
v___x_1491_ = l_Lake_Toml_trailingWs;
v___x_1492_ = lean_obj_once(&l_Lake_Toml_key___closed__6, &l_Lake_Toml_key___closed__6_once, _init_l_Lake_Toml_key___closed__6);
v___x_1493_ = l_Lean_Parser_andthen(v___x_1492_, v___x_1491_);
return v___x_1493_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__8(void){
_start:
{
lean_object* v___x_1494_; lean_object* v___x_1495_; lean_object* v___x_1496_; 
v___x_1494_ = lean_obj_once(&l_Lake_Toml_key___closed__7, &l_Lake_Toml_key___closed__7_once, _init_l_Lake_Toml_key___closed__7);
v___x_1495_ = l_Lake_Toml_trailingWs;
v___x_1496_ = l_Lean_Parser_andthen(v___x_1495_, v___x_1494_);
return v___x_1496_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__9(void){
_start:
{
uint8_t v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; 
v___x_1497_ = 0;
v___x_1498_ = lean_obj_once(&l_Lake_Toml_key___closed__8, &l_Lake_Toml_key___closed__8_once, _init_l_Lake_Toml_key___closed__8);
v___x_1499_ = ((lean_object*)(l_Lake_Toml_key___closed__3));
v___x_1500_ = l_Lake_Toml_simpleKey;
v___x_1501_ = l_Lean_Parser_sepBy1(v___x_1500_, v___x_1499_, v___x_1498_, v___x_1497_);
return v___x_1501_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__10(void){
_start:
{
lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1504_; 
v___x_1502_ = lean_obj_once(&l_Lake_Toml_key___closed__9, &l_Lake_Toml_key___closed__9_once, _init_l_Lake_Toml_key___closed__9);
v___x_1503_ = ((lean_object*)(l_Lake_Toml_key___closed__2));
v___x_1504_ = l_Lean_Parser_setExpected(v___x_1503_, v___x_1502_);
return v___x_1504_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__11(void){
_start:
{
uint8_t v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1505_ = 1;
v___x_1506_ = lean_obj_once(&l_Lake_Toml_key___closed__10, &l_Lake_Toml_key___closed__10_once, _init_l_Lake_Toml_key___closed__10);
v___x_1507_ = ((lean_object*)(l_Lake_Toml_key___closed__1));
v___x_1508_ = ((lean_object*)(l_Lake_Toml_key___closed__0));
v___x_1509_ = l_Lean_Parser_nodeWithAntiquot(v___x_1508_, v___x_1507_, v___x_1506_, v___x_1505_);
return v___x_1509_;
}
}
static lean_object* _init_l_Lake_Toml_key(void){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_obj_once(&l_Lake_Toml_key___closed__11, &l_Lake_Toml_key___closed__11_once, _init_l_Lake_Toml_key___closed__11);
return v___x_1510_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__4(void){
_start:
{
lean_object* v___x_1520_; lean_object* v___x_1521_; uint32_t v___x_1522_; lean_object* v___x_1523_; 
v___x_1520_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1521_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__3));
v___x_1522_ = 91;
v___x_1523_ = l_Lake_Toml_chAtom(v___x_1522_, v___x_1521_, v___x_1520_);
return v___x_1523_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__7(void){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; uint32_t v___x_1530_; lean_object* v___x_1531_; 
v___x_1528_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1529_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__6));
v___x_1530_ = 91;
v___x_1531_ = l_Lake_Toml_chAtom(v___x_1530_, v___x_1529_, v___x_1528_);
return v___x_1531_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__8(void){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; 
v___x_1532_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__5));
v___x_1533_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__7, &l_Lake_Toml_stdTable___closed__7_once, _init_l_Lake_Toml_stdTable___closed__7);
v___x_1534_ = l_Lean_Parser_notFollowedBy(v___x_1533_, v___x_1532_);
return v___x_1534_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__9(void){
_start:
{
lean_object* v___x_1535_; lean_object* v___x_1536_; lean_object* v___x_1537_; 
v___x_1535_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__8, &l_Lake_Toml_stdTable___closed__8_once, _init_l_Lake_Toml_stdTable___closed__8);
v___x_1536_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__4, &l_Lake_Toml_stdTable___closed__4_once, _init_l_Lake_Toml_stdTable___closed__4);
v___x_1537_ = l_Lean_Parser_andthen(v___x_1536_, v___x_1535_);
return v___x_1537_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__10(void){
_start:
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1538_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__9, &l_Lake_Toml_stdTable___closed__9_once, _init_l_Lake_Toml_stdTable___closed__9);
v___x_1539_ = l_Lean_Parser_atomic(v___x_1538_);
return v___x_1539_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__13(void){
_start:
{
lean_object* v___x_1544_; lean_object* v___x_1545_; uint32_t v___x_1546_; lean_object* v___x_1547_; 
v___x_1544_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1545_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__12));
v___x_1546_ = 93;
v___x_1547_ = l_Lake_Toml_chAtom(v___x_1546_, v___x_1545_, v___x_1544_);
return v___x_1547_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__14(void){
_start:
{
lean_object* v___x_1548_; lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1548_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__13, &l_Lake_Toml_stdTable___closed__13_once, _init_l_Lake_Toml_stdTable___closed__13);
v___x_1549_ = l_Lake_Toml_trailingWs;
v___x_1550_ = l_Lean_Parser_andthen(v___x_1549_, v___x_1548_);
return v___x_1550_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__15(void){
_start:
{
lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1553_; 
v___x_1551_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__14, &l_Lake_Toml_stdTable___closed__14_once, _init_l_Lake_Toml_stdTable___closed__14);
v___x_1552_ = l_Lake_Toml_key;
v___x_1553_ = l_Lean_Parser_andthen(v___x_1552_, v___x_1551_);
return v___x_1553_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__16(void){
_start:
{
lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1554_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__15, &l_Lake_Toml_stdTable___closed__15_once, _init_l_Lake_Toml_stdTable___closed__15);
v___x_1555_ = l_Lake_Toml_trailingWs;
v___x_1556_ = l_Lean_Parser_andthen(v___x_1555_, v___x_1554_);
return v___x_1556_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__17(void){
_start:
{
lean_object* v___x_1557_; lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1557_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__16, &l_Lake_Toml_stdTable___closed__16_once, _init_l_Lake_Toml_stdTable___closed__16);
v___x_1558_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__10, &l_Lake_Toml_stdTable___closed__10_once, _init_l_Lake_Toml_stdTable___closed__10);
v___x_1559_ = l_Lean_Parser_andthen(v___x_1558_, v___x_1557_);
return v___x_1559_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__18(void){
_start:
{
uint8_t v___x_1560_; lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; lean_object* v___x_1564_; 
v___x_1560_ = 0;
v___x_1561_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__17, &l_Lake_Toml_stdTable___closed__17_once, _init_l_Lake_Toml_stdTable___closed__17);
v___x_1562_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__1));
v___x_1563_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__0));
v___x_1564_ = l_Lean_Parser_nodeWithAntiquot(v___x_1563_, v___x_1562_, v___x_1561_, v___x_1560_);
return v___x_1564_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable(void){
_start:
{
lean_object* v___x_1565_; 
v___x_1565_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__18, &l_Lake_Toml_stdTable___closed__18_once, _init_l_Lake_Toml_stdTable___closed__18);
return v___x_1565_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__2(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1571_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__7, &l_Lake_Toml_stdTable___closed__7_once, _init_l_Lake_Toml_stdTable___closed__7);
v___x_1572_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__4, &l_Lake_Toml_stdTable___closed__4_once, _init_l_Lake_Toml_stdTable___closed__4);
v___x_1573_ = l_Lean_Parser_andthen(v___x_1572_, v___x_1571_);
return v___x_1573_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__3(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1574_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__2, &l_Lake_Toml_arrayTable___closed__2_once, _init_l_Lake_Toml_arrayTable___closed__2);
v___x_1575_ = l_Lean_Parser_atomic(v___x_1574_);
return v___x_1575_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__4(void){
_start:
{
lean_object* v___x_1576_; lean_object* v___x_1577_; 
v___x_1576_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__13, &l_Lake_Toml_stdTable___closed__13_once, _init_l_Lake_Toml_stdTable___closed__13);
v___x_1577_ = l_Lean_Parser_andthen(v___x_1576_, v___x_1576_);
return v___x_1577_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__5(void){
_start:
{
lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; 
v___x_1578_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__4, &l_Lake_Toml_arrayTable___closed__4_once, _init_l_Lake_Toml_arrayTable___closed__4);
v___x_1579_ = l_Lake_Toml_trailingWs;
v___x_1580_ = l_Lean_Parser_andthen(v___x_1579_, v___x_1578_);
return v___x_1580_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__6(void){
_start:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1583_; 
v___x_1581_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__5, &l_Lake_Toml_arrayTable___closed__5_once, _init_l_Lake_Toml_arrayTable___closed__5);
v___x_1582_ = l_Lake_Toml_key;
v___x_1583_ = l_Lean_Parser_andthen(v___x_1582_, v___x_1581_);
return v___x_1583_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__7(void){
_start:
{
lean_object* v___x_1584_; lean_object* v___x_1585_; lean_object* v___x_1586_; 
v___x_1584_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__6, &l_Lake_Toml_arrayTable___closed__6_once, _init_l_Lake_Toml_arrayTable___closed__6);
v___x_1585_ = l_Lake_Toml_trailingWs;
v___x_1586_ = l_Lean_Parser_andthen(v___x_1585_, v___x_1584_);
return v___x_1586_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__8(void){
_start:
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1587_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__7, &l_Lake_Toml_arrayTable___closed__7_once, _init_l_Lake_Toml_arrayTable___closed__7);
v___x_1588_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__3, &l_Lake_Toml_arrayTable___closed__3_once, _init_l_Lake_Toml_arrayTable___closed__3);
v___x_1589_ = l_Lean_Parser_andthen(v___x_1588_, v___x_1587_);
return v___x_1589_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__9(void){
_start:
{
uint8_t v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1590_ = 0;
v___x_1591_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__8, &l_Lake_Toml_arrayTable___closed__8_once, _init_l_Lake_Toml_arrayTable___closed__8);
v___x_1592_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__1));
v___x_1593_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__0));
v___x_1594_ = l_Lean_Parser_nodeWithAntiquot(v___x_1593_, v___x_1592_, v___x_1591_, v___x_1590_);
return v___x_1594_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable(void){
_start:
{
lean_object* v___x_1595_; 
v___x_1595_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__9, &l_Lake_Toml_arrayTable___closed__9_once, _init_l_Lake_Toml_arrayTable___closed__9);
return v___x_1595_;
}
}
static lean_object* _init_l_Lake_Toml_table___closed__0(void){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; 
v___x_1596_ = l_Lake_Toml_arrayTable;
v___x_1597_ = l_Lake_Toml_stdTable;
v___x_1598_ = l_Lean_Parser_orelse(v___x_1597_, v___x_1596_);
return v___x_1598_;
}
}
static lean_object* _init_l_Lake_Toml_table(void){
_start:
{
lean_object* v___x_1599_; 
v___x_1599_ = lean_obj_once(&l_Lake_Toml_table___closed__0, &l_Lake_Toml_table___closed__0_once, _init_l_Lake_Toml_table___closed__0);
return v___x_1599_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4(void){
_start:
{
lean_object* v___x_1609_; lean_object* v___x_1610_; uint32_t v___x_1611_; lean_object* v___x_1612_; 
v___x_1609_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1610_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3));
v___x_1611_ = 61;
v___x_1612_ = l_Lake_Toml_chAtom(v___x_1611_, v___x_1610_, v___x_1609_);
return v___x_1612_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(lean_object* v_val_1613_){
_start:
{
lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; lean_object* v___x_1621_; lean_object* v___x_1622_; uint8_t v___x_1623_; lean_object* v___x_1624_; 
v___x_1614_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0));
v___x_1615_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1));
v___x_1616_ = l_Lake_Toml_key;
v___x_1617_ = l_Lake_Toml_trailingWs;
v___x_1618_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4);
v___x_1619_ = l_Lean_Parser_andthen(v___x_1617_, v_val_1613_);
v___x_1620_ = l_Lean_Parser_andthen(v___x_1618_, v___x_1619_);
v___x_1621_ = l_Lean_Parser_andthen(v___x_1617_, v___x_1620_);
v___x_1622_ = l_Lean_Parser_andthen(v___x_1616_, v___x_1621_);
v___x_1623_ = 1;
v___x_1624_ = l_Lean_Parser_nodeWithAntiquot(v___x_1614_, v___x_1615_, v___x_1622_, v___x_1623_);
return v___x_1624_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2(void){
_start:
{
uint8_t v___x_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1633_; 
v___x_1630_ = 1;
v___x_1631_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1));
v___x_1632_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0));
v___x_1633_ = l_Lean_Parser_mkAntiquot(v___x_1632_, v___x_1631_, v___x_1630_, v___x_1630_);
return v___x_1633_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(lean_object* v_val_1634_){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; lean_object* v___x_1638_; lean_object* v___x_1639_; 
v___x_1635_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2, &l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2);
v___x_1636_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(v_val_1634_);
v___x_1637_ = l_Lake_Toml_table;
v___x_1638_ = l_Lean_Parser_orelse(v___x_1636_, v___x_1637_);
v___x_1639_ = l_Lean_Parser_withAntiquot(v___x_1635_, v___x_1638_);
return v___x_1639_;
}
}
static lean_object* _init_l_Lake_Toml_header___closed__2(void){
_start:
{
uint8_t v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1645_ = 0;
v___x_1646_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1647_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1648_ = ((lean_object*)(l_Lake_Toml_header___closed__1));
v___x_1649_ = ((lean_object*)(l_Lake_Toml_header___closed__0));
v___x_1650_ = l_Lake_Toml_litWithAntiquot(v___x_1649_, v___x_1648_, v___x_1647_, v___x_1646_, v___x_1645_);
return v___x_1650_;
}
}
static lean_object* _init_l_Lake_Toml_header(void){
_start:
{
lean_object* v___x_1651_; 
v___x_1651_ = lean_obj_once(&l_Lake_Toml_header___closed__2, &l_Lake_Toml_header___closed__2_once, _init_l_Lake_Toml_header___closed__2);
return v___x_1651_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5(void){
_start:
{
lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1661_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__4));
v___x_1662_ = l_Lean_Parser_symbol(v___x_1661_);
return v___x_1662_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7(void){
_start:
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__6));
v___x_1665_ = l_Lean_Parser_checkLinebreakBefore(v___x_1664_);
return v___x_1665_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8(void){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1666_ = l_Lean_Parser_pushNone;
v___x_1667_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7, &l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7);
v___x_1668_ = l_Lean_Parser_andthen(v___x_1667_, v___x_1666_);
return v___x_1668_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore(lean_object* v_val_1669_){
_start:
{
lean_object* v___x_1670_; lean_object* v___x_1671_; lean_object* v___x_1672_; lean_object* v___x_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; uint8_t v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; lean_object* v_p_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1670_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0));
v___x_1671_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1));
v___x_1672_ = l_Lake_Toml_header;
v___x_1673_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(v_val_1669_);
v___x_1674_ = l_Lake_Toml_trailingSep;
v___x_1675_ = l_Lean_Parser_andthen(v___x_1673_, v___x_1674_);
v___x_1676_ = 1;
v___x_1677_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__3));
v___x_1678_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5);
v_p_1679_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1677_, v___x_1675_, v___x_1678_);
v___x_1680_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8, &l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8);
v___x_1681_ = l_Lean_Parser_sepByNoAntiquot(v_p_1679_, v___x_1680_, v___x_1676_);
v___x_1682_ = l_Lean_Parser_andthen(v___x_1672_, v___x_1681_);
v___x_1683_ = l_Lean_Parser_nodeWithAntiquot(v___x_1670_, v___x_1671_, v___x_1682_, v___x_1676_);
return v___x_1683_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; uint32_t v___x_1695_; lean_object* v___x_1696_; 
v___x_1693_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1694_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__3));
v___x_1695_ = 123;
v___x_1696_ = l_Lake_Toml_chAtom(v___x_1695_, v___x_1694_, v___x_1693_);
return v___x_1696_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; uint32_t v___x_1704_; lean_object* v___x_1705_; 
v___x_1702_ = lean_alloc_closure((void*)(l_Lake_Toml_wsFn___boxed), 2, 0);
v___x_1703_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7));
v___x_1704_ = 44;
v___x_1705_ = l_Lake_Toml_chAtom(v___x_1704_, v___x_1703_, v___x_1702_);
return v___x_1705_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11(void){
_start:
{
lean_object* v___x_1710_; lean_object* v___x_1711_; uint32_t v___x_1712_; lean_object* v___x_1713_; 
v___x_1710_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1711_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10));
v___x_1712_ = 125;
v___x_1713_ = l_Lake_Toml_chAtom(v___x_1712_, v___x_1711_, v___x_1710_);
return v___x_1713_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(lean_object* v_val_1714_){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; lean_object* v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; uint8_t v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; lean_object* v___x_1728_; 
v___x_1715_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0));
v___x_1716_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1));
v___x_1717_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4);
v___x_1718_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(v_val_1714_);
v___x_1719_ = l_Lake_Toml_trailingWs;
v___x_1720_ = l_Lean_Parser_andthen(v___x_1718_, v___x_1719_);
v___x_1721_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5));
v___x_1722_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8);
v___x_1723_ = 0;
v___x_1724_ = l_Lean_Parser_sepBy(v___x_1720_, v___x_1721_, v___x_1722_, v___x_1723_);
v___x_1725_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11);
v___x_1726_ = l_Lean_Parser_andthen(v___x_1724_, v___x_1725_);
v___x_1727_ = l_Lean_Parser_andthen(v___x_1717_, v___x_1726_);
v___x_1728_ = l_Lean_Parser_nodeWithAntiquot(v___x_1715_, v___x_1716_, v___x_1727_, v___x_1723_);
return v___x_1728_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3(void){
_start:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; uint32_t v___x_1739_; lean_object* v___x_1740_; 
v___x_1737_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1738_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__2));
v___x_1739_ = 91;
v___x_1740_ = l_Lake_Toml_chAtom(v___x_1739_, v___x_1738_, v___x_1737_);
return v___x_1740_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4(void){
_start:
{
lean_object* v___x_1741_; lean_object* v___x_1742_; uint32_t v___x_1743_; lean_object* v___x_1744_; 
v___x_1741_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1742_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7));
v___x_1743_ = 44;
v___x_1744_ = l_Lake_Toml_chAtom(v___x_1743_, v___x_1742_, v___x_1741_);
return v___x_1744_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(lean_object* v_val_1745_){
_start:
{
lean_object* v___x_1746_; lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; uint8_t v___x_1758_; lean_object* v___x_1759_; 
v___x_1746_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0));
v___x_1747_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1));
v___x_1748_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3, &l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3);
v___x_1749_ = l_Lake_Toml_trailingSep;
v___x_1750_ = l_Lean_Parser_andthen(v_val_1745_, v___x_1749_);
v___x_1751_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5));
v___x_1752_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4, &l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4);
v___x_1753_ = 1;
v___x_1754_ = l_Lean_Parser_sepBy(v___x_1750_, v___x_1751_, v___x_1752_, v___x_1753_);
v___x_1755_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__13, &l_Lake_Toml_stdTable___closed__13_once, _init_l_Lake_Toml_stdTable___closed__13);
v___x_1756_ = l_Lean_Parser_andthen(v___x_1754_, v___x_1755_);
v___x_1757_ = l_Lean_Parser_andthen(v___x_1748_, v___x_1756_);
v___x_1758_ = 0;
v___x_1759_ = l_Lean_Parser_nodeWithAntiquot(v___x_1746_, v___x_1747_, v___x_1757_, v___x_1758_);
return v___x_1759_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__3(void){
_start:
{
lean_object* v___x_1768_; lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1768_ = l_Lake_Toml_literalString;
v___x_1769_ = l_Lake_Toml_mlLiteralString;
v___x_1770_ = l_Lean_Parser_orelse(v___x_1769_, v___x_1768_);
return v___x_1770_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__4(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1771_ = lean_obj_once(&l_Lake_Toml_string___closed__3, &l_Lake_Toml_string___closed__3_once, _init_l_Lake_Toml_string___closed__3);
v___x_1772_ = l_Lake_Toml_basicString;
v___x_1773_ = l_Lean_Parser_orelse(v___x_1772_, v___x_1771_);
return v___x_1773_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__5(void){
_start:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; lean_object* v___x_1776_; 
v___x_1774_ = lean_obj_once(&l_Lake_Toml_string___closed__4, &l_Lake_Toml_string___closed__4_once, _init_l_Lake_Toml_string___closed__4);
v___x_1775_ = l_Lake_Toml_mlBasicString;
v___x_1776_ = l_Lean_Parser_orelse(v___x_1775_, v___x_1774_);
return v___x_1776_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__6(void){
_start:
{
lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; 
v___x_1777_ = lean_obj_once(&l_Lake_Toml_string___closed__5, &l_Lake_Toml_string___closed__5_once, _init_l_Lake_Toml_string___closed__5);
v___x_1778_ = ((lean_object*)(l_Lake_Toml_string___closed__2));
v___x_1779_ = l_Lean_Parser_setExpected(v___x_1778_, v___x_1777_);
return v___x_1779_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__7(void){
_start:
{
uint8_t v___x_1780_; lean_object* v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; 
v___x_1780_ = 0;
v___x_1781_ = lean_obj_once(&l_Lake_Toml_string___closed__6, &l_Lake_Toml_string___closed__6_once, _init_l_Lake_Toml_string___closed__6);
v___x_1782_ = ((lean_object*)(l_Lake_Toml_string___closed__1));
v___x_1783_ = ((lean_object*)(l_Lake_Toml_string___closed__0));
v___x_1784_ = l_Lean_Parser_nodeWithAntiquot(v___x_1783_, v___x_1782_, v___x_1781_, v___x_1780_);
return v___x_1784_;
}
}
static lean_object* _init_l_Lake_Toml_string(void){
_start:
{
lean_object* v___x_1785_; 
v___x_1785_ = lean_obj_once(&l_Lake_Toml_string___closed__7, &l_Lake_Toml_string___closed__7_once, _init_l_Lake_Toml_string___closed__7);
return v___x_1785_;
}
}
static lean_object* _init_l_Lake_Toml_true___closed__5(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1798_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1799_ = ((lean_object*)(l_Lake_Toml_true___closed__4));
v___x_1800_ = ((lean_object*)(l_Lake_Toml_true___closed__1));
v___x_1801_ = l_Lake_Toml_lit(v___x_1800_, v___x_1799_, v___x_1798_);
return v___x_1801_;
}
}
static lean_object* _init_l_Lake_Toml_true(void){
_start:
{
lean_object* v___x_1802_; 
v___x_1802_ = lean_obj_once(&l_Lake_Toml_true___closed__5, &l_Lake_Toml_true___closed__5_once, _init_l_Lake_Toml_true___closed__5);
return v___x_1802_;
}
}
static lean_object* _init_l_Lake_Toml_false___closed__5(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; 
v___x_1815_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1816_ = ((lean_object*)(l_Lake_Toml_false___closed__4));
v___x_1817_ = ((lean_object*)(l_Lake_Toml_false___closed__1));
v___x_1818_ = l_Lake_Toml_lit(v___x_1817_, v___x_1816_, v___x_1815_);
return v___x_1818_;
}
}
static lean_object* _init_l_Lake_Toml_false(void){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = lean_obj_once(&l_Lake_Toml_false___closed__5, &l_Lake_Toml_false___closed__5_once, _init_l_Lake_Toml_false___closed__5);
return v___x_1819_;
}
}
static lean_object* _init_l_Lake_Toml_boolean___closed__2(void){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1825_ = l_Lake_Toml_false;
v___x_1826_ = l_Lake_Toml_true;
v___x_1827_ = l_Lean_Parser_orelse(v___x_1826_, v___x_1825_);
return v___x_1827_;
}
}
static lean_object* _init_l_Lake_Toml_boolean___closed__3(void){
_start:
{
uint8_t v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; 
v___x_1828_ = 0;
v___x_1829_ = lean_obj_once(&l_Lake_Toml_boolean___closed__2, &l_Lake_Toml_boolean___closed__2_once, _init_l_Lake_Toml_boolean___closed__2);
v___x_1830_ = ((lean_object*)(l_Lake_Toml_boolean___closed__1));
v___x_1831_ = ((lean_object*)(l_Lake_Toml_boolean___closed__0));
v___x_1832_ = l_Lean_Parser_nodeWithAntiquot(v___x_1831_, v___x_1830_, v___x_1829_, v___x_1828_);
return v___x_1832_;
}
}
static lean_object* _init_l_Lake_Toml_boolean(void){
_start:
{
lean_object* v___x_1833_; 
v___x_1833_ = lean_obj_once(&l_Lake_Toml_boolean___closed__3, &l_Lake_Toml_boolean___closed__3_once, _init_l_Lake_Toml_boolean___closed__3);
return v___x_1833_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__0(void){
_start:
{
uint8_t v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; lean_object* v___x_1837_; 
v___x_1834_ = 0;
v___x_1835_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_1836_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2));
v___x_1837_ = l_Lean_Parser_mkAntiquot(v___x_1836_, v___x_1835_, v___x_1834_, v___x_1834_);
return v___x_1837_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__1(void){
_start:
{
uint8_t v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; 
v___x_1838_ = 0;
v___x_1839_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1840_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5));
v___x_1841_ = l_Lean_Parser_mkAntiquot(v___x_1840_, v___x_1839_, v___x_1838_, v___x_1838_);
return v___x_1841_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__2(void){
_start:
{
uint8_t v___x_1842_; lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1842_ = 0;
v___x_1843_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__19));
v___x_1844_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__18));
v___x_1845_ = l_Lean_Parser_mkAntiquot(v___x_1844_, v___x_1843_, v___x_1842_, v___x_1842_);
return v___x_1845_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__3(void){
_start:
{
uint8_t v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1846_ = 0;
v___x_1847_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__14));
v___x_1848_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__13));
v___x_1849_ = l_Lean_Parser_mkAntiquot(v___x_1848_, v___x_1847_, v___x_1846_, v___x_1846_);
return v___x_1849_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__4(void){
_start:
{
uint8_t v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; lean_object* v___x_1853_; 
v___x_1850_ = 0;
v___x_1851_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__9));
v___x_1852_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__8));
v___x_1853_ = l_Lean_Parser_mkAntiquot(v___x_1852_, v___x_1851_, v___x_1850_, v___x_1850_);
return v___x_1853_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__5(void){
_start:
{
uint8_t v___x_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; 
v___x_1854_ = 0;
v___x_1855_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_1856_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0));
v___x_1857_ = l_Lean_Parser_mkAntiquot(v___x_1856_, v___x_1855_, v___x_1854_, v___x_1854_);
return v___x_1857_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__8(void){
_start:
{
uint8_t v___x_1863_; lean_object* v___x_1864_; lean_object* v___x_1865_; lean_object* v___x_1866_; 
v___x_1863_ = 1;
v___x_1864_ = ((lean_object*)(l_Lake_Toml_numeralAntiquot___closed__7));
v___x_1865_ = ((lean_object*)(l_Lake_Toml_numeralAntiquot___closed__6));
v___x_1866_ = l_Lean_Parser_mkAntiquot(v___x_1865_, v___x_1864_, v___x_1863_, v___x_1863_);
return v___x_1866_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__9(void){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; 
v___x_1867_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__8, &l_Lake_Toml_numeralAntiquot___closed__8_once, _init_l_Lake_Toml_numeralAntiquot___closed__8);
v___x_1868_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__5, &l_Lake_Toml_numeralAntiquot___closed__5_once, _init_l_Lake_Toml_numeralAntiquot___closed__5);
v___x_1869_ = l_Lean_Parser_orelse(v___x_1868_, v___x_1867_);
return v___x_1869_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__10(void){
_start:
{
lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; 
v___x_1870_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__9, &l_Lake_Toml_numeralAntiquot___closed__9_once, _init_l_Lake_Toml_numeralAntiquot___closed__9);
v___x_1871_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__4, &l_Lake_Toml_numeralAntiquot___closed__4_once, _init_l_Lake_Toml_numeralAntiquot___closed__4);
v___x_1872_ = l_Lean_Parser_orelse(v___x_1871_, v___x_1870_);
return v___x_1872_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__11(void){
_start:
{
lean_object* v___x_1873_; lean_object* v___x_1874_; lean_object* v___x_1875_; 
v___x_1873_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__10, &l_Lake_Toml_numeralAntiquot___closed__10_once, _init_l_Lake_Toml_numeralAntiquot___closed__10);
v___x_1874_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__3, &l_Lake_Toml_numeralAntiquot___closed__3_once, _init_l_Lake_Toml_numeralAntiquot___closed__3);
v___x_1875_ = l_Lean_Parser_orelse(v___x_1874_, v___x_1873_);
return v___x_1875_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__12(void){
_start:
{
lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; 
v___x_1876_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__11, &l_Lake_Toml_numeralAntiquot___closed__11_once, _init_l_Lake_Toml_numeralAntiquot___closed__11);
v___x_1877_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__2, &l_Lake_Toml_numeralAntiquot___closed__2_once, _init_l_Lake_Toml_numeralAntiquot___closed__2);
v___x_1878_ = l_Lean_Parser_orelse(v___x_1877_, v___x_1876_);
return v___x_1878_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__13(void){
_start:
{
lean_object* v___x_1879_; lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1879_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__12, &l_Lake_Toml_numeralAntiquot___closed__12_once, _init_l_Lake_Toml_numeralAntiquot___closed__12);
v___x_1880_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__1, &l_Lake_Toml_numeralAntiquot___closed__1_once, _init_l_Lake_Toml_numeralAntiquot___closed__1);
v___x_1881_ = l_Lean_Parser_orelse(v___x_1880_, v___x_1879_);
return v___x_1881_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__14(void){
_start:
{
lean_object* v___x_1882_; lean_object* v___x_1883_; lean_object* v___x_1884_; 
v___x_1882_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__13, &l_Lake_Toml_numeralAntiquot___closed__13_once, _init_l_Lake_Toml_numeralAntiquot___closed__13);
v___x_1883_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__0, &l_Lake_Toml_numeralAntiquot___closed__0_once, _init_l_Lake_Toml_numeralAntiquot___closed__0);
v___x_1884_ = l_Lean_Parser_orelse(v___x_1883_, v___x_1882_);
return v___x_1884_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot(void){
_start:
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__14, &l_Lake_Toml_numeralAntiquot___closed__14_once, _init_l_Lake_Toml_numeralAntiquot___closed__14);
return v___x_1885_;
}
}
static lean_object* _init_l_Lake_Toml_numeral___closed__0(void){
_start:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
v___x_1886_ = lean_alloc_closure((void*)(l_Lake_Toml_numeralFn), 2, 0);
v___x_1887_ = l_Lake_Toml_dynamicNode(v___x_1886_);
return v___x_1887_;
}
}
static lean_object* _init_l_Lake_Toml_numeral___closed__1(void){
_start:
{
lean_object* v___x_1888_; lean_object* v___x_1889_; lean_object* v___x_1890_; 
v___x_1888_ = lean_obj_once(&l_Lake_Toml_numeral___closed__0, &l_Lake_Toml_numeral___closed__0_once, _init_l_Lake_Toml_numeral___closed__0);
v___x_1889_ = l_Lake_Toml_numeralAntiquot;
v___x_1890_ = l_Lean_Parser_withAntiquot(v___x_1889_, v___x_1888_);
return v___x_1890_;
}
}
static lean_object* _init_l_Lake_Toml_numeral(void){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_obj_once(&l_Lake_Toml_numeral___closed__1, &l_Lake_Toml_numeral___closed__1_once, _init_l_Lake_Toml_numeral___closed__1);
return v___x_1891_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_numeralOfKind___lam__0(lean_object* v_kind_1892_, lean_object* v_x_1893_){
_start:
{
uint8_t v___x_1894_; 
v___x_1894_ = l_Lean_Syntax_isOfKind(v_x_1893_, v_kind_1892_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralOfKind___lam__0___boxed(lean_object* v_kind_1895_, lean_object* v_x_1896_){
_start:
{
uint8_t v_res_1897_; lean_object* v_r_1898_; 
v_res_1897_ = l_Lake_Toml_numeralOfKind___lam__0(v_kind_1895_, v_x_1896_);
lean_dec(v_kind_1895_);
v_r_1898_ = lean_box(v_res_1897_);
return v_r_1898_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralOfKind(lean_object* v_name_1900_, lean_object* v_kind_1901_){
_start:
{
lean_object* v___f_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; 
v___f_1902_ = lean_alloc_closure((void*)(l_Lake_Toml_numeralOfKind___lam__0___boxed), 2, 1);
lean_closure_set(v___f_1902_, 0, v_kind_1901_);
v___x_1903_ = l_Lake_Toml_numeral;
v___x_1904_ = lean_box(0);
v___x_1905_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1905_, 0, v_name_1900_);
lean_ctor_set(v___x_1905_, 1, v___x_1904_);
v___x_1906_ = ((lean_object*)(l_Lake_Toml_numeralOfKind___closed__0));
v___x_1907_ = l_Lean_Parser_checkStackTop(v___f_1902_, v___x_1906_);
v___x_1908_ = l_Lean_Parser_setExpected(v___x_1905_, v___x_1907_);
v___x_1909_ = l_Lean_Parser_andthen(v___x_1903_, v___x_1908_);
return v___x_1909_;
}
}
static lean_object* _init_l_Lake_Toml_float___closed__0(void){
_start:
{
lean_object* v___x_1910_; lean_object* v___x_1911_; lean_object* v___x_1912_; 
v___x_1910_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_1911_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2));
v___x_1912_ = l_Lake_Toml_numeralOfKind(v___x_1911_, v___x_1910_);
return v___x_1912_;
}
}
static lean_object* _init_l_Lake_Toml_float(void){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = lean_obj_once(&l_Lake_Toml_float___closed__0, &l_Lake_Toml_float___closed__0_once, _init_l_Lake_Toml_float___closed__0);
return v___x_1913_;
}
}
static lean_object* _init_l_Lake_Toml_decInt___closed__0(void){
_start:
{
lean_object* v___x_1914_; lean_object* v___x_1915_; lean_object* v___x_1916_; 
v___x_1914_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1915_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0));
v___x_1916_ = l_Lake_Toml_numeralOfKind(v___x_1915_, v___x_1914_);
return v___x_1916_;
}
}
static lean_object* _init_l_Lake_Toml_decInt(void){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_obj_once(&l_Lake_Toml_decInt___closed__0, &l_Lake_Toml_decInt___closed__0_once, _init_l_Lake_Toml_decInt___closed__0);
return v___x_1917_;
}
}
static lean_object* _init_l_Lake_Toml_binNum___closed__1(void){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; 
v___x_1919_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__19));
v___x_1920_ = ((lean_object*)(l_Lake_Toml_binNum___closed__0));
v___x_1921_ = l_Lake_Toml_numeralOfKind(v___x_1920_, v___x_1919_);
return v___x_1921_;
}
}
static lean_object* _init_l_Lake_Toml_binNum(void){
_start:
{
lean_object* v___x_1922_; 
v___x_1922_ = lean_obj_once(&l_Lake_Toml_binNum___closed__1, &l_Lake_Toml_binNum___closed__1_once, _init_l_Lake_Toml_binNum___closed__1);
return v___x_1922_;
}
}
static lean_object* _init_l_Lake_Toml_octNum___closed__1(void){
_start:
{
lean_object* v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1926_; 
v___x_1924_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__14));
v___x_1925_ = ((lean_object*)(l_Lake_Toml_octNum___closed__0));
v___x_1926_ = l_Lake_Toml_numeralOfKind(v___x_1925_, v___x_1924_);
return v___x_1926_;
}
}
static lean_object* _init_l_Lake_Toml_octNum(void){
_start:
{
lean_object* v___x_1927_; 
v___x_1927_ = lean_obj_once(&l_Lake_Toml_octNum___closed__1, &l_Lake_Toml_octNum___closed__1_once, _init_l_Lake_Toml_octNum___closed__1);
return v___x_1927_;
}
}
static lean_object* _init_l_Lake_Toml_hexNum___closed__1(void){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__9));
v___x_1930_ = ((lean_object*)(l_Lake_Toml_hexNum___closed__0));
v___x_1931_ = l_Lake_Toml_numeralOfKind(v___x_1930_, v___x_1929_);
return v___x_1931_;
}
}
static lean_object* _init_l_Lake_Toml_hexNum(void){
_start:
{
lean_object* v___x_1932_; 
v___x_1932_ = lean_obj_once(&l_Lake_Toml_hexNum___closed__1, &l_Lake_Toml_hexNum___closed__1_once, _init_l_Lake_Toml_hexNum___closed__1);
return v___x_1932_;
}
}
static lean_object* _init_l_Lake_Toml_dateTime___closed__0(void){
_start:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1933_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_1934_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2));
v___x_1935_ = l_Lake_Toml_numeralOfKind(v___x_1934_, v___x_1933_);
return v___x_1935_;
}
}
static lean_object* _init_l_Lake_Toml_dateTime(void){
_start:
{
lean_object* v___x_1936_; 
v___x_1936_ = lean_obj_once(&l_Lake_Toml_dateTime___closed__0, &l_Lake_Toml_dateTime___closed__0_once, _init_l_Lake_Toml_dateTime___closed__0);
return v___x_1936_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_valCore(lean_object* v_val_1937_){
_start:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; lean_object* v___x_1940_; lean_object* v___x_1941_; lean_object* v___x_1942_; lean_object* v___x_1943_; lean_object* v___x_1944_; lean_object* v___x_1945_; lean_object* v___x_1946_; 
v___x_1938_ = l_Lake_Toml_string;
v___x_1939_ = l_Lake_Toml_boolean;
v___x_1940_ = l_Lake_Toml_numeral;
lean_inc_ref(v_val_1937_);
v___x_1941_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(v_val_1937_);
v___x_1942_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(v_val_1937_);
v___x_1943_ = l_Lean_Parser_orelse(v___x_1941_, v___x_1942_);
v___x_1944_ = l_Lean_Parser_orelse(v___x_1940_, v___x_1943_);
v___x_1945_ = l_Lean_Parser_orelse(v___x_1939_, v___x_1944_);
v___x_1946_ = l_Lean_Parser_orelse(v___x_1938_, v___x_1945_);
return v___x_1946_;
}
}
static lean_object* _init_l_Lake_Toml_val___closed__3(void){
_start:
{
uint8_t v___x_1953_; lean_object* v___x_1954_; lean_object* v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; 
v___x_1953_ = 1;
v___x_1954_ = ((lean_object*)(l_Lake_Toml_val___closed__2));
v___x_1955_ = ((lean_object*)(l_Lake_Toml_val___closed__1));
v___x_1956_ = ((lean_object*)(l_Lake_Toml_val___closed__0));
v___x_1957_ = l_Lake_Toml_recNodeWithAntiquot(v___x_1956_, v___x_1955_, v___x_1954_, v___x_1953_);
return v___x_1957_;
}
}
static lean_object* _init_l_Lake_Toml_val(void){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = lean_obj_once(&l_Lake_Toml_val___closed__3, &l_Lake_Toml_val___closed__3_once, _init_l_Lake_Toml_val___closed__3);
return v___x_1958_;
}
}
static lean_object* _init_l_Lake_Toml_array___closed__0(void){
_start:
{
lean_object* v___x_1959_; lean_object* v___x_1960_; 
v___x_1959_ = l_Lake_Toml_val;
v___x_1960_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(v___x_1959_);
return v___x_1960_;
}
}
static lean_object* _init_l_Lake_Toml_array(void){
_start:
{
lean_object* v___x_1961_; 
v___x_1961_ = lean_obj_once(&l_Lake_Toml_array___closed__0, &l_Lake_Toml_array___closed__0_once, _init_l_Lake_Toml_array___closed__0);
return v___x_1961_;
}
}
static lean_object* _init_l_Lake_Toml_inlineTable___closed__0(void){
_start:
{
lean_object* v___x_1962_; lean_object* v___x_1963_; 
v___x_1962_ = l_Lake_Toml_val;
v___x_1963_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(v___x_1962_);
return v___x_1963_;
}
}
static lean_object* _init_l_Lake_Toml_inlineTable(void){
_start:
{
lean_object* v___x_1964_; 
v___x_1964_ = lean_obj_once(&l_Lake_Toml_inlineTable___closed__0, &l_Lake_Toml_inlineTable___closed__0_once, _init_l_Lake_Toml_inlineTable___closed__0);
return v___x_1964_;
}
}
static lean_object* _init_l_Lake_Toml_keyval___closed__0(void){
_start:
{
lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1965_ = l_Lake_Toml_val;
v___x_1966_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(v___x_1965_);
return v___x_1966_;
}
}
static lean_object* _init_l_Lake_Toml_keyval(void){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = lean_obj_once(&l_Lake_Toml_keyval___closed__0, &l_Lake_Toml_keyval___closed__0_once, _init_l_Lake_Toml_keyval___closed__0);
return v___x_1967_;
}
}
static lean_object* _init_l_Lake_Toml_expression___closed__0(void){
_start:
{
lean_object* v___x_1968_; lean_object* v___x_1969_; 
v___x_1968_ = l_Lake_Toml_val;
v___x_1969_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(v___x_1968_);
return v___x_1969_;
}
}
static lean_object* _init_l_Lake_Toml_expression(void){
_start:
{
lean_object* v___x_1970_; 
v___x_1970_ = lean_obj_once(&l_Lake_Toml_expression___closed__0, &l_Lake_Toml_expression___closed__0_once, _init_l_Lake_Toml_expression___closed__0);
return v___x_1970_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_header_formatter(lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_, lean_object* v_a_1974_){
_start:
{
lean_object* v___x_1976_; lean_object* v___x_1977_; uint8_t v___x_1978_; lean_object* v___x_1979_; 
v___x_1976_ = ((lean_object*)(l_Lake_Toml_header___closed__0));
v___x_1977_ = ((lean_object*)(l_Lake_Toml_header___closed__1));
v___x_1978_ = 0;
v___x_1979_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v___x_1976_, v___x_1977_, v___x_1978_, v_a_1971_, v_a_1972_, v_a_1973_, v_a_1974_);
return v___x_1979_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_header_formatter___boxed(lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_){
_start:
{
lean_object* v_res_1985_; 
v_res_1985_ = l_Lake_Toml_header_formatter(v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
lean_dec(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
lean_dec_ref(v_a_1980_);
return v_res_1985_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_formatter(lean_object* v_a_1986_, lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; lean_object* v___x_1994_; 
v___x_1991_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__0));
v___x_1992_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__1));
v___x_1993_ = 0;
v___x_1994_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v___x_1991_, v___x_1992_, v___x_1993_, v_a_1986_, v_a_1987_, v_a_1988_, v_a_1989_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_formatter___boxed(lean_object* v_a_1995_, lean_object* v_a_1996_, lean_object* v_a_1997_, lean_object* v_a_1998_, lean_object* v_a_1999_){
_start:
{
lean_object* v_res_2000_; 
v_res_2000_ = l_Lake_Toml_unquotedKey_formatter(v_a_1995_, v_a_1996_, v_a_1997_, v_a_1998_);
lean_dec(v_a_1998_);
lean_dec_ref(v_a_1997_);
lean_dec(v_a_1996_);
lean_dec_ref(v_a_1995_);
return v_res_2000_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_formatter(lean_object* v_a_2001_, lean_object* v_a_2002_, lean_object* v_a_2003_, lean_object* v_a_2004_){
_start:
{
lean_object* v___x_2006_; lean_object* v___x_2007_; uint8_t v___x_2008_; lean_object* v___x_2009_; 
v___x_2006_ = ((lean_object*)(l_Lake_Toml_basicString___closed__0));
v___x_2007_ = ((lean_object*)(l_Lake_Toml_basicString___closed__1));
v___x_2008_ = 0;
v___x_2009_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v___x_2006_, v___x_2007_, v___x_2008_, v_a_2001_, v_a_2002_, v_a_2003_, v_a_2004_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_formatter___boxed(lean_object* v_a_2010_, lean_object* v_a_2011_, lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_Lake_Toml_basicString_formatter(v_a_2010_, v_a_2011_, v_a_2012_, v_a_2013_);
lean_dec(v_a_2013_);
lean_dec_ref(v_a_2012_);
lean_dec(v_a_2011_);
lean_dec_ref(v_a_2010_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_formatter(lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_){
_start:
{
lean_object* v___x_2021_; lean_object* v___x_2022_; uint8_t v___x_2023_; lean_object* v___x_2024_; 
v___x_2021_ = ((lean_object*)(l_Lake_Toml_literalString___closed__0));
v___x_2022_ = ((lean_object*)(l_Lake_Toml_literalString___closed__1));
v___x_2023_ = 0;
v___x_2024_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v___x_2021_, v___x_2022_, v___x_2023_, v_a_2016_, v_a_2017_, v_a_2018_, v_a_2019_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_formatter___boxed(lean_object* v_a_2025_, lean_object* v_a_2026_, lean_object* v_a_2027_, lean_object* v_a_2028_, lean_object* v_a_2029_){
_start:
{
lean_object* v_res_2030_; 
v_res_2030_ = l_Lake_Toml_literalString_formatter(v_a_2025_, v_a_2026_, v_a_2027_, v_a_2028_);
lean_dec(v_a_2028_);
lean_dec_ref(v_a_2027_);
lean_dec(v_a_2026_);
lean_dec_ref(v_a_2025_);
return v_res_2030_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_formatter(lean_object* v_a_2031_, lean_object* v_a_2032_, lean_object* v_a_2033_, lean_object* v_a_2034_){
_start:
{
lean_object* v___x_2036_; lean_object* v___x_2037_; lean_object* v___x_2038_; 
v___x_2036_ = lean_alloc_closure((void*)(l_Lake_Toml_basicString_formatter___boxed), 5, 0);
v___x_2037_ = lean_alloc_closure((void*)(l_Lake_Toml_literalString_formatter___boxed), 5, 0);
v___x_2038_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2036_, v___x_2037_, v_a_2031_, v_a_2032_, v_a_2033_, v_a_2034_);
return v___x_2038_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_formatter___boxed(lean_object* v_a_2039_, lean_object* v_a_2040_, lean_object* v_a_2041_, lean_object* v_a_2042_, lean_object* v_a_2043_){
_start:
{
lean_object* v_res_2044_; 
v_res_2044_ = l_Lake_Toml_quotedKey_formatter(v_a_2039_, v_a_2040_, v_a_2041_, v_a_2042_);
lean_dec(v_a_2042_);
lean_dec_ref(v_a_2041_);
lean_dec(v_a_2040_);
lean_dec_ref(v_a_2039_);
return v_res_2044_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey_formatter___closed__0(void){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2045_ = lean_alloc_closure((void*)(l_Lake_Toml_quotedKey_formatter___boxed), 5, 0);
v___x_2046_ = lean_alloc_closure((void*)(l_Lake_Toml_unquotedKey_formatter___boxed), 5, 0);
v___x_2047_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2047_, 0, v___x_2046_);
lean_closure_set(v___x_2047_, 1, v___x_2045_);
return v___x_2047_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_formatter(lean_object* v_a_2048_, lean_object* v_a_2049_, lean_object* v_a_2050_, lean_object* v_a_2051_){
_start:
{
lean_object* v___x_2053_; lean_object* v___x_2054_; lean_object* v___x_2055_; uint8_t v___x_2056_; lean_object* v___x_2057_; 
v___x_2053_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__0));
v___x_2054_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__1));
v___x_2055_ = lean_obj_once(&l_Lake_Toml_simpleKey_formatter___closed__0, &l_Lake_Toml_simpleKey_formatter___closed__0_once, _init_l_Lake_Toml_simpleKey_formatter___closed__0);
v___x_2056_ = 1;
v___x_2057_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2053_, v___x_2054_, v___x_2055_, v___x_2056_, v_a_2048_, v_a_2049_, v_a_2050_, v_a_2051_);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_formatter___boxed(lean_object* v_a_2058_, lean_object* v_a_2059_, lean_object* v_a_2060_, lean_object* v_a_2061_, lean_object* v_a_2062_){
_start:
{
lean_object* v_res_2063_; 
v_res_2063_ = l_Lake_Toml_simpleKey_formatter(v_a_2058_, v_a_2059_, v_a_2060_, v_a_2061_);
lean_dec(v_a_2061_);
lean_dec_ref(v_a_2060_);
lean_dec(v_a_2059_);
lean_dec_ref(v_a_2058_);
return v_res_2063_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter___redArg(){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_2065_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter___redArg___boxed(lean_object* v_a_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Lake_Toml_trailingWs_formatter___redArg();
return v_res_2067_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter(lean_object* v_a_2068_, lean_object* v_a_2069_, lean_object* v_a_2070_, lean_object* v_a_2071_){
_start:
{
lean_object* v___x_2073_; 
v___x_2073_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_2073_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter___boxed(lean_object* v_a_2074_, lean_object* v_a_2075_, lean_object* v_a_2076_, lean_object* v_a_2077_, lean_object* v_a_2078_){
_start:
{
lean_object* v_res_2079_; 
v_res_2079_ = l_Lake_Toml_trailingWs_formatter(v_a_2074_, v_a_2075_, v_a_2076_, v_a_2077_);
lean_dec(v_a_2077_);
lean_dec_ref(v_a_2076_);
lean_dec(v_a_2075_);
lean_dec_ref(v_a_2074_);
return v_res_2079_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = 46;
v___x_2081_ = lean_box_uint32(v___x_2080_);
return v___x_2081_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__0(void){
_start:
{
lean_object* v___x_2082_; lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2082_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2083_ = ((lean_object*)(l_Lake_Toml_key___closed__5));
v___x_2084_ = l_Lake_Toml_key_formatter___closed__0___boxed__const__1;
v___x_2085_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2085_, 0, v___x_2084_);
lean_closure_set(v___x_2085_, 1, v___x_2083_);
lean_closure_set(v___x_2085_, 2, v___x_2082_);
return v___x_2085_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__1(void){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; lean_object* v___x_2088_; 
v___x_2086_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2087_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__0, &l_Lake_Toml_key_formatter___closed__0_once, _init_l_Lake_Toml_key_formatter___closed__0);
v___x_2088_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2088_, 0, v___x_2087_);
lean_closure_set(v___x_2088_, 1, v___x_2086_);
return v___x_2088_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__2(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; lean_object* v___x_2091_; 
v___x_2089_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__1, &l_Lake_Toml_key_formatter___closed__1_once, _init_l_Lake_Toml_key_formatter___closed__1);
v___x_2090_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2091_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2091_, 0, v___x_2090_);
lean_closure_set(v___x_2091_, 1, v___x_2089_);
return v___x_2091_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__3(void){
_start:
{
uint8_t v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; 
v___x_2092_ = 0;
v___x_2093_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__2, &l_Lake_Toml_key_formatter___closed__2_once, _init_l_Lake_Toml_key_formatter___closed__2);
v___x_2094_ = ((lean_object*)(l_Lake_Toml_key___closed__3));
v___x_2095_ = lean_alloc_closure((void*)(l_Lake_Toml_simpleKey_formatter___boxed), 5, 0);
v___x_2096_ = lean_box(v___x_2092_);
v___x_2097_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_formatter___boxed), 9, 4);
lean_closure_set(v___x_2097_, 0, v___x_2095_);
lean_closure_set(v___x_2097_, 1, v___x_2094_);
lean_closure_set(v___x_2097_, 2, v___x_2093_);
lean_closure_set(v___x_2097_, 3, v___x_2096_);
return v___x_2097_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__4(void){
_start:
{
lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2100_; 
v___x_2098_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__3, &l_Lake_Toml_key_formatter___closed__3_once, _init_l_Lake_Toml_key_formatter___closed__3);
v___x_2099_ = ((lean_object*)(l_Lake_Toml_key___closed__2));
v___x_2100_ = lean_alloc_closure((void*)(l_Lean_Parser_setExpected_formatter___boxed), 7, 2);
lean_closure_set(v___x_2100_, 0, v___x_2099_);
lean_closure_set(v___x_2100_, 1, v___x_2098_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_key_formatter(lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_){
_start:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; uint8_t v___x_2109_; lean_object* v___x_2110_; 
v___x_2106_ = ((lean_object*)(l_Lake_Toml_key___closed__0));
v___x_2107_ = ((lean_object*)(l_Lake_Toml_key___closed__1));
v___x_2108_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__4, &l_Lake_Toml_key_formatter___closed__4_once, _init_l_Lake_Toml_key_formatter___closed__4);
v___x_2109_ = 1;
v___x_2110_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2106_, v___x_2107_, v___x_2108_, v___x_2109_, v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_);
return v___x_2110_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_key_formatter___boxed(lean_object* v_a_2111_, lean_object* v_a_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l_Lake_Toml_key_formatter(v_a_2111_, v_a_2112_, v_a_2113_, v_a_2114_);
lean_dec(v_a_2114_);
lean_dec_ref(v_a_2113_);
lean_dec(v_a_2112_);
lean_dec_ref(v_a_2111_);
return v_res_2116_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = 61;
v___x_2118_ = lean_box_uint32(v___x_2117_);
return v___x_2118_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0(void){
_start:
{
lean_object* v___x_2119_; lean_object* v___x_2120_; lean_object* v___x_2121_; lean_object* v___x_2122_; 
v___x_2119_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2120_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3));
v___x_2121_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1;
v___x_2122_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2122_, 0, v___x_2121_);
lean_closure_set(v___x_2122_, 1, v___x_2120_);
lean_closure_set(v___x_2122_, 2, v___x_2119_);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter(lean_object* v_val_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_, lean_object* v_a_2127_){
_start:
{
lean_object* v___x_2129_; lean_object* v___x_2130_; lean_object* v___x_2131_; lean_object* v___x_2132_; lean_object* v___x_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; lean_object* v___x_2136_; lean_object* v___x_2137_; uint8_t v___x_2138_; lean_object* v___x_2139_; 
v___x_2129_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0));
v___x_2130_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1));
v___x_2131_ = lean_alloc_closure((void*)(l_Lake_Toml_key_formatter___boxed), 5, 0);
v___x_2132_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2133_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0);
lean_inc_ref(v___x_2132_);
v___x_2134_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2134_, 0, v___x_2132_);
lean_closure_set(v___x_2134_, 1, v_val_2123_);
v___x_2135_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2135_, 0, v___x_2133_);
lean_closure_set(v___x_2135_, 1, v___x_2134_);
v___x_2136_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2136_, 0, v___x_2132_);
lean_closure_set(v___x_2136_, 1, v___x_2135_);
v___x_2137_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2137_, 0, v___x_2131_);
lean_closure_set(v___x_2137_, 1, v___x_2136_);
v___x_2138_ = 1;
v___x_2139_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2129_, v___x_2130_, v___x_2137_, v___x_2138_, v_a_2124_, v_a_2125_, v_a_2126_, v_a_2127_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___boxed(lean_object* v_val_2140_, lean_object* v_a_2141_, lean_object* v_a_2142_, lean_object* v_a_2143_, lean_object* v_a_2144_, lean_object* v_a_2145_){
_start:
{
lean_object* v_res_2146_; 
v_res_2146_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter(v_val_2140_, v_a_2141_, v_a_2142_, v_a_2143_, v_a_2144_);
lean_dec(v_a_2144_);
lean_dec_ref(v_a_2143_);
lean_dec(v_a_2142_);
lean_dec_ref(v_a_2141_);
return v_res_2146_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_2147_; lean_object* v___x_2148_; 
v___x_2147_ = 91;
v___x_2148_ = lean_box_uint32(v___x_2147_);
return v___x_2148_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__0(void){
_start:
{
lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; 
v___x_2149_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2150_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__3));
v___x_2151_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
v___x_2152_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2152_, 0, v___x_2151_);
lean_closure_set(v___x_2152_, 1, v___x_2150_);
lean_closure_set(v___x_2152_, 2, v___x_2149_);
return v___x_2152_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__1(void){
_start:
{
lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; lean_object* v___x_2156_; 
v___x_2153_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2154_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__6));
v___x_2155_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
v___x_2156_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2156_, 0, v___x_2155_);
lean_closure_set(v___x_2156_, 1, v___x_2154_);
lean_closure_set(v___x_2156_, 2, v___x_2153_);
return v___x_2156_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__2(void){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
v___x_2157_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__1, &l_Lake_Toml_stdTable_formatter___closed__1_once, _init_l_Lake_Toml_stdTable_formatter___closed__1);
v___x_2158_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed), 6, 1);
lean_closure_set(v___x_2158_, 0, v___x_2157_);
return v___x_2158_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__3(void){
_start:
{
lean_object* v___x_2159_; lean_object* v___x_2160_; lean_object* v___x_2161_; 
v___x_2159_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__2, &l_Lake_Toml_stdTable_formatter___closed__2_once, _init_l_Lake_Toml_stdTable_formatter___closed__2);
v___x_2160_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__0, &l_Lake_Toml_stdTable_formatter___closed__0_once, _init_l_Lake_Toml_stdTable_formatter___closed__0);
v___x_2161_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2161_, 0, v___x_2160_);
lean_closure_set(v___x_2161_, 1, v___x_2159_);
return v___x_2161_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__4(void){
_start:
{
lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2162_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__3, &l_Lake_Toml_stdTable_formatter___closed__3_once, _init_l_Lake_Toml_stdTable_formatter___closed__3);
v___x_2163_ = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter___boxed), 6, 1);
lean_closure_set(v___x_2163_, 0, v___x_2162_);
return v___x_2163_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1(void){
_start:
{
uint32_t v___x_2164_; lean_object* v___x_2165_; 
v___x_2164_ = 93;
v___x_2165_ = lean_box_uint32(v___x_2164_);
return v___x_2165_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__5(void){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; lean_object* v___x_2169_; 
v___x_2166_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2167_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__12));
v___x_2168_ = l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1;
v___x_2169_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2169_, 0, v___x_2168_);
lean_closure_set(v___x_2169_, 1, v___x_2167_);
lean_closure_set(v___x_2169_, 2, v___x_2166_);
return v___x_2169_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__6(void){
_start:
{
lean_object* v___x_2170_; lean_object* v___x_2171_; lean_object* v___x_2172_; 
v___x_2170_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__5, &l_Lake_Toml_stdTable_formatter___closed__5_once, _init_l_Lake_Toml_stdTable_formatter___closed__5);
v___x_2171_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2172_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2172_, 0, v___x_2171_);
lean_closure_set(v___x_2172_, 1, v___x_2170_);
return v___x_2172_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__7(void){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; lean_object* v___x_2175_; 
v___x_2173_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__6, &l_Lake_Toml_stdTable_formatter___closed__6_once, _init_l_Lake_Toml_stdTable_formatter___closed__6);
v___x_2174_ = lean_alloc_closure((void*)(l_Lake_Toml_key_formatter___boxed), 5, 0);
v___x_2175_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2175_, 0, v___x_2174_);
lean_closure_set(v___x_2175_, 1, v___x_2173_);
return v___x_2175_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__8(void){
_start:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; lean_object* v___x_2178_; 
v___x_2176_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__7, &l_Lake_Toml_stdTable_formatter___closed__7_once, _init_l_Lake_Toml_stdTable_formatter___closed__7);
v___x_2177_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2178_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2178_, 0, v___x_2177_);
lean_closure_set(v___x_2178_, 1, v___x_2176_);
return v___x_2178_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__9(void){
_start:
{
lean_object* v___x_2179_; lean_object* v___x_2180_; lean_object* v___x_2181_; 
v___x_2179_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__8, &l_Lake_Toml_stdTable_formatter___closed__8_once, _init_l_Lake_Toml_stdTable_formatter___closed__8);
v___x_2180_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__4, &l_Lake_Toml_stdTable_formatter___closed__4_once, _init_l_Lake_Toml_stdTable_formatter___closed__4);
v___x_2181_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2181_, 0, v___x_2180_);
lean_closure_set(v___x_2181_, 1, v___x_2179_);
return v___x_2181_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_formatter(lean_object* v_a_2182_, lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_){
_start:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; uint8_t v___x_2190_; lean_object* v___x_2191_; 
v___x_2187_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__0));
v___x_2188_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__1));
v___x_2189_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__9, &l_Lake_Toml_stdTable_formatter___closed__9_once, _init_l_Lake_Toml_stdTable_formatter___closed__9);
v___x_2190_ = 0;
v___x_2191_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2187_, v___x_2188_, v___x_2189_, v___x_2190_, v_a_2182_, v_a_2183_, v_a_2184_, v_a_2185_);
return v___x_2191_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_formatter___boxed(lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_, lean_object* v_a_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_Lake_Toml_stdTable_formatter(v_a_2192_, v_a_2193_, v_a_2194_, v_a_2195_);
lean_dec(v_a_2195_);
lean_dec_ref(v_a_2194_);
lean_dec(v_a_2193_);
lean_dec_ref(v_a_2192_);
return v_res_2197_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__0(void){
_start:
{
lean_object* v___x_2198_; lean_object* v___x_2199_; lean_object* v___x_2200_; 
v___x_2198_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__1, &l_Lake_Toml_stdTable_formatter___closed__1_once, _init_l_Lake_Toml_stdTable_formatter___closed__1);
v___x_2199_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__0, &l_Lake_Toml_stdTable_formatter___closed__0_once, _init_l_Lake_Toml_stdTable_formatter___closed__0);
v___x_2200_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2200_, 0, v___x_2199_);
lean_closure_set(v___x_2200_, 1, v___x_2198_);
return v___x_2200_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__1(void){
_start:
{
lean_object* v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__0, &l_Lake_Toml_arrayTable_formatter___closed__0_once, _init_l_Lake_Toml_arrayTable_formatter___closed__0);
v___x_2202_ = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter___boxed), 6, 1);
lean_closure_set(v___x_2202_, 0, v___x_2201_);
return v___x_2202_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__2(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; 
v___x_2203_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__5, &l_Lake_Toml_stdTable_formatter___closed__5_once, _init_l_Lake_Toml_stdTable_formatter___closed__5);
v___x_2204_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2204_, 0, v___x_2203_);
lean_closure_set(v___x_2204_, 1, v___x_2203_);
return v___x_2204_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__3(void){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; 
v___x_2205_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__2, &l_Lake_Toml_arrayTable_formatter___closed__2_once, _init_l_Lake_Toml_arrayTable_formatter___closed__2);
v___x_2206_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2207_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2207_, 0, v___x_2206_);
lean_closure_set(v___x_2207_, 1, v___x_2205_);
return v___x_2207_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__4(void){
_start:
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
v___x_2208_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__3, &l_Lake_Toml_arrayTable_formatter___closed__3_once, _init_l_Lake_Toml_arrayTable_formatter___closed__3);
v___x_2209_ = lean_alloc_closure((void*)(l_Lake_Toml_key_formatter___boxed), 5, 0);
v___x_2210_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2210_, 0, v___x_2209_);
lean_closure_set(v___x_2210_, 1, v___x_2208_);
return v___x_2210_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__5(void){
_start:
{
lean_object* v___x_2211_; lean_object* v___x_2212_; lean_object* v___x_2213_; 
v___x_2211_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__4, &l_Lake_Toml_arrayTable_formatter___closed__4_once, _init_l_Lake_Toml_arrayTable_formatter___closed__4);
v___x_2212_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2213_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2213_, 0, v___x_2212_);
lean_closure_set(v___x_2213_, 1, v___x_2211_);
return v___x_2213_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__6(void){
_start:
{
lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; 
v___x_2214_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__5, &l_Lake_Toml_arrayTable_formatter___closed__5_once, _init_l_Lake_Toml_arrayTable_formatter___closed__5);
v___x_2215_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__1, &l_Lake_Toml_arrayTable_formatter___closed__1_once, _init_l_Lake_Toml_arrayTable_formatter___closed__1);
v___x_2216_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2216_, 0, v___x_2215_);
lean_closure_set(v___x_2216_, 1, v___x_2214_);
return v___x_2216_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_formatter(lean_object* v_a_2217_, lean_object* v_a_2218_, lean_object* v_a_2219_, lean_object* v_a_2220_){
_start:
{
lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; uint8_t v___x_2225_; lean_object* v___x_2226_; 
v___x_2222_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__0));
v___x_2223_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__1));
v___x_2224_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__6, &l_Lake_Toml_arrayTable_formatter___closed__6_once, _init_l_Lake_Toml_arrayTable_formatter___closed__6);
v___x_2225_ = 0;
v___x_2226_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2222_, v___x_2223_, v___x_2224_, v___x_2225_, v_a_2217_, v_a_2218_, v_a_2219_, v_a_2220_);
return v___x_2226_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_formatter___boxed(lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_, lean_object* v_a_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_Lake_Toml_arrayTable_formatter(v_a_2227_, v_a_2228_, v_a_2229_, v_a_2230_);
lean_dec(v_a_2230_);
lean_dec_ref(v_a_2229_);
lean_dec(v_a_2228_);
lean_dec_ref(v_a_2227_);
return v_res_2232_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_table_formatter(lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2238_ = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_formatter___boxed), 5, 0);
v___x_2239_ = lean_alloc_closure((void*)(l_Lake_Toml_arrayTable_formatter___boxed), 5, 0);
v___x_2240_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2238_, v___x_2239_, v_a_2233_, v_a_2234_, v_a_2235_, v_a_2236_);
return v___x_2240_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_table_formatter___boxed(lean_object* v_a_2241_, lean_object* v_a_2242_, lean_object* v_a_2243_, lean_object* v_a_2244_, lean_object* v_a_2245_){
_start:
{
lean_object* v_res_2246_; 
v_res_2246_ = l_Lake_Toml_table_formatter(v_a_2241_, v_a_2242_, v_a_2243_, v_a_2244_);
lean_dec(v_a_2244_);
lean_dec_ref(v_a_2243_);
lean_dec(v_a_2242_);
lean_dec_ref(v_a_2241_);
return v_res_2246_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter(lean_object* v_val_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_, lean_object* v_a_2257_){
_start:
{
lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v___x_2259_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___closed__0));
v___x_2260_ = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___boxed), 6, 1);
lean_closure_set(v___x_2260_, 0, v_val_2253_);
v___x_2261_ = lean_alloc_closure((void*)(l_Lake_Toml_table_formatter___boxed), 5, 0);
v___x_2262_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2262_, 0, v___x_2260_);
lean_closure_set(v___x_2262_, 1, v___x_2261_);
v___x_2263_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2259_, v___x_2262_, v_a_2254_, v_a_2255_, v_a_2256_, v_a_2257_);
return v___x_2263_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___boxed(lean_object* v_val_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_, lean_object* v_a_2268_, lean_object* v_a_2269_){
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter(v_val_2264_, v_a_2265_, v_a_2266_, v_a_2267_, v_a_2268_);
lean_dec(v_a_2268_);
lean_dec_ref(v_a_2267_);
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2265_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter___redArg(){
_start:
{
lean_object* v___x_2272_; 
v___x_2272_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_2272_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter___redArg___boxed(lean_object* v_a_2273_){
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l_Lake_Toml_trailingSep_formatter___redArg();
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter(lean_object* v_a_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_){
_start:
{
lean_object* v___x_2280_; 
v___x_2280_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_2280_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter___boxed(lean_object* v_a_2281_, lean_object* v_a_2282_, lean_object* v_a_2283_, lean_object* v_a_2284_, lean_object* v_a_2285_){
_start:
{
lean_object* v_res_2286_; 
v_res_2286_ = l_Lake_Toml_trailingSep_formatter(v_a_2281_, v_a_2282_, v_a_2283_, v_a_2284_);
lean_dec(v_a_2284_);
lean_dec_ref(v_a_2283_);
lean_dec(v_a_2282_);
lean_dec_ref(v_a_2281_);
return v_res_2286_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(lean_object* v_val_2287_, lean_object* v_a_2288_, lean_object* v_a_2289_, lean_object* v_a_2290_, lean_object* v_a_2291_){
_start:
{
lean_object* v___x_2293_; lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; lean_object* v___x_2297_; lean_object* v___x_2298_; uint8_t v___x_2299_; lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; 
v___x_2293_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0));
v___x_2294_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1));
v___x_2295_ = lean_alloc_closure((void*)(l_Lake_Toml_header_formatter___boxed), 5, 0);
v___x_2296_ = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___boxed), 6, 1);
lean_closure_set(v___x_2296_, 0, v_val_2287_);
v___x_2297_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingSep_formatter___boxed), 5, 0);
v___x_2298_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2298_, 0, v___x_2296_);
lean_closure_set(v___x_2298_, 1, v___x_2297_);
v___x_2299_ = 1;
v___x_2300_ = lean_box(v___x_2299_);
v___x_2301_ = lean_alloc_closure((void*)(l_Lake_Toml_sepByLinebreak_formatter___boxed), 7, 2);
lean_closure_set(v___x_2301_, 0, v___x_2298_);
lean_closure_set(v___x_2301_, 1, v___x_2300_);
v___x_2302_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2302_, 0, v___x_2295_);
lean_closure_set(v___x_2302_, 1, v___x_2301_);
v___x_2303_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2293_, v___x_2294_, v___x_2302_, v___x_2299_, v_a_2288_, v_a_2289_, v_a_2290_, v_a_2291_);
return v___x_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter___boxed(lean_object* v_val_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_, lean_object* v_a_2307_, lean_object* v_a_2308_, lean_object* v_a_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(v_val_2304_, v_a_2305_, v_a_2306_, v_a_2307_, v_a_2308_);
lean_dec(v_a_2308_);
lean_dec_ref(v_a_2307_);
lean_dec(v_a_2306_);
lean_dec_ref(v_a_2305_);
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_val_formatter(lean_object* v_a_2311_, lean_object* v_a_2312_, lean_object* v_a_2313_, lean_object* v_a_2314_){
_start:
{
lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; uint8_t v___x_2319_; lean_object* v___x_2320_; 
v___x_2316_ = ((lean_object*)(l_Lake_Toml_val___closed__0));
v___x_2317_ = ((lean_object*)(l_Lake_Toml_val___closed__1));
v___x_2318_ = ((lean_object*)(l_Lake_Toml_val___closed__2));
v___x_2319_ = 1;
v___x_2320_ = l_Lake_Toml_recNodeWithAntiquot_formatter(v___x_2316_, v___x_2317_, v___x_2318_, v___x_2319_, v_a_2311_, v_a_2312_, v_a_2313_, v_a_2314_);
return v___x_2320_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_val_formatter___boxed(lean_object* v_a_2321_, lean_object* v_a_2322_, lean_object* v_a_2323_, lean_object* v_a_2324_, lean_object* v_a_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l_Lake_Toml_val_formatter(v_a_2321_, v_a_2322_, v_a_2323_, v_a_2324_);
lean_dec(v_a_2324_);
lean_dec_ref(v_a_2323_);
lean_dec(v_a_2322_);
lean_dec_ref(v_a_2321_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_toml_formatter(lean_object* v_a_2327_, lean_object* v_a_2328_, lean_object* v_a_2329_, lean_object* v_a_2330_){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2332_ = lean_alloc_closure((void*)(l_Lake_Toml_val_formatter___boxed), 5, 0);
v___x_2333_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(v___x_2332_, v_a_2327_, v_a_2328_, v_a_2329_, v_a_2330_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_toml_formatter___boxed(lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_, lean_object* v_a_2338_){
_start:
{
lean_object* v_res_2339_; 
v_res_2339_ = l_Lake_Toml_toml_formatter(v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
lean_dec(v_a_2337_);
lean_dec_ref(v_a_2336_);
lean_dec(v_a_2335_);
lean_dec_ref(v_a_2334_);
return v_res_2339_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_header_parenthesizer(lean_object* v_a_2340_, lean_object* v_a_2341_, lean_object* v_a_2342_, lean_object* v_a_2343_){
_start:
{
lean_object* v___x_2345_; lean_object* v___x_2346_; uint8_t v___x_2347_; lean_object* v___x_2348_; 
v___x_2345_ = ((lean_object*)(l_Lake_Toml_header___closed__0));
v___x_2346_ = ((lean_object*)(l_Lake_Toml_header___closed__1));
v___x_2347_ = 0;
v___x_2348_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v___x_2345_, v___x_2346_, v___x_2347_, v_a_2340_, v_a_2341_, v_a_2342_, v_a_2343_);
return v___x_2348_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_header_parenthesizer___boxed(lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_, lean_object* v_a_2353_){
_start:
{
lean_object* v_res_2354_; 
v_res_2354_ = l_Lake_Toml_header_parenthesizer(v_a_2349_, v_a_2350_, v_a_2351_, v_a_2352_);
lean_dec(v_a_2352_);
lean_dec_ref(v_a_2351_);
lean_dec(v_a_2350_);
lean_dec_ref(v_a_2349_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_parenthesizer(lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_, lean_object* v_a_2358_){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; uint8_t v___x_2362_; lean_object* v___x_2363_; 
v___x_2360_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__0));
v___x_2361_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__1));
v___x_2362_ = 0;
v___x_2363_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v___x_2360_, v___x_2361_, v___x_2362_, v_a_2355_, v_a_2356_, v_a_2357_, v_a_2358_);
return v___x_2363_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_parenthesizer___boxed(lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_, lean_object* v_a_2367_, lean_object* v_a_2368_){
_start:
{
lean_object* v_res_2369_; 
v_res_2369_ = l_Lake_Toml_unquotedKey_parenthesizer(v_a_2364_, v_a_2365_, v_a_2366_, v_a_2367_);
lean_dec(v_a_2367_);
lean_dec_ref(v_a_2366_);
lean_dec(v_a_2365_);
lean_dec_ref(v_a_2364_);
return v_res_2369_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_parenthesizer(lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_, lean_object* v_a_2373_){
_start:
{
lean_object* v___x_2375_; lean_object* v___x_2376_; uint8_t v___x_2377_; lean_object* v___x_2378_; 
v___x_2375_ = ((lean_object*)(l_Lake_Toml_basicString___closed__0));
v___x_2376_ = ((lean_object*)(l_Lake_Toml_basicString___closed__1));
v___x_2377_ = 0;
v___x_2378_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v___x_2375_, v___x_2376_, v___x_2377_, v_a_2370_, v_a_2371_, v_a_2372_, v_a_2373_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_parenthesizer___boxed(lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lake_Toml_basicString_parenthesizer(v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_parenthesizer(lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; uint8_t v___x_2392_; lean_object* v___x_2393_; 
v___x_2390_ = ((lean_object*)(l_Lake_Toml_literalString___closed__0));
v___x_2391_ = ((lean_object*)(l_Lake_Toml_literalString___closed__1));
v___x_2392_ = 0;
v___x_2393_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v___x_2390_, v___x_2391_, v___x_2392_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_);
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_parenthesizer___boxed(lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_Lake_Toml_literalString_parenthesizer(v_a_2394_, v_a_2395_, v_a_2396_, v_a_2397_);
lean_dec(v_a_2397_);
lean_dec_ref(v_a_2396_);
lean_dec(v_a_2395_);
lean_dec_ref(v_a_2394_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_parenthesizer(lean_object* v_a_2400_, lean_object* v_a_2401_, lean_object* v_a_2402_, lean_object* v_a_2403_){
_start:
{
lean_object* v___x_2405_; lean_object* v___x_2406_; lean_object* v___x_2407_; 
v___x_2405_ = lean_alloc_closure((void*)(l_Lake_Toml_basicString_parenthesizer___boxed), 5, 0);
v___x_2406_ = lean_alloc_closure((void*)(l_Lake_Toml_literalString_parenthesizer___boxed), 5, 0);
v___x_2407_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___x_2405_, v___x_2406_, v_a_2400_, v_a_2401_, v_a_2402_, v_a_2403_);
return v___x_2407_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_parenthesizer___boxed(lean_object* v_a_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v_res_2413_; 
v_res_2413_ = l_Lake_Toml_quotedKey_parenthesizer(v_a_2408_, v_a_2409_, v_a_2410_, v_a_2411_);
lean_dec(v_a_2411_);
lean_dec_ref(v_a_2410_);
lean_dec(v_a_2409_);
lean_dec_ref(v_a_2408_);
return v_res_2413_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; 
v___x_2414_ = lean_alloc_closure((void*)(l_Lake_Toml_quotedKey_parenthesizer___boxed), 5, 0);
v___x_2415_ = lean_alloc_closure((void*)(l_Lake_Toml_unquotedKey_parenthesizer___boxed), 5, 0);
v___x_2416_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2416_, 0, v___x_2415_);
lean_closure_set(v___x_2416_, 1, v___x_2414_);
return v___x_2416_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_parenthesizer(lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_){
_start:
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; uint8_t v___x_2425_; lean_object* v___x_2426_; 
v___x_2422_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__0));
v___x_2423_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__1));
v___x_2424_ = lean_obj_once(&l_Lake_Toml_simpleKey_parenthesizer___closed__0, &l_Lake_Toml_simpleKey_parenthesizer___closed__0_once, _init_l_Lake_Toml_simpleKey_parenthesizer___closed__0);
v___x_2425_ = 1;
v___x_2426_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2422_, v___x_2423_, v___x_2424_, v___x_2425_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_);
return v___x_2426_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_parenthesizer___boxed(lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_, lean_object* v_a_2431_){
_start:
{
lean_object* v_res_2432_; 
v_res_2432_ = l_Lake_Toml_simpleKey_parenthesizer(v_a_2427_, v_a_2428_, v_a_2429_, v_a_2430_);
lean_dec(v_a_2430_);
lean_dec_ref(v_a_2429_);
lean_dec(v_a_2428_);
lean_dec_ref(v_a_2427_);
return v_res_2432_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer___redArg(){
_start:
{
lean_object* v___x_2434_; 
v___x_2434_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_2434_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer___redArg___boxed(lean_object* v_a_2435_){
_start:
{
lean_object* v_res_2436_; 
v_res_2436_ = l_Lake_Toml_trailingWs_parenthesizer___redArg();
return v_res_2436_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer(lean_object* v_a_2437_, lean_object* v_a_2438_, lean_object* v_a_2439_, lean_object* v_a_2440_){
_start:
{
lean_object* v___x_2442_; 
v___x_2442_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_2442_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer___boxed(lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_, lean_object* v_a_2447_){
_start:
{
lean_object* v_res_2448_; 
v_res_2448_ = l_Lake_Toml_trailingWs_parenthesizer(v_a_2443_, v_a_2444_, v_a_2445_, v_a_2446_);
lean_dec(v_a_2446_);
lean_dec_ref(v_a_2445_);
lean_dec(v_a_2444_);
lean_dec_ref(v_a_2443_);
return v_res_2448_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2449_; lean_object* v___x_2450_; lean_object* v___x_2451_; lean_object* v___x_2452_; 
v___x_2449_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2450_ = ((lean_object*)(l_Lake_Toml_key___closed__5));
v___x_2451_ = l_Lake_Toml_key_formatter___closed__0___boxed__const__1;
v___x_2452_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2452_, 0, v___x_2451_);
lean_closure_set(v___x_2452_, 1, v___x_2450_);
lean_closure_set(v___x_2452_, 2, v___x_2449_);
return v___x_2452_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2453_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2454_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__0, &l_Lake_Toml_key_parenthesizer___closed__0_once, _init_l_Lake_Toml_key_parenthesizer___closed__0);
v___x_2455_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2455_, 0, v___x_2454_);
lean_closure_set(v___x_2455_, 1, v___x_2453_);
return v___x_2455_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2458_; 
v___x_2456_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__1, &l_Lake_Toml_key_parenthesizer___closed__1_once, _init_l_Lake_Toml_key_parenthesizer___closed__1);
v___x_2457_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2458_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2458_, 0, v___x_2457_);
lean_closure_set(v___x_2458_, 1, v___x_2456_);
return v___x_2458_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__3(void){
_start:
{
uint8_t v___x_2459_; lean_object* v___x_2460_; lean_object* v___x_2461_; lean_object* v___x_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; 
v___x_2459_ = 0;
v___x_2460_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__2, &l_Lake_Toml_key_parenthesizer___closed__2_once, _init_l_Lake_Toml_key_parenthesizer___closed__2);
v___x_2461_ = ((lean_object*)(l_Lake_Toml_key___closed__3));
v___x_2462_ = lean_alloc_closure((void*)(l_Lake_Toml_simpleKey_parenthesizer___boxed), 5, 0);
v___x_2463_ = lean_box(v___x_2459_);
v___x_2464_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_2464_, 0, v___x_2462_);
lean_closure_set(v___x_2464_, 1, v___x_2461_);
lean_closure_set(v___x_2464_, 2, v___x_2460_);
lean_closure_set(v___x_2464_, 3, v___x_2463_);
return v___x_2464_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v___x_2465_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__3, &l_Lake_Toml_key_parenthesizer___closed__3_once, _init_l_Lake_Toml_key_parenthesizer___closed__3);
v___x_2466_ = ((lean_object*)(l_Lake_Toml_key___closed__2));
v___x_2467_ = lean_alloc_closure((void*)(l_Lean_Parser_setExpected_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2467_, 0, v___x_2466_);
lean_closure_set(v___x_2467_, 1, v___x_2465_);
return v___x_2467_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_key_parenthesizer(lean_object* v_a_2468_, lean_object* v_a_2469_, lean_object* v_a_2470_, lean_object* v_a_2471_){
_start:
{
lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; uint8_t v___x_2476_; lean_object* v___x_2477_; 
v___x_2473_ = ((lean_object*)(l_Lake_Toml_key___closed__0));
v___x_2474_ = ((lean_object*)(l_Lake_Toml_key___closed__1));
v___x_2475_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__4, &l_Lake_Toml_key_parenthesizer___closed__4_once, _init_l_Lake_Toml_key_parenthesizer___closed__4);
v___x_2476_ = 1;
v___x_2477_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2473_, v___x_2474_, v___x_2475_, v___x_2476_, v_a_2468_, v_a_2469_, v_a_2470_, v_a_2471_);
return v___x_2477_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_key_parenthesizer___boxed(lean_object* v_a_2478_, lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v_res_2483_; 
v_res_2483_ = l_Lake_Toml_key_parenthesizer(v_a_2478_, v_a_2479_, v_a_2480_, v_a_2481_);
lean_dec(v_a_2481_);
lean_dec_ref(v_a_2480_);
lean_dec(v_a_2479_);
lean_dec_ref(v_a_2478_);
return v_res_2483_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; lean_object* v___x_2486_; lean_object* v___x_2487_; 
v___x_2484_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2485_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3));
v___x_2486_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1;
v___x_2487_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2487_, 0, v___x_2486_);
lean_closure_set(v___x_2487_, 1, v___x_2485_);
lean_closure_set(v___x_2487_, 2, v___x_2484_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer(lean_object* v_val_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_, lean_object* v_a_2491_, lean_object* v_a_2492_){
_start:
{
lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; lean_object* v___x_2497_; lean_object* v___x_2498_; lean_object* v___x_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; lean_object* v___x_2502_; uint8_t v___x_2503_; lean_object* v___x_2504_; 
v___x_2494_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0));
v___x_2495_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1));
v___x_2496_ = lean_alloc_closure((void*)(l_Lake_Toml_key_parenthesizer___boxed), 5, 0);
v___x_2497_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2498_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0);
lean_inc_ref(v___x_2497_);
v___x_2499_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2499_, 0, v___x_2497_);
lean_closure_set(v___x_2499_, 1, v_val_2488_);
v___x_2500_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2500_, 0, v___x_2498_);
lean_closure_set(v___x_2500_, 1, v___x_2499_);
v___x_2501_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2501_, 0, v___x_2497_);
lean_closure_set(v___x_2501_, 1, v___x_2500_);
v___x_2502_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2502_, 0, v___x_2496_);
lean_closure_set(v___x_2502_, 1, v___x_2501_);
v___x_2503_ = 1;
v___x_2504_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2494_, v___x_2495_, v___x_2502_, v___x_2503_, v_a_2489_, v_a_2490_, v_a_2491_, v_a_2492_);
return v___x_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___boxed(lean_object* v_val_2505_, lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_){
_start:
{
lean_object* v_res_2511_; 
v_res_2511_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer(v_val_2505_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
lean_dec(v_a_2509_);
lean_dec_ref(v_a_2508_);
lean_dec(v_a_2507_);
lean_dec_ref(v_a_2506_);
return v_res_2511_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer___lam__0(lean_object* v___x_2512_, lean_object* v___x_2513_, lean_object* v___y_2514_, lean_object* v___y_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_){
_start:
{
lean_object* v___x_2519_; 
v___x_2519_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(v___x_2512_, v___x_2513_, v___y_2514_, v___y_2515_, v___y_2516_, v___y_2517_);
return v___x_2519_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer___lam__0___boxed(lean_object* v___x_2520_, lean_object* v___x_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_, lean_object* v___y_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_Lake_Toml_stdTable_parenthesizer___lam__0(v___x_2520_, v___x_2521_, v___y_2522_, v___y_2523_, v___y_2524_, v___y_2525_);
lean_dec(v___y_2525_);
lean_dec_ref(v___y_2524_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
return v_res_2527_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2528_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2529_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__3));
v___x_2530_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
v___x_2531_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2531_, 0, v___x_2530_);
lean_closure_set(v___x_2531_, 1, v___x_2529_);
lean_closure_set(v___x_2531_, 2, v___x_2528_);
return v___x_2531_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2532_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2533_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__6));
v___x_2534_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
v___x_2535_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2535_, 0, v___x_2534_);
lean_closure_set(v___x_2535_, 1, v___x_2533_);
lean_closure_set(v___x_2535_, 2, v___x_2532_);
return v___x_2535_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__1, &l_Lake_Toml_stdTable_parenthesizer___closed__1_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__1);
v___x_2537_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2537_, 0, v___x_2536_);
return v___x_2537_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; lean_object* v___f_2540_; 
v___x_2538_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__2, &l_Lake_Toml_stdTable_parenthesizer___closed__2_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__2);
v___x_2539_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__0, &l_Lake_Toml_stdTable_parenthesizer___closed__0_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__0);
v___f_2540_ = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_parenthesizer___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2540_, 0, v___x_2539_);
lean_closure_set(v___f_2540_, 1, v___x_2538_);
return v___f_2540_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; 
v___x_2541_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2542_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__12));
v___x_2543_ = l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1;
v___x_2544_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2544_, 0, v___x_2543_);
lean_closure_set(v___x_2544_, 1, v___x_2542_);
lean_closure_set(v___x_2544_, 2, v___x_2541_);
return v___x_2544_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; 
v___x_2545_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__4, &l_Lake_Toml_stdTable_parenthesizer___closed__4_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__4);
v___x_2546_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2547_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2547_, 0, v___x_2546_);
lean_closure_set(v___x_2547_, 1, v___x_2545_);
return v___x_2547_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_2548_; lean_object* v___x_2549_; lean_object* v___x_2550_; 
v___x_2548_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__5, &l_Lake_Toml_stdTable_parenthesizer___closed__5_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__5);
v___x_2549_ = lean_alloc_closure((void*)(l_Lake_Toml_key_parenthesizer___boxed), 5, 0);
v___x_2550_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2550_, 0, v___x_2549_);
lean_closure_set(v___x_2550_, 1, v___x_2548_);
return v___x_2550_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_2551_; lean_object* v___x_2552_; lean_object* v___x_2553_; 
v___x_2551_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__6, &l_Lake_Toml_stdTable_parenthesizer___closed__6_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__6);
v___x_2552_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2553_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2553_, 0, v___x_2552_);
lean_closure_set(v___x_2553_, 1, v___x_2551_);
return v___x_2553_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_2554_; lean_object* v___f_2555_; lean_object* v___x_2556_; 
v___x_2554_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__7, &l_Lake_Toml_stdTable_parenthesizer___closed__7_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__7);
v___f_2555_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__3, &l_Lake_Toml_stdTable_parenthesizer___closed__3_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__3);
v___x_2556_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2556_, 0, v___f_2555_);
lean_closure_set(v___x_2556_, 1, v___x_2554_);
return v___x_2556_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer(lean_object* v_a_2557_, lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_){
_start:
{
lean_object* v___x_2562_; lean_object* v___x_2563_; lean_object* v___x_2564_; uint8_t v___x_2565_; lean_object* v___x_2566_; 
v___x_2562_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__0));
v___x_2563_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__1));
v___x_2564_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__8, &l_Lake_Toml_stdTable_parenthesizer___closed__8_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__8);
v___x_2565_ = 0;
v___x_2566_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2562_, v___x_2563_, v___x_2564_, v___x_2565_, v_a_2557_, v_a_2558_, v_a_2559_, v_a_2560_);
return v___x_2566_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer___boxed(lean_object* v_a_2567_, lean_object* v_a_2568_, lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_Lake_Toml_stdTable_parenthesizer(v_a_2567_, v_a_2568_, v_a_2569_, v_a_2570_);
lean_dec(v_a_2570_);
lean_dec_ref(v_a_2569_);
lean_dec(v_a_2568_);
lean_dec_ref(v_a_2567_);
return v_res_2572_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; lean_object* v___f_2575_; 
v___x_2573_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__1, &l_Lake_Toml_stdTable_parenthesizer___closed__1_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__1);
v___x_2574_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__0, &l_Lake_Toml_stdTable_parenthesizer___closed__0_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__0);
v___f_2575_ = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_parenthesizer___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2575_, 0, v___x_2574_);
lean_closure_set(v___f_2575_, 1, v___x_2573_);
return v___f_2575_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; 
v___x_2576_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__4, &l_Lake_Toml_stdTable_parenthesizer___closed__4_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__4);
v___x_2577_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2577_, 0, v___x_2576_);
lean_closure_set(v___x_2577_, 1, v___x_2576_);
return v___x_2577_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v___x_2578_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__1, &l_Lake_Toml_arrayTable_parenthesizer___closed__1_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__1);
v___x_2579_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2580_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2580_, 0, v___x_2579_);
lean_closure_set(v___x_2580_, 1, v___x_2578_);
return v___x_2580_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; 
v___x_2581_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__2, &l_Lake_Toml_arrayTable_parenthesizer___closed__2_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__2);
v___x_2582_ = lean_alloc_closure((void*)(l_Lake_Toml_key_parenthesizer___boxed), 5, 0);
v___x_2583_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2583_, 0, v___x_2582_);
lean_closure_set(v___x_2583_, 1, v___x_2581_);
return v___x_2583_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2586_; 
v___x_2584_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__3, &l_Lake_Toml_arrayTable_parenthesizer___closed__3_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__3);
v___x_2585_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2586_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2586_, 0, v___x_2585_);
lean_closure_set(v___x_2586_, 1, v___x_2584_);
return v___x_2586_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_2587_; lean_object* v___f_2588_; lean_object* v___x_2589_; 
v___x_2587_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__4, &l_Lake_Toml_arrayTable_parenthesizer___closed__4_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__4);
v___f_2588_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__0, &l_Lake_Toml_arrayTable_parenthesizer___closed__0_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__0);
v___x_2589_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2589_, 0, v___f_2588_);
lean_closure_set(v___x_2589_, 1, v___x_2587_);
return v___x_2589_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_parenthesizer(lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_, lean_object* v_a_2593_){
_start:
{
lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; uint8_t v___x_2598_; lean_object* v___x_2599_; 
v___x_2595_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__0));
v___x_2596_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__1));
v___x_2597_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__5, &l_Lake_Toml_arrayTable_parenthesizer___closed__5_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__5);
v___x_2598_ = 0;
v___x_2599_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2595_, v___x_2596_, v___x_2597_, v___x_2598_, v_a_2590_, v_a_2591_, v_a_2592_, v_a_2593_);
return v___x_2599_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_parenthesizer___boxed(lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_, lean_object* v_a_2604_){
_start:
{
lean_object* v_res_2605_; 
v_res_2605_ = l_Lake_Toml_arrayTable_parenthesizer(v_a_2600_, v_a_2601_, v_a_2602_, v_a_2603_);
lean_dec(v_a_2603_);
lean_dec_ref(v_a_2602_);
lean_dec(v_a_2601_);
lean_dec_ref(v_a_2600_);
return v_res_2605_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_table_parenthesizer(lean_object* v_a_2606_, lean_object* v_a_2607_, lean_object* v_a_2608_, lean_object* v_a_2609_){
_start:
{
lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2611_ = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_parenthesizer___boxed), 5, 0);
v___x_2612_ = lean_alloc_closure((void*)(l_Lake_Toml_arrayTable_parenthesizer___boxed), 5, 0);
v___x_2613_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___x_2611_, v___x_2612_, v_a_2606_, v_a_2607_, v_a_2608_, v_a_2609_);
return v___x_2613_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_table_parenthesizer___boxed(lean_object* v_a_2614_, lean_object* v_a_2615_, lean_object* v_a_2616_, lean_object* v_a_2617_, lean_object* v_a_2618_){
_start:
{
lean_object* v_res_2619_; 
v_res_2619_ = l_Lake_Toml_table_parenthesizer(v_a_2614_, v_a_2615_, v_a_2616_, v_a_2617_);
lean_dec(v_a_2617_);
lean_dec_ref(v_a_2616_);
lean_dec(v_a_2615_);
lean_dec_ref(v_a_2614_);
return v_res_2619_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer(lean_object* v_val_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_){
_start:
{
lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; 
v___x_2632_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___closed__0));
v___x_2633_ = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2633_, 0, v_val_2626_);
v___x_2634_ = lean_alloc_closure((void*)(l_Lake_Toml_table_parenthesizer___boxed), 5, 0);
v___x_2635_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2635_, 0, v___x_2633_);
lean_closure_set(v___x_2635_, 1, v___x_2634_);
v___x_2636_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2632_, v___x_2635_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
return v___x_2636_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___boxed(lean_object* v_val_2637_, lean_object* v_a_2638_, lean_object* v_a_2639_, lean_object* v_a_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer(v_val_2637_, v_a_2638_, v_a_2639_, v_a_2640_, v_a_2641_);
lean_dec(v_a_2641_);
lean_dec_ref(v_a_2640_);
lean_dec(v_a_2639_);
lean_dec_ref(v_a_2638_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer___redArg(){
_start:
{
lean_object* v___x_2645_; 
v___x_2645_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_2645_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer___redArg___boxed(lean_object* v_a_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_Lake_Toml_trailingSep_parenthesizer___redArg();
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer(lean_object* v_a_2648_, lean_object* v_a_2649_, lean_object* v_a_2650_, lean_object* v_a_2651_){
_start:
{
lean_object* v___x_2653_; 
v___x_2653_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_2653_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer___boxed(lean_object* v_a_2654_, lean_object* v_a_2655_, lean_object* v_a_2656_, lean_object* v_a_2657_, lean_object* v_a_2658_){
_start:
{
lean_object* v_res_2659_; 
v_res_2659_ = l_Lake_Toml_trailingSep_parenthesizer(v_a_2654_, v_a_2655_, v_a_2656_, v_a_2657_);
lean_dec(v_a_2657_);
lean_dec_ref(v_a_2656_);
lean_dec(v_a_2655_);
lean_dec_ref(v_a_2654_);
return v_res_2659_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(lean_object* v_val_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_){
_start:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; uint8_t v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; lean_object* v___x_2675_; lean_object* v___x_2676_; 
v___x_2666_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0));
v___x_2667_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1));
v___x_2668_ = lean_alloc_closure((void*)(l_Lake_Toml_header_parenthesizer___boxed), 5, 0);
v___x_2669_ = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2669_, 0, v_val_2660_);
v___x_2670_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingSep_parenthesizer___boxed), 5, 0);
v___x_2671_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2671_, 0, v___x_2669_);
lean_closure_set(v___x_2671_, 1, v___x_2670_);
v___x_2672_ = 1;
v___x_2673_ = lean_box(v___x_2672_);
v___x_2674_ = lean_alloc_closure((void*)(l_Lake_Toml_sepByLinebreak_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2674_, 0, v___x_2671_);
lean_closure_set(v___x_2674_, 1, v___x_2673_);
v___x_2675_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2675_, 0, v___x_2668_);
lean_closure_set(v___x_2675_, 1, v___x_2674_);
v___x_2676_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2666_, v___x_2667_, v___x_2675_, v___x_2672_, v_a_2661_, v_a_2662_, v_a_2663_, v_a_2664_);
return v___x_2676_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer___boxed(lean_object* v_val_2677_, lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(v_val_2677_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
lean_dec(v_a_2681_);
lean_dec_ref(v_a_2680_);
lean_dec(v_a_2679_);
lean_dec_ref(v_a_2678_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_val_parenthesizer(lean_object* v_a_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_, lean_object* v_a_2687_){
_start:
{
lean_object* v___x_2689_; lean_object* v___x_2690_; lean_object* v___x_2691_; uint8_t v___x_2692_; lean_object* v___x_2693_; 
v___x_2689_ = ((lean_object*)(l_Lake_Toml_val___closed__0));
v___x_2690_ = ((lean_object*)(l_Lake_Toml_val___closed__1));
v___x_2691_ = ((lean_object*)(l_Lake_Toml_val___closed__2));
v___x_2692_ = 1;
v___x_2693_ = l_Lake_Toml_recNodeWithAntiquot_parenthesizer(v___x_2689_, v___x_2690_, v___x_2691_, v___x_2692_, v_a_2684_, v_a_2685_, v_a_2686_, v_a_2687_);
return v___x_2693_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_val_parenthesizer___boxed(lean_object* v_a_2694_, lean_object* v_a_2695_, lean_object* v_a_2696_, lean_object* v_a_2697_, lean_object* v_a_2698_){
_start:
{
lean_object* v_res_2699_; 
v_res_2699_ = l_Lake_Toml_val_parenthesizer(v_a_2694_, v_a_2695_, v_a_2696_, v_a_2697_);
lean_dec(v_a_2697_);
lean_dec_ref(v_a_2696_);
lean_dec(v_a_2695_);
lean_dec_ref(v_a_2694_);
return v_res_2699_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_toml_parenthesizer(lean_object* v_a_2700_, lean_object* v_a_2701_, lean_object* v_a_2702_, lean_object* v_a_2703_){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; 
v___x_2705_ = lean_alloc_closure((void*)(l_Lake_Toml_val_parenthesizer___boxed), 5, 0);
v___x_2706_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(v___x_2705_, v_a_2700_, v_a_2701_, v_a_2702_, v_a_2703_);
return v___x_2706_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_toml_parenthesizer___boxed(lean_object* v_a_2707_, lean_object* v_a_2708_, lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_){
_start:
{
lean_object* v_res_2712_; 
v_res_2712_ = l_Lake_Toml_toml_parenthesizer(v_a_2707_, v_a_2708_, v_a_2709_, v_a_2710_);
lean_dec(v_a_2710_);
lean_dec_ref(v_a_2709_);
lean_dec(v_a_2708_);
lean_dec_ref(v_a_2707_);
return v_res_2712_;
}
}
static lean_object* _init_l_Lake_Toml_toml___closed__0(void){
_start:
{
lean_object* v___x_2713_; lean_object* v___x_2714_; 
v___x_2713_ = l_Lake_Toml_val;
v___x_2714_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore(v___x_2713_);
return v___x_2714_;
}
}
static lean_object* _init_l_Lake_Toml_toml___closed__1(void){
_start:
{
lean_object* v___x_2715_; lean_object* v___x_2716_; lean_object* v___x_2717_; 
v___x_2715_ = lean_obj_once(&l_Lake_Toml_toml___closed__0, &l_Lake_Toml_toml___closed__0_once, _init_l_Lake_Toml_toml___closed__0);
v___x_2716_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1));
v___x_2717_ = l_Lean_Parser_withCache(v___x_2716_, v___x_2715_);
return v___x_2717_;
}
}
static lean_object* _init_l_Lake_Toml_toml(void){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = lean_obj_once(&l_Lake_Toml_toml___closed__1, &l_Lake_Toml_toml___closed__1_once, _init_l_Lake_Toml_toml___closed__1);
return v___x_2718_;
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
