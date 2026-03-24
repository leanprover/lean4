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
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
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
lean_dec_ref(v_x_84_);
v___x_86_ = 0;
return v___x_86_;
}
}
else
{
if (lean_obj_tag(v_x_84_) == 0)
{
uint8_t v___x_87_; 
lean_dec_ref(v_x_83_);
v___x_87_ = 0;
return v___x_87_;
}
else
{
lean_object* v_val_88_; lean_object* v_val_89_; uint8_t v___x_90_; 
v_val_88_ = lean_ctor_get(v_x_83_, 0);
lean_inc(v_val_88_);
lean_dec_ref(v_x_83_);
v_val_89_ = lean_ctor_get(v_x_84_, 0);
lean_inc(v_val_89_);
lean_dec_ref(v_x_84_);
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
lean_object* v_inputString_119_; uint32_t v_curr_120_; uint8_t v___y_122_; uint32_t v___x_133_; uint8_t v___x_134_; 
v_inputString_119_ = lean_ctor_get(v_toInputContext_113_, 0);
v_curr_120_ = lean_string_utf8_get_fast(v_inputString_119_, v_pos_114_);
v___x_133_ = 32;
v___x_134_ = lean_uint32_dec_eq(v_curr_120_, v___x_133_);
if (v___x_134_ == 0)
{
uint32_t v___x_135_; uint8_t v___x_136_; 
v___x_135_ = 9;
v___x_136_ = lean_uint32_dec_eq(v_curr_120_, v___x_135_);
v___y_122_ = v___x_136_;
goto v___jp_121_;
}
else
{
v___y_122_ = v___x_134_;
goto v___jp_121_;
}
v___jp_121_:
{
if (v___y_122_ == 0)
{
uint32_t v___x_123_; uint8_t v___x_124_; 
v___x_123_ = 10;
v___x_124_ = lean_uint32_dec_eq(v_curr_120_, v___x_123_);
if (v___x_124_ == 0)
{
uint32_t v___x_125_; uint8_t v___x_126_; 
v___x_125_ = 13;
v___x_126_ = lean_uint32_dec_eq(v_curr_120_, v___x_125_);
if (v___x_126_ == 0)
{
return v_s_112_;
}
else
{
lean_object* v___x_127_; lean_object* v_s_128_; lean_object* v_errorMsg_129_; lean_object* v___x_130_; uint8_t v___x_131_; 
lean_inc(v_pos_114_);
v___x_127_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_112_, v_c_111_, v_pos_114_);
lean_dec(v_pos_114_);
v_s_128_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_111_, v___x_127_);
v_errorMsg_129_ = lean_ctor_get(v_s_128_, 4);
lean_inc(v_errorMsg_129_);
v___x_130_ = lean_box(0);
v___x_131_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_129_, v___x_130_);
if (v___x_131_ == 0)
{
return v_s_128_;
}
else
{
v_s_112_ = v_s_128_;
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
LEAN_EXPORT lean_object* l_Lake_Toml_wsNewlineFn___boxed(lean_object* v_c_137_, lean_object* v_s_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lake_Toml_wsNewlineFn(v_c_137_, v_s_138_);
lean_dec_ref(v_c_137_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingFn(lean_object* v_c_140_, lean_object* v_s_141_){
_start:
{
lean_object* v_toInputContext_142_; lean_object* v_pos_143_; uint8_t v___x_147_; 
v_toInputContext_142_ = lean_ctor_get(v_c_140_, 0);
v_pos_143_ = lean_ctor_get(v_s_141_, 2);
v___x_147_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_142_, v_pos_143_);
if (v___x_147_ == 0)
{
lean_object* v_inputString_148_; uint32_t v_curr_149_; uint8_t v___y_151_; uint32_t v___x_170_; uint8_t v___x_171_; 
v_inputString_148_ = lean_ctor_get(v_toInputContext_142_, 0);
v_curr_149_ = lean_string_utf8_get_fast(v_inputString_148_, v_pos_143_);
v___x_170_ = 32;
v___x_171_ = lean_uint32_dec_eq(v_curr_149_, v___x_170_);
if (v___x_171_ == 0)
{
uint32_t v___x_172_; uint8_t v___x_173_; 
v___x_172_ = 9;
v___x_173_ = lean_uint32_dec_eq(v_curr_149_, v___x_172_);
v___y_151_ = v___x_173_;
goto v___jp_150_;
}
else
{
v___y_151_ = v___x_171_;
goto v___jp_150_;
}
v___jp_150_:
{
if (v___y_151_ == 0)
{
uint32_t v___x_152_; uint8_t v___x_153_; 
v___x_152_ = 10;
v___x_153_ = lean_uint32_dec_eq(v_curr_149_, v___x_152_);
if (v___x_153_ == 0)
{
uint32_t v___x_154_; uint8_t v___x_155_; 
v___x_154_ = 13;
v___x_155_ = lean_uint32_dec_eq(v_curr_149_, v___x_154_);
if (v___x_155_ == 0)
{
uint32_t v___x_156_; uint8_t v___x_157_; 
v___x_156_ = 35;
v___x_157_ = lean_uint32_dec_eq(v_curr_149_, v___x_156_);
if (v___x_157_ == 0)
{
return v_s_141_;
}
else
{
lean_object* v___x_158_; lean_object* v_s_159_; lean_object* v_errorMsg_160_; lean_object* v___x_161_; uint8_t v___x_162_; 
lean_inc(v_pos_143_);
v___x_158_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_141_, v_c_140_, v_pos_143_);
lean_dec(v_pos_143_);
v_s_159_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(v_c_140_, v___x_158_);
v_errorMsg_160_ = lean_ctor_get(v_s_159_, 4);
lean_inc(v_errorMsg_160_);
v___x_161_ = lean_box(0);
v___x_162_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_160_, v___x_161_);
if (v___x_162_ == 0)
{
return v_s_159_;
}
else
{
v_s_141_ = v_s_159_;
goto _start;
}
}
}
else
{
lean_object* v___x_164_; lean_object* v_s_165_; lean_object* v_errorMsg_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
lean_inc(v_pos_143_);
v___x_164_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_141_, v_c_140_, v_pos_143_);
lean_dec(v_pos_143_);
v_s_165_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_140_, v___x_164_);
v_errorMsg_166_ = lean_ctor_get(v_s_165_, 4);
lean_inc(v_errorMsg_166_);
v___x_167_ = lean_box(0);
v___x_168_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_166_, v___x_167_);
if (v___x_168_ == 0)
{
return v_s_165_;
}
else
{
v_s_141_ = v_s_165_;
goto _start;
}
}
}
else
{
lean_inc(v_pos_143_);
goto v___jp_144_;
}
}
else
{
lean_inc(v_pos_143_);
goto v___jp_144_;
}
}
}
else
{
return v_s_141_;
}
v___jp_144_:
{
lean_object* v___x_145_; 
v___x_145_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_141_, v_c_140_, v_pos_143_);
lean_dec(v_pos_143_);
v_s_141_ = v___x_145_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingFn___boxed(lean_object* v_c_174_, lean_object* v_s_175_){
_start:
{
lean_object* v_res_176_; 
v_res_176_ = l_Lake_Toml_trailingFn(v_c_174_, v_s_175_);
lean_dec_ref(v_c_174_);
return v_res_176_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_isEscapeChar(uint32_t v_c_177_){
_start:
{
uint8_t v___y_179_; uint32_t v___x_190_; uint8_t v___x_191_; 
v___x_190_ = 98;
v___x_191_ = lean_uint32_dec_eq(v_c_177_, v___x_190_);
if (v___x_191_ == 0)
{
uint32_t v___x_192_; uint8_t v___x_193_; 
v___x_192_ = 116;
v___x_193_ = lean_uint32_dec_eq(v_c_177_, v___x_192_);
v___y_179_ = v___x_193_;
goto v___jp_178_;
}
else
{
v___y_179_ = v___x_191_;
goto v___jp_178_;
}
v___jp_178_:
{
if (v___y_179_ == 0)
{
uint32_t v___x_180_; uint8_t v___x_181_; 
v___x_180_ = 110;
v___x_181_ = lean_uint32_dec_eq(v_c_177_, v___x_180_);
if (v___x_181_ == 0)
{
uint32_t v___x_182_; uint8_t v___x_183_; 
v___x_182_ = 102;
v___x_183_ = lean_uint32_dec_eq(v_c_177_, v___x_182_);
if (v___x_183_ == 0)
{
uint32_t v___x_184_; uint8_t v___x_185_; 
v___x_184_ = 114;
v___x_185_ = lean_uint32_dec_eq(v_c_177_, v___x_184_);
if (v___x_185_ == 0)
{
uint32_t v___x_186_; uint8_t v___x_187_; 
v___x_186_ = 34;
v___x_187_ = lean_uint32_dec_eq(v_c_177_, v___x_186_);
if (v___x_187_ == 0)
{
uint32_t v___x_188_; uint8_t v___x_189_; 
v___x_188_ = 92;
v___x_189_ = lean_uint32_dec_eq(v_c_177_, v___x_188_);
return v___x_189_;
}
else
{
return v___x_187_;
}
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
return v___y_179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_isEscapeChar___boxed(lean_object* v_c_194_){
_start:
{
uint32_t v_c_boxed_195_; uint8_t v_res_196_; lean_object* v_r_197_; 
v_c_boxed_195_ = lean_unbox_uint32(v_c_194_);
lean_dec(v_c_194_);
v_res_196_ = l_Lake_Toml_isEscapeChar(v_c_boxed_195_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0(lean_object* v___y_198_, lean_object* v___y_199_){
_start:
{
lean_object* v_s_200_; lean_object* v_errorMsg_201_; lean_object* v___x_202_; uint8_t v___x_203_; 
v_s_200_ = l_Lake_Toml_wsFn(v___y_198_, v___y_199_);
v_errorMsg_201_ = lean_ctor_get(v_s_200_, 4);
lean_inc(v_errorMsg_201_);
v___x_202_ = lean_box(0);
v___x_203_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_201_, v___x_202_);
if (v___x_203_ == 0)
{
return v_s_200_;
}
else
{
lean_object* v_s_204_; lean_object* v_errorMsg_205_; uint8_t v___x_206_; 
v_s_204_ = l_Lake_Toml_newlineFn(v___y_198_, v_s_200_);
v_errorMsg_205_ = lean_ctor_get(v_s_204_, 4);
lean_inc(v_errorMsg_205_);
v___x_206_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_205_, v___x_202_);
if (v___x_206_ == 0)
{
return v_s_204_;
}
else
{
lean_object* v___x_207_; 
v___x_207_ = l_Lake_Toml_wsNewlineFn(v___y_198_, v_s_204_);
return v___x_207_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0___boxed(lean_object* v___y_208_, lean_object* v___y_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0(v___y_208_, v___y_209_);
lean_dec_ref(v___y_208_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1(lean_object* v___y_211_, lean_object* v___y_212_){
_start:
{
lean_object* v_s_213_; lean_object* v_errorMsg_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v_s_213_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v___y_211_, v___y_212_);
v_errorMsg_214_ = lean_ctor_get(v_s_213_, 4);
lean_inc(v_errorMsg_214_);
v___x_215_ = lean_box(0);
v___x_216_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_214_, v___x_215_);
if (v___x_216_ == 0)
{
return v_s_213_;
}
else
{
lean_object* v___x_217_; 
v___x_217_ = l_Lake_Toml_wsNewlineFn(v___y_211_, v_s_213_);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1___boxed(lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1(v___y_218_, v___y_219_);
lean_dec_ref(v___y_218_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(lean_object* v_c_221_, lean_object* v_x_222_, lean_object* v_x_223_){
_start:
{
lean_object* v_zero_224_; uint8_t v_isZero_225_; 
v_zero_224_ = lean_unsigned_to_nat(0u);
v_isZero_225_ = lean_nat_dec_eq(v_x_222_, v_zero_224_);
if (v_isZero_225_ == 1)
{
lean_dec(v_x_222_);
return v_x_223_;
}
else
{
lean_object* v_s_226_; lean_object* v_errorMsg_227_; lean_object* v___x_228_; uint8_t v___x_229_; 
v_s_226_ = l_Lean_Parser_hexDigitFn(v_c_221_, v_x_223_);
v_errorMsg_227_ = lean_ctor_get(v_s_226_, 4);
lean_inc(v_errorMsg_227_);
v___x_228_ = lean_box(0);
v___x_229_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_227_, v___x_228_);
if (v___x_229_ == 0)
{
lean_dec(v_x_222_);
return v_s_226_;
}
else
{
lean_object* v_one_230_; lean_object* v_n_231_; 
v_one_230_ = lean_unsigned_to_nat(1u);
v_n_231_ = lean_nat_sub(v_x_222_, v_one_230_);
lean_dec(v_x_222_);
v_x_222_ = v_n_231_;
v_x_223_ = v_s_226_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0___boxed(lean_object* v_c_233_, lean_object* v_x_234_, lean_object* v_x_235_){
_start:
{
lean_object* v_res_236_; 
v_res_236_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(v_c_233_, v_x_234_, v_x_235_);
lean_dec_ref(v_c_233_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(uint8_t v_stringGap_246_, lean_object* v_c_247_, lean_object* v_s_248_){
_start:
{
lean_object* v_toInputContext_249_; lean_object* v_pos_250_; lean_object* v___x_251_; lean_object* v_expected_252_; uint8_t v___x_253_; 
v_toInputContext_249_ = lean_ctor_get(v_c_247_, 0);
v_pos_250_ = lean_ctor_get(v_s_248_, 2);
v___x_251_ = lean_box(0);
v_expected_252_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__1));
v___x_253_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_249_, v_pos_250_);
if (v___x_253_ == 0)
{
lean_object* v_inputString_254_; uint32_t v_curr_255_; uint8_t v___x_256_; 
v_inputString_254_ = lean_ctor_get(v_toInputContext_249_, 0);
v_curr_255_ = lean_string_utf8_get_fast(v_inputString_254_, v_pos_250_);
v___x_256_ = l_Lake_Toml_isEscapeChar(v_curr_255_);
if (v___x_256_ == 0)
{
uint32_t v___x_257_; uint8_t v___x_258_; 
v___x_257_ = 117;
v___x_258_ = lean_uint32_dec_eq(v_curr_255_, v___x_257_);
if (v___x_258_ == 0)
{
uint32_t v___x_259_; uint8_t v___x_260_; 
v___x_259_ = 85;
v___x_260_ = lean_uint32_dec_eq(v_curr_255_, v___x_259_);
if (v___x_260_ == 0)
{
lean_object* v___f_261_; uint8_t v___x_262_; lean_object* v_p_264_; uint32_t v___x_269_; uint8_t v___x_270_; 
v___f_261_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__2));
v___x_262_ = 1;
v___x_269_ = 32;
v___x_270_ = lean_uint32_dec_eq(v_curr_255_, v___x_269_);
if (v___x_270_ == 0)
{
uint32_t v___x_271_; uint8_t v___x_272_; 
v___x_271_ = 9;
v___x_272_ = lean_uint32_dec_eq(v_curr_255_, v___x_271_);
if (v___x_272_ == 0)
{
uint32_t v___x_273_; uint8_t v___x_274_; 
v___x_273_ = 10;
v___x_274_ = lean_uint32_dec_eq(v_curr_255_, v___x_273_);
if (v___x_274_ == 0)
{
uint32_t v___x_275_; uint8_t v___x_276_; 
v___x_275_ = 13;
v___x_276_ = lean_uint32_dec_eq(v_curr_255_, v___x_275_);
if (v___x_276_ == 0)
{
lean_object* v___x_277_; lean_object* v___x_278_; 
lean_dec_ref(v_c_247_);
v___x_277_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__4));
v___x_278_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_248_, v___x_277_, v___x_251_, v___x_262_);
return v___x_278_;
}
else
{
lean_object* v___f_279_; 
v___f_279_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__5));
v_p_264_ = v___f_279_;
goto v___jp_263_;
}
}
else
{
lean_object* v___x_280_; 
v___x_280_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__6));
v_p_264_ = v___x_280_;
goto v___jp_263_;
}
}
else
{
v_p_264_ = v___f_261_;
goto v___jp_263_;
}
}
else
{
v_p_264_ = v___f_261_;
goto v___jp_263_;
}
v___jp_263_:
{
if (v_stringGap_246_ == 0)
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec_ref(v_p_264_);
lean_dec_ref(v_c_247_);
v___x_265_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__3));
v___x_266_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_248_, v___x_265_, v_expected_252_, v___x_262_);
return v___x_266_;
}
else
{
lean_object* v___x_267_; lean_object* v___x_268_; 
lean_inc(v_pos_250_);
v___x_267_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_248_, v_c_247_, v_pos_250_);
lean_dec(v_pos_250_);
v___x_268_ = lean_apply_2(v_p_264_, v_c_247_, v___x_267_);
return v___x_268_;
}
}
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
lean_inc(v_pos_250_);
v___x_281_ = lean_unsigned_to_nat(8u);
v___x_282_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_248_, v_c_247_, v_pos_250_);
lean_dec(v_pos_250_);
v___x_283_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(v_c_247_, v___x_281_, v___x_282_);
lean_dec_ref(v_c_247_);
return v___x_283_;
}
}
else
{
lean_object* v___x_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
lean_inc(v_pos_250_);
v___x_284_ = lean_unsigned_to_nat(4u);
v___x_285_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_248_, v_c_247_, v_pos_250_);
lean_dec(v_pos_250_);
v___x_286_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(v_c_247_, v___x_284_, v___x_285_);
lean_dec_ref(v_c_247_);
return v___x_286_;
}
}
else
{
lean_object* v___x_287_; 
lean_inc(v_pos_250_);
v___x_287_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_248_, v_c_247_, v_pos_250_);
lean_dec(v_pos_250_);
lean_dec_ref(v_c_247_);
return v___x_287_;
}
}
else
{
lean_object* v___x_288_; 
lean_dec_ref(v_c_247_);
v___x_288_ = l_Lean_Parser_ParserState_mkEOIError(v_s_248_, v_expected_252_);
return v___x_288_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___boxed(lean_object* v_stringGap_289_, lean_object* v_c_290_, lean_object* v_s_291_){
_start:
{
uint8_t v_stringGap_boxed_292_; lean_object* v_res_293_; 
v_stringGap_boxed_292_ = lean_unbox(v_stringGap_289_);
v_res_293_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(v_stringGap_boxed_292_, v_c_290_, v_s_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn(lean_object* v_startPos_295_, lean_object* v_c_296_, lean_object* v_s_297_){
_start:
{
lean_object* v_toInputContext_298_; lean_object* v_pos_299_; uint8_t v___x_300_; 
v_toInputContext_298_ = lean_ctor_get(v_c_296_, 0);
v_pos_299_ = lean_ctor_get(v_s_297_, 2);
v___x_300_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_298_, v_pos_299_);
if (v___x_300_ == 0)
{
lean_object* v_inputString_301_; uint32_t v_curr_302_; uint32_t v___x_303_; uint8_t v___x_304_; 
v_inputString_301_ = lean_ctor_get(v_toInputContext_298_, 0);
v_curr_302_ = lean_string_utf8_get_fast(v_inputString_301_, v_pos_299_);
v___x_303_ = 34;
v___x_304_ = lean_uint32_dec_eq(v_curr_302_, v___x_303_);
if (v___x_304_ == 0)
{
uint32_t v___x_305_; uint8_t v___x_306_; 
v___x_305_ = 92;
v___x_306_ = lean_uint32_dec_eq(v_curr_302_, v___x_305_);
if (v___x_306_ == 0)
{
uint8_t v___x_307_; 
v___x_307_ = l_Lake_Toml_isControlChar(v_curr_302_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; 
lean_inc(v_pos_299_);
v___x_308_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_297_, v_c_296_, v_pos_299_);
lean_dec(v_pos_299_);
v_s_297_ = v___x_308_;
goto _start;
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec_ref(v_c_296_);
lean_dec(v_startPos_295_);
v___x_310_ = lean_box(0);
v___x_311_ = l_Lake_Toml_mkUnexpectedCharError(v_s_297_, v_curr_302_, v___x_310_, v___x_307_);
return v___x_311_;
}
}
else
{
lean_object* v___x_312_; lean_object* v_s_313_; lean_object* v_errorMsg_314_; lean_object* v___x_315_; uint8_t v___x_316_; 
lean_inc(v_pos_299_);
v___x_312_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_297_, v_c_296_, v_pos_299_);
lean_dec(v_pos_299_);
lean_inc_ref(v_c_296_);
v_s_313_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(v___x_304_, v_c_296_, v___x_312_);
v_errorMsg_314_ = lean_ctor_get(v_s_313_, 4);
lean_inc(v_errorMsg_314_);
v___x_315_ = lean_box(0);
v___x_316_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_314_, v___x_315_);
if (v___x_316_ == 0)
{
lean_dec_ref(v_c_296_);
lean_dec(v_startPos_295_);
return v_s_313_;
}
else
{
v_s_297_ = v_s_313_;
goto _start;
}
}
}
else
{
lean_object* v___x_318_; 
lean_inc(v_pos_299_);
lean_dec(v_startPos_295_);
v___x_318_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_297_, v_c_296_, v_pos_299_);
lean_dec(v_pos_299_);
lean_dec_ref(v_c_296_);
return v___x_318_;
}
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec_ref(v_c_296_);
v___x_319_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn___closed__0));
v___x_320_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_297_, v___x_319_, v_startPos_295_);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicStringFn(lean_object* v_a_325_, lean_object* v_a_326_){
_start:
{
lean_object* v_pos_327_; uint32_t v___x_328_; lean_object* v___x_329_; lean_object* v_s_330_; lean_object* v_errorMsg_331_; lean_object* v___x_332_; uint8_t v___x_333_; 
v_pos_327_ = lean_ctor_get(v_a_326_, 2);
lean_inc(v_pos_327_);
v___x_328_ = 34;
v___x_329_ = ((lean_object*)(l_Lake_Toml_basicStringFn___closed__1));
v_s_330_ = l_Lake_Toml_chFn(v___x_328_, v___x_329_, v_a_325_, v_a_326_);
v_errorMsg_331_ = lean_ctor_get(v_s_330_, 4);
lean_inc(v_errorMsg_331_);
v___x_332_ = lean_box(0);
v___x_333_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_331_, v___x_332_);
if (v___x_333_ == 0)
{
lean_dec(v_pos_327_);
lean_dec_ref(v_a_325_);
return v_s_330_;
}
else
{
lean_object* v___x_334_; 
v___x_334_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn(v_pos_327_, v_a_325_, v_s_330_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(lean_object* v_startPos_336_, lean_object* v_c_337_, lean_object* v_s_338_){
_start:
{
lean_object* v_toInputContext_339_; lean_object* v_pos_340_; uint8_t v___x_341_; 
v_toInputContext_339_ = lean_ctor_get(v_c_337_, 0);
v_pos_340_ = lean_ctor_get(v_s_338_, 2);
v___x_341_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_339_, v_pos_340_);
if (v___x_341_ == 0)
{
lean_object* v_inputString_342_; uint32_t v_curr_343_; uint32_t v___x_344_; uint8_t v___x_345_; 
v_inputString_342_ = lean_ctor_get(v_toInputContext_339_, 0);
v_curr_343_ = lean_string_utf8_get_fast(v_inputString_342_, v_pos_340_);
v___x_344_ = 39;
v___x_345_ = lean_uint32_dec_eq(v_curr_343_, v___x_344_);
if (v___x_345_ == 0)
{
uint8_t v___x_346_; 
v___x_346_ = l_Lake_Toml_isControlChar(v_curr_343_);
if (v___x_346_ == 0)
{
lean_object* v___x_347_; 
lean_inc(v_pos_340_);
v___x_347_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_338_, v_c_337_, v_pos_340_);
lean_dec(v_pos_340_);
v_s_338_ = v___x_347_;
goto _start;
}
else
{
lean_object* v___x_349_; lean_object* v___x_350_; 
lean_dec(v_startPos_336_);
v___x_349_ = lean_box(0);
v___x_350_ = l_Lake_Toml_mkUnexpectedCharError(v_s_338_, v_curr_343_, v___x_349_, v___x_346_);
return v___x_350_;
}
}
else
{
lean_object* v___x_351_; 
lean_inc(v_pos_340_);
lean_dec(v_startPos_336_);
v___x_351_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_338_, v_c_337_, v_pos_340_);
lean_dec(v_pos_340_);
return v___x_351_;
}
}
else
{
lean_object* v___x_352_; lean_object* v___x_353_; 
v___x_352_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___closed__0));
v___x_353_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_338_, v___x_352_, v_startPos_336_);
return v___x_353_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___boxed(lean_object* v_startPos_354_, lean_object* v_c_355_, lean_object* v_s_356_){
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(v_startPos_354_, v_c_355_, v_s_356_);
lean_dec_ref(v_c_355_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalStringFn(lean_object* v_a_362_, lean_object* v_a_363_){
_start:
{
lean_object* v_pos_364_; uint32_t v___x_365_; lean_object* v___x_366_; lean_object* v_s_367_; lean_object* v_errorMsg_368_; lean_object* v___x_369_; uint8_t v___x_370_; 
v_pos_364_ = lean_ctor_get(v_a_363_, 2);
lean_inc(v_pos_364_);
v___x_365_ = 39;
v___x_366_ = ((lean_object*)(l_Lake_Toml_literalStringFn___closed__1));
v_s_367_ = l_Lake_Toml_chFn(v___x_365_, v___x_366_, v_a_362_, v_a_363_);
v_errorMsg_368_ = lean_ctor_get(v_s_367_, 4);
lean_inc(v_errorMsg_368_);
v___x_369_ = lean_box(0);
v___x_370_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_368_, v___x_369_);
if (v___x_370_ == 0)
{
lean_dec(v_pos_364_);
return v_s_367_;
}
else
{
lean_object* v___x_371_; 
v___x_371_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(v_pos_364_, v_a_362_, v_s_367_);
return v___x_371_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalStringFn___boxed(lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v_res_374_; 
v_res_374_ = l_Lake_Toml_literalStringFn(v_a_372_, v_a_373_);
lean_dec_ref(v_a_372_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(lean_object* v_startPos_377_, lean_object* v_quoteDepth_378_, lean_object* v_c_379_, lean_object* v_s_380_){
_start:
{
lean_object* v_toInputContext_381_; lean_object* v_pos_382_; uint8_t v___x_383_; 
v_toInputContext_381_ = lean_ctor_get(v_c_379_, 0);
v_pos_382_ = lean_ctor_get(v_s_380_, 2);
v___x_383_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_381_, v_pos_382_);
if (v___x_383_ == 0)
{
lean_object* v_inputString_384_; uint8_t v___x_385_; uint32_t v_curr_386_; uint32_t v___x_387_; uint8_t v___x_388_; 
v_inputString_384_ = lean_ctor_get(v_toInputContext_381_, 0);
v___x_385_ = 1;
v_curr_386_ = lean_string_utf8_get_fast(v_inputString_384_, v_pos_382_);
v___x_387_ = 39;
v___x_388_ = lean_uint32_dec_eq(v_curr_386_, v___x_387_);
if (v___x_388_ == 0)
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = lean_unsigned_to_nat(3u);
v___x_390_ = lean_nat_dec_le(v___x_389_, v_quoteDepth_378_);
lean_dec(v_quoteDepth_378_);
if (v___x_390_ == 0)
{
uint32_t v___x_391_; uint8_t v___x_392_; 
v___x_391_ = 10;
v___x_392_ = lean_uint32_dec_eq(v_curr_386_, v___x_391_);
if (v___x_392_ == 0)
{
uint32_t v___x_393_; uint8_t v___x_394_; 
v___x_393_ = 13;
v___x_394_ = lean_uint32_dec_eq(v_curr_386_, v___x_393_);
if (v___x_394_ == 0)
{
uint8_t v___x_395_; 
v___x_395_ = l_Lake_Toml_isControlChar(v_curr_386_);
if (v___x_395_ == 0)
{
lean_object* v___x_396_; lean_object* v___x_397_; 
lean_inc(v_pos_382_);
v___x_396_ = lean_unsigned_to_nat(0u);
v___x_397_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_380_, v_c_379_, v_pos_382_);
lean_dec(v_pos_382_);
v_quoteDepth_378_ = v___x_396_;
v_s_380_ = v___x_397_;
goto _start;
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; 
lean_dec(v_startPos_377_);
v___x_399_ = lean_box(0);
v___x_400_ = l_Lake_Toml_mkUnexpectedCharError(v_s_380_, v_curr_386_, v___x_399_, v___x_385_);
return v___x_400_;
}
}
else
{
lean_object* v___x_401_; lean_object* v_s_402_; lean_object* v_errorMsg_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
lean_inc(v_pos_382_);
v___x_401_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_380_, v_c_379_, v_pos_382_);
lean_dec(v_pos_382_);
v_s_402_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_379_, v___x_401_);
v_errorMsg_403_ = lean_ctor_get(v_s_402_, 4);
lean_inc(v_errorMsg_403_);
v___x_404_ = lean_box(0);
v___x_405_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_403_, v___x_404_);
if (v___x_405_ == 0)
{
lean_dec(v_startPos_377_);
return v_s_402_;
}
else
{
lean_object* v___x_406_; 
v___x_406_ = lean_unsigned_to_nat(0u);
v_quoteDepth_378_ = v___x_406_;
v_s_380_ = v_s_402_;
goto _start;
}
}
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; 
lean_inc(v_pos_382_);
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_380_, v_c_379_, v_pos_382_);
lean_dec(v_pos_382_);
v_quoteDepth_378_ = v___x_408_;
v_s_380_ = v___x_409_;
goto _start;
}
}
else
{
lean_dec(v_startPos_377_);
return v_s_380_;
}
}
else
{
lean_object* v_s_411_; lean_object* v___x_412_; uint8_t v___x_413_; 
lean_inc(v_pos_382_);
v_s_411_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_380_, v_c_379_, v_pos_382_);
lean_dec(v_pos_382_);
v___x_412_ = lean_unsigned_to_nat(5u);
v___x_413_ = lean_nat_dec_le(v___x_412_, v_quoteDepth_378_);
if (v___x_413_ == 0)
{
lean_object* v___x_414_; lean_object* v___x_415_; 
v___x_414_ = lean_unsigned_to_nat(1u);
v___x_415_ = lean_nat_add(v_quoteDepth_378_, v___x_414_);
lean_dec(v_quoteDepth_378_);
v_quoteDepth_378_ = v___x_415_;
v_s_380_ = v_s_411_;
goto _start;
}
else
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec(v_quoteDepth_378_);
lean_dec(v_startPos_377_);
v___x_417_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0));
v___x_418_ = lean_box(0);
v___x_419_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_411_, v___x_417_, v___x_418_, v___x_385_);
return v___x_419_;
}
}
}
else
{
lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = lean_unsigned_to_nat(3u);
v___x_421_ = lean_nat_dec_le(v___x_420_, v_quoteDepth_378_);
lean_dec(v_quoteDepth_378_);
if (v___x_421_ == 0)
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__1));
v___x_423_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_380_, v___x_422_, v_startPos_377_);
return v___x_423_;
}
else
{
lean_dec(v_startPos_377_);
return v_s_380_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___boxed(lean_object* v_startPos_424_, lean_object* v_quoteDepth_425_, lean_object* v_c_426_, lean_object* v_s_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(v_startPos_424_, v_quoteDepth_425_, v_c_426_, v_s_427_);
lean_dec_ref(v_c_426_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0(lean_object* v_c_433_, lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
lean_object* v_zero_436_; uint8_t v_isZero_437_; 
v_zero_436_ = lean_unsigned_to_nat(0u);
v_isZero_437_ = lean_nat_dec_eq(v_x_434_, v_zero_436_);
if (v_isZero_437_ == 1)
{
lean_dec(v_x_434_);
return v_x_435_;
}
else
{
uint32_t v___x_438_; lean_object* v___x_439_; lean_object* v_s_440_; lean_object* v_errorMsg_441_; lean_object* v___x_442_; uint8_t v___x_443_; 
v___x_438_ = 39;
v___x_439_ = ((lean_object*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__1));
v_s_440_ = l_Lake_Toml_chFn(v___x_438_, v___x_439_, v_c_433_, v_x_435_);
v_errorMsg_441_ = lean_ctor_get(v_s_440_, 4);
lean_inc(v_errorMsg_441_);
v___x_442_ = lean_box(0);
v___x_443_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_441_, v___x_442_);
if (v___x_443_ == 0)
{
lean_dec(v_x_434_);
return v_s_440_;
}
else
{
lean_object* v_one_444_; lean_object* v_n_445_; 
v_one_444_ = lean_unsigned_to_nat(1u);
v_n_445_ = lean_nat_sub(v_x_434_, v_one_444_);
lean_dec(v_x_434_);
v_x_434_ = v_n_445_;
v_x_435_ = v_s_440_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___boxed(lean_object* v_c_447_, lean_object* v_x_448_, lean_object* v_x_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0(v_c_447_, v_x_448_, v_x_449_);
lean_dec_ref(v_c_447_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralStringFn___lam__0(lean_object* v___x_451_, lean_object* v___y_452_, lean_object* v___y_453_){
_start:
{
lean_object* v___x_454_; 
v___x_454_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0(v___y_452_, v___x_451_, v___y_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralStringFn___lam__0___boxed(lean_object* v___x_455_, lean_object* v___y_456_, lean_object* v___y_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Lake_Toml_mlLiteralStringFn___lam__0(v___x_455_, v___y_456_, v___y_457_);
lean_dec_ref(v___y_456_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralStringFn(lean_object* v_a_461_, lean_object* v_a_462_){
_start:
{
lean_object* v_pos_463_; lean_object* v___f_464_; lean_object* v_s_465_; lean_object* v_errorMsg_466_; lean_object* v___x_467_; uint8_t v___x_468_; 
v_pos_463_ = lean_ctor_get(v_a_462_, 2);
lean_inc(v_pos_463_);
v___f_464_ = ((lean_object*)(l_Lake_Toml_mlLiteralStringFn___closed__0));
lean_inc_ref(v_a_461_);
v_s_465_ = l_Lean_Parser_atomicFn(v___f_464_, v_a_461_, v_a_462_);
v_errorMsg_466_ = lean_ctor_get(v_s_465_, 4);
lean_inc(v_errorMsg_466_);
v___x_467_ = lean_box(0);
v___x_468_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_466_, v___x_467_);
if (v___x_468_ == 0)
{
lean_dec(v_pos_463_);
lean_dec_ref(v_a_461_);
return v_s_465_;
}
else
{
lean_object* v___x_469_; lean_object* v___x_470_; 
v___x_469_ = lean_unsigned_to_nat(0u);
v___x_470_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(v_pos_463_, v___x_469_, v_a_461_, v_s_465_);
lean_dec_ref(v_a_461_);
return v___x_470_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn(lean_object* v_startPos_472_, lean_object* v_quoteDepth_473_, lean_object* v_c_474_, lean_object* v_s_475_){
_start:
{
lean_object* v_toInputContext_476_; lean_object* v_pos_477_; uint8_t v___x_478_; 
v_toInputContext_476_ = lean_ctor_get(v_c_474_, 0);
v_pos_477_ = lean_ctor_get(v_s_475_, 2);
v___x_478_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_476_, v_pos_477_);
if (v___x_478_ == 0)
{
lean_object* v_inputString_479_; uint8_t v___x_480_; uint32_t v_curr_481_; uint32_t v___x_482_; uint8_t v___x_483_; 
v_inputString_479_ = lean_ctor_get(v_toInputContext_476_, 0);
v___x_480_ = 1;
v_curr_481_ = lean_string_utf8_get_fast(v_inputString_479_, v_pos_477_);
v___x_482_ = 34;
v___x_483_ = lean_uint32_dec_eq(v_curr_481_, v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; uint8_t v___x_485_; 
v___x_484_ = lean_unsigned_to_nat(3u);
v___x_485_ = lean_nat_dec_le(v___x_484_, v_quoteDepth_473_);
lean_dec(v_quoteDepth_473_);
if (v___x_485_ == 0)
{
uint32_t v___x_486_; uint8_t v___x_487_; 
v___x_486_ = 10;
v___x_487_ = lean_uint32_dec_eq(v_curr_481_, v___x_486_);
if (v___x_487_ == 0)
{
uint32_t v___x_488_; uint8_t v___x_489_; 
v___x_488_ = 13;
v___x_489_ = lean_uint32_dec_eq(v_curr_481_, v___x_488_);
if (v___x_489_ == 0)
{
uint32_t v___x_490_; uint8_t v___x_491_; 
v___x_490_ = 92;
v___x_491_ = lean_uint32_dec_eq(v_curr_481_, v___x_490_);
if (v___x_491_ == 0)
{
uint8_t v___x_492_; 
v___x_492_ = l_Lake_Toml_isControlChar(v_curr_481_);
if (v___x_492_ == 0)
{
lean_object* v___x_493_; lean_object* v___x_494_; 
lean_inc(v_pos_477_);
v___x_493_ = lean_unsigned_to_nat(0u);
v___x_494_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_475_, v_c_474_, v_pos_477_);
lean_dec(v_pos_477_);
v_quoteDepth_473_ = v___x_493_;
v_s_475_ = v___x_494_;
goto _start;
}
else
{
lean_object* v___x_496_; lean_object* v___x_497_; 
lean_dec_ref(v_c_474_);
lean_dec(v_startPos_472_);
v___x_496_ = lean_box(0);
v___x_497_ = l_Lake_Toml_mkUnexpectedCharError(v_s_475_, v_curr_481_, v___x_496_, v___x_480_);
return v___x_497_;
}
}
else
{
lean_object* v___x_498_; lean_object* v_s_499_; lean_object* v_errorMsg_500_; lean_object* v___x_501_; uint8_t v___x_502_; 
lean_inc(v_pos_477_);
v___x_498_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_475_, v_c_474_, v_pos_477_);
lean_dec(v_pos_477_);
lean_inc_ref(v_c_474_);
v_s_499_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(v___x_480_, v_c_474_, v___x_498_);
v_errorMsg_500_ = lean_ctor_get(v_s_499_, 4);
lean_inc(v_errorMsg_500_);
v___x_501_ = lean_box(0);
v___x_502_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_500_, v___x_501_);
if (v___x_502_ == 0)
{
lean_dec_ref(v_c_474_);
lean_dec(v_startPos_472_);
return v_s_499_;
}
else
{
lean_object* v___x_503_; 
v___x_503_ = lean_unsigned_to_nat(0u);
v_quoteDepth_473_ = v___x_503_;
v_s_475_ = v_s_499_;
goto _start;
}
}
}
else
{
lean_object* v___x_505_; lean_object* v_s_506_; lean_object* v_errorMsg_507_; lean_object* v___x_508_; uint8_t v___x_509_; 
lean_inc(v_pos_477_);
v___x_505_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_475_, v_c_474_, v_pos_477_);
lean_dec(v_pos_477_);
v_s_506_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_474_, v___x_505_);
v_errorMsg_507_ = lean_ctor_get(v_s_506_, 4);
lean_inc(v_errorMsg_507_);
v___x_508_ = lean_box(0);
v___x_509_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_507_, v___x_508_);
if (v___x_509_ == 0)
{
lean_dec_ref(v_c_474_);
lean_dec(v_startPos_472_);
return v_s_506_;
}
else
{
lean_object* v___x_510_; 
v___x_510_ = lean_unsigned_to_nat(0u);
v_quoteDepth_473_ = v___x_510_;
v_s_475_ = v_s_506_;
goto _start;
}
}
}
else
{
lean_object* v___x_512_; lean_object* v___x_513_; 
lean_inc(v_pos_477_);
v___x_512_ = lean_unsigned_to_nat(0u);
v___x_513_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_475_, v_c_474_, v_pos_477_);
lean_dec(v_pos_477_);
v_quoteDepth_473_ = v___x_512_;
v_s_475_ = v___x_513_;
goto _start;
}
}
else
{
lean_dec_ref(v_c_474_);
lean_dec(v_startPos_472_);
return v_s_475_;
}
}
else
{
lean_object* v_s_515_; lean_object* v___x_516_; uint8_t v___x_517_; 
lean_inc(v_pos_477_);
v_s_515_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_475_, v_c_474_, v_pos_477_);
lean_dec(v_pos_477_);
v___x_516_ = lean_unsigned_to_nat(5u);
v___x_517_ = lean_nat_dec_le(v___x_516_, v_quoteDepth_473_);
if (v___x_517_ == 0)
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_unsigned_to_nat(1u);
v___x_519_ = lean_nat_add(v_quoteDepth_473_, v___x_518_);
lean_dec(v_quoteDepth_473_);
v_quoteDepth_473_ = v___x_519_;
v_s_475_ = v_s_515_;
goto _start;
}
else
{
lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec_ref(v_c_474_);
lean_dec(v_quoteDepth_473_);
lean_dec(v_startPos_472_);
v___x_521_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0));
v___x_522_ = lean_box(0);
v___x_523_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_515_, v___x_521_, v___x_522_, v___x_480_);
return v___x_523_;
}
}
}
else
{
lean_object* v___x_524_; uint8_t v___x_525_; 
lean_dec_ref(v_c_474_);
v___x_524_ = lean_unsigned_to_nat(3u);
v___x_525_ = lean_nat_dec_le(v___x_524_, v_quoteDepth_473_);
lean_dec(v_quoteDepth_473_);
if (v___x_525_ == 0)
{
lean_object* v___x_526_; lean_object* v___x_527_; 
v___x_526_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn___closed__0));
v___x_527_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_475_, v___x_526_, v_startPos_472_);
return v___x_527_;
}
else
{
lean_dec(v_startPos_472_);
return v_s_475_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0(lean_object* v_c_532_, lean_object* v_x_533_, lean_object* v_x_534_){
_start:
{
lean_object* v_zero_535_; uint8_t v_isZero_536_; 
v_zero_535_ = lean_unsigned_to_nat(0u);
v_isZero_536_ = lean_nat_dec_eq(v_x_533_, v_zero_535_);
if (v_isZero_536_ == 1)
{
lean_dec(v_x_533_);
return v_x_534_;
}
else
{
uint32_t v___x_537_; lean_object* v___x_538_; lean_object* v_s_539_; lean_object* v_errorMsg_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_537_ = 34;
v___x_538_ = ((lean_object*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__1));
v_s_539_ = l_Lake_Toml_chFn(v___x_537_, v___x_538_, v_c_532_, v_x_534_);
v_errorMsg_540_ = lean_ctor_get(v_s_539_, 4);
lean_inc(v_errorMsg_540_);
v___x_541_ = lean_box(0);
v___x_542_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_540_, v___x_541_);
if (v___x_542_ == 0)
{
lean_dec(v_x_533_);
return v_s_539_;
}
else
{
lean_object* v_one_543_; lean_object* v_n_544_; 
v_one_543_ = lean_unsigned_to_nat(1u);
v_n_544_ = lean_nat_sub(v_x_533_, v_one_543_);
lean_dec(v_x_533_);
v_x_533_ = v_n_544_;
v_x_534_ = v_s_539_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___boxed(lean_object* v_c_546_, lean_object* v_x_547_, lean_object* v_x_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0(v_c_546_, v_x_547_, v_x_548_);
lean_dec_ref(v_c_546_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicStringFn___lam__0(lean_object* v___x_550_, lean_object* v___y_551_, lean_object* v___y_552_){
_start:
{
lean_object* v___x_553_; 
v___x_553_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0(v___y_551_, v___x_550_, v___y_552_);
return v___x_553_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicStringFn___lam__0___boxed(lean_object* v___x_554_, lean_object* v___y_555_, lean_object* v___y_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Lake_Toml_mlBasicStringFn___lam__0(v___x_554_, v___y_555_, v___y_556_);
lean_dec_ref(v___y_555_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicStringFn(lean_object* v_a_560_, lean_object* v_a_561_){
_start:
{
lean_object* v_pos_562_; lean_object* v___f_563_; lean_object* v_s_564_; lean_object* v_errorMsg_565_; lean_object* v___x_566_; uint8_t v___x_567_; 
v_pos_562_ = lean_ctor_get(v_a_561_, 2);
lean_inc(v_pos_562_);
v___f_563_ = ((lean_object*)(l_Lake_Toml_mlBasicStringFn___closed__0));
lean_inc_ref(v_a_560_);
v_s_564_ = l_Lean_Parser_atomicFn(v___f_563_, v_a_560_, v_a_561_);
v_errorMsg_565_ = lean_ctor_get(v_s_564_, 4);
lean_inc(v_errorMsg_565_);
v___x_566_ = lean_box(0);
v___x_567_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_565_, v___x_566_);
if (v___x_567_ == 0)
{
lean_dec(v_pos_562_);
lean_dec_ref(v_a_560_);
return v_s_564_;
}
else
{
lean_object* v___x_568_; lean_object* v___x_569_; 
v___x_568_ = lean_unsigned_to_nat(0u);
v___x_569_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn(v_pos_562_, v___x_568_, v_a_560_, v_s_564_);
return v___x_569_;
}
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4(void){
_start:
{
uint32_t v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_576_ = 58;
v___x_577_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_578_ = lean_string_push(v___x_577_, v___x_576_);
return v___x_578_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5(void){
_start:
{
lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_579_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4, &l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4);
v___x_580_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_581_ = lean_string_append(v___x_580_, v___x_579_);
return v___x_581_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6(void){
_start:
{
lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; 
v___x_582_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_583_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5);
v___x_584_ = lean_string_append(v___x_583_, v___x_582_);
return v___x_584_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7(void){
_start:
{
lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_585_ = lean_box(0);
v___x_586_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6, &l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6);
v___x_587_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_587_, 0, v___x_586_);
lean_ctor_set(v___x_587_, 1, v___x_585_);
return v___x_587_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(lean_object* v_a_592_, lean_object* v_a_593_){
_start:
{
lean_object* v___x_594_; lean_object* v_s_595_; lean_object* v_errorMsg_596_; lean_object* v___x_597_; uint8_t v___x_598_; 
v___x_594_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__1));
v_s_595_ = l_Lake_Toml_digitPairFn(v___x_594_, v_a_592_, v_a_593_);
v_errorMsg_596_ = lean_ctor_get(v_s_595_, 4);
lean_inc(v_errorMsg_596_);
v___x_597_ = lean_box(0);
v___x_598_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_596_, v___x_597_);
if (v___x_598_ == 0)
{
return v_s_595_;
}
else
{
uint32_t v___x_599_; lean_object* v___x_600_; lean_object* v_s_601_; lean_object* v_errorMsg_602_; uint8_t v___x_603_; 
v___x_599_ = 58;
v___x_600_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7, &l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7);
v_s_601_ = l_Lake_Toml_chFn(v___x_599_, v___x_600_, v_a_592_, v_s_595_);
v_errorMsg_602_ = lean_ctor_get(v_s_601_, 4);
lean_inc(v_errorMsg_602_);
v___x_603_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_602_, v___x_597_);
if (v___x_603_ == 0)
{
return v_s_601_;
}
else
{
lean_object* v___x_604_; lean_object* v___x_605_; 
v___x_604_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9));
v___x_605_ = l_Lake_Toml_digitPairFn(v___x_604_, v_a_592_, v_s_601_);
return v___x_605_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___boxed(lean_object* v_a_606_, lean_object* v_a_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(v_a_606_, v_a_607_);
lean_dec_ref(v_a_606_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn(uint8_t v_allowOffset_610_, uint32_t v_curr_611_, lean_object* v_nextPos_612_, lean_object* v_c_613_, lean_object* v_s_614_){
_start:
{
uint8_t v___y_616_; uint8_t v___y_617_; uint8_t v___y_624_; uint32_t v___x_634_; uint8_t v___x_635_; 
v___x_634_ = 90;
v___x_635_ = lean_uint32_dec_eq(v_curr_611_, v___x_634_);
if (v___x_635_ == 0)
{
uint32_t v___x_636_; uint8_t v___x_637_; 
v___x_636_ = 122;
v___x_637_ = lean_uint32_dec_eq(v_curr_611_, v___x_636_);
v___y_624_ = v___x_637_;
goto v___jp_623_;
}
else
{
v___y_624_ = v___x_635_;
goto v___jp_623_;
}
v___jp_615_:
{
if (v___y_617_ == 0)
{
lean_dec(v_nextPos_612_);
return v_s_614_;
}
else
{
if (v_allowOffset_610_ == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; 
lean_dec(v_nextPos_612_);
v___x_618_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_619_ = lean_box(0);
v___x_620_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_614_, v___x_618_, v___x_619_, v___y_616_);
return v___x_620_;
}
else
{
lean_object* v___x_621_; lean_object* v___x_622_; 
v___x_621_ = l_Lean_Parser_ParserState_setPos(v_s_614_, v_nextPos_612_);
v___x_622_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(v_c_613_, v___x_621_);
return v___x_622_;
}
}
}
v___jp_623_:
{
uint8_t v___x_625_; 
v___x_625_ = 1;
if (v___y_624_ == 0)
{
uint32_t v___x_626_; uint8_t v___x_627_; 
v___x_626_ = 43;
v___x_627_ = lean_uint32_dec_eq(v_curr_611_, v___x_626_);
if (v___x_627_ == 0)
{
uint32_t v___x_628_; uint8_t v___x_629_; 
v___x_628_ = 45;
v___x_629_ = lean_uint32_dec_eq(v_curr_611_, v___x_628_);
v___y_616_ = v___x_625_;
v___y_617_ = v___x_629_;
goto v___jp_615_;
}
else
{
v___y_616_ = v___x_625_;
v___y_617_ = v___x_627_;
goto v___jp_615_;
}
}
else
{
if (v_allowOffset_610_ == 0)
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
lean_dec(v_nextPos_612_);
v___x_630_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_631_ = lean_box(0);
v___x_632_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_614_, v___x_630_, v___x_631_, v___x_625_);
return v___x_632_;
}
else
{
lean_object* v___x_633_; 
v___x_633_ = l_Lean_Parser_ParserState_setPos(v_s_614_, v_nextPos_612_);
return v___x_633_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___boxed(lean_object* v_allowOffset_638_, lean_object* v_curr_639_, lean_object* v_nextPos_640_, lean_object* v_c_641_, lean_object* v_s_642_){
_start:
{
uint8_t v_allowOffset_boxed_643_; uint32_t v_curr_boxed_644_; lean_object* v_res_645_; 
v_allowOffset_boxed_643_ = lean_unbox(v_allowOffset_638_);
v_curr_boxed_644_ = lean_unbox_uint32(v_curr_639_);
lean_dec(v_curr_639_);
v_res_645_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn(v_allowOffset_boxed_643_, v_curr_boxed_644_, v_nextPos_640_, v_c_641_, v_s_642_);
lean_dec_ref(v_c_641_);
return v_res_645_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0(uint32_t v_x_646_){
_start:
{
uint32_t v___x_647_; uint8_t v___x_648_; 
v___x_647_ = 48;
v___x_648_ = lean_uint32_dec_le(v___x_647_, v_x_646_);
if (v___x_648_ == 0)
{
return v___x_648_;
}
else
{
uint32_t v___x_649_; uint8_t v___x_650_; 
v___x_649_ = 57;
v___x_650_ = lean_uint32_dec_le(v_x_646_, v___x_649_);
return v___x_650_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0___boxed(lean_object* v_x_651_){
_start:
{
uint32_t v_x_512__boxed_652_; uint8_t v_res_653_; lean_object* v_r_654_; 
v_x_512__boxed_652_ = lean_unbox_uint32(v_x_651_);
lean_dec(v_x_651_);
v_res_653_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0(v_x_512__boxed_652_);
v_r_654_ = lean_box(v_res_653_);
return v_r_654_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(uint8_t v_allowOffset_660_, lean_object* v_c_661_, lean_object* v_s_662_){
_start:
{
lean_object* v_toInputContext_663_; lean_object* v_pos_664_; uint8_t v___x_665_; 
v_toInputContext_663_ = lean_ctor_get(v_c_661_, 0);
v_pos_664_ = lean_ctor_get(v_s_662_, 2);
v___x_665_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_663_, v_pos_664_);
if (v___x_665_ == 0)
{
lean_object* v_inputString_666_; uint32_t v_curr_667_; uint32_t v___x_668_; uint8_t v___x_669_; 
v_inputString_666_ = lean_ctor_get(v_toInputContext_663_, 0);
v_curr_667_ = lean_string_utf8_get_fast(v_inputString_666_, v_pos_664_);
v___x_668_ = 46;
v___x_669_ = lean_uint32_dec_eq(v_curr_667_, v___x_668_);
if (v___x_669_ == 0)
{
lean_object* v___x_670_; uint8_t v___y_672_; uint8_t v___y_673_; uint8_t v___y_680_; uint32_t v___x_690_; uint8_t v___x_691_; 
v___x_670_ = lean_string_utf8_next_fast(v_inputString_666_, v_pos_664_);
v___x_690_ = 90;
v___x_691_ = lean_uint32_dec_eq(v_curr_667_, v___x_690_);
if (v___x_691_ == 0)
{
uint32_t v___x_692_; uint8_t v___x_693_; 
v___x_692_ = 122;
v___x_693_ = lean_uint32_dec_eq(v_curr_667_, v___x_692_);
v___y_680_ = v___x_693_;
goto v___jp_679_;
}
else
{
v___y_680_ = v___x_691_;
goto v___jp_679_;
}
v___jp_671_:
{
if (v___y_673_ == 0)
{
return v_s_662_;
}
else
{
if (v_allowOffset_660_ == 0)
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_675_ = lean_box(0);
v___x_676_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_662_, v___x_674_, v___x_675_, v___y_672_);
return v___x_676_;
}
else
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = l_Lean_Parser_ParserState_setPos(v_s_662_, v___x_670_);
v___x_678_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(v_c_661_, v___x_677_);
return v___x_678_;
}
}
}
v___jp_679_:
{
uint8_t v___x_681_; 
v___x_681_ = 1;
if (v___y_680_ == 0)
{
uint32_t v___x_682_; uint8_t v___x_683_; 
v___x_682_ = 43;
v___x_683_ = lean_uint32_dec_eq(v_curr_667_, v___x_682_);
if (v___x_683_ == 0)
{
uint32_t v___x_684_; uint8_t v___x_685_; 
v___x_684_ = 45;
v___x_685_ = lean_uint32_dec_eq(v_curr_667_, v___x_684_);
v___y_672_ = v___x_681_;
v___y_673_ = v___x_685_;
goto v___jp_671_;
}
else
{
v___y_672_ = v___x_681_;
v___y_673_ = v___x_683_;
goto v___jp_671_;
}
}
else
{
if (v_allowOffset_660_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_686_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_687_ = lean_box(0);
v___x_688_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_662_, v___x_686_, v___x_687_, v___x_681_);
return v___x_688_;
}
else
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_Parser_ParserState_setPos(v_s_662_, v___x_670_);
return v___x_689_;
}
}
}
}
else
{
lean_object* v___f_694_; lean_object* v_s_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v_s_698_; lean_object* v_pos_699_; lean_object* v_errorMsg_700_; lean_object* v___x_701_; uint8_t v___x_702_; 
lean_inc(v_pos_664_);
v___f_694_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0));
v_s_695_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_662_, v_c_661_, v_pos_664_);
lean_dec(v_pos_664_);
v___x_696_ = lean_box(0);
v___x_697_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__2));
v_s_698_ = l_Lake_Toml_takeWhile1Fn(v___f_694_, v___x_697_, v_c_661_, v_s_695_);
v_pos_699_ = lean_ctor_get(v_s_698_, 2);
lean_inc(v_pos_699_);
v_errorMsg_700_ = lean_ctor_get(v_s_698_, 4);
lean_inc(v_errorMsg_700_);
v___x_701_ = lean_box(0);
v___x_702_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_700_, v___x_701_);
if (v___x_702_ == 0)
{
lean_dec(v_pos_699_);
return v_s_698_;
}
else
{
if (v___x_665_ == 0)
{
uint8_t v___x_703_; 
v___x_703_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_663_, v_pos_699_);
if (v___x_703_ == 0)
{
uint32_t v___x_704_; lean_object* v___x_705_; uint8_t v___y_707_; uint8_t v___y_713_; uint32_t v___x_721_; uint8_t v___x_722_; 
v___x_704_ = lean_string_utf8_get_fast(v_inputString_666_, v_pos_699_);
v___x_705_ = lean_string_utf8_next_fast(v_inputString_666_, v_pos_699_);
lean_dec(v_pos_699_);
v___x_721_ = 90;
v___x_722_ = lean_uint32_dec_eq(v___x_704_, v___x_721_);
if (v___x_722_ == 0)
{
uint32_t v___x_723_; uint8_t v___x_724_; 
v___x_723_ = 122;
v___x_724_ = lean_uint32_dec_eq(v___x_704_, v___x_723_);
v___y_713_ = v___x_724_;
goto v___jp_712_;
}
else
{
v___y_713_ = v___x_722_;
goto v___jp_712_;
}
v___jp_706_:
{
if (v___y_707_ == 0)
{
return v_s_698_;
}
else
{
if (v_allowOffset_660_ == 0)
{
lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_708_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_709_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_698_, v___x_708_, v___x_696_, v___x_702_);
return v___x_709_;
}
else
{
lean_object* v___x_710_; lean_object* v___x_711_; 
v___x_710_ = l_Lean_Parser_ParserState_setPos(v_s_698_, v___x_705_);
v___x_711_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(v_c_661_, v___x_710_);
return v___x_711_;
}
}
}
v___jp_712_:
{
if (v___y_713_ == 0)
{
uint32_t v___x_714_; uint8_t v___x_715_; 
v___x_714_ = 43;
v___x_715_ = lean_uint32_dec_eq(v___x_704_, v___x_714_);
if (v___x_715_ == 0)
{
uint32_t v___x_716_; uint8_t v___x_717_; 
v___x_716_ = 45;
v___x_717_ = lean_uint32_dec_eq(v___x_704_, v___x_716_);
v___y_707_ = v___x_717_;
goto v___jp_706_;
}
else
{
v___y_707_ = v___x_715_;
goto v___jp_706_;
}
}
else
{
if (v_allowOffset_660_ == 0)
{
lean_object* v___x_718_; lean_object* v___x_719_; 
v___x_718_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_719_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_698_, v___x_718_, v___x_696_, v___x_702_);
return v___x_719_;
}
else
{
lean_object* v___x_720_; 
v___x_720_ = l_Lean_Parser_ParserState_setPos(v_s_698_, v___x_705_);
return v___x_720_;
}
}
}
}
else
{
lean_dec(v_pos_699_);
return v_s_698_;
}
}
else
{
lean_dec(v_pos_699_);
return v_s_698_;
}
}
}
}
else
{
return v_s_662_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___boxed(lean_object* v_allowOffset_725_, lean_object* v_c_726_, lean_object* v_s_727_){
_start:
{
uint8_t v_allowOffset_boxed_728_; lean_object* v_res_729_; 
v_allowOffset_boxed_728_ = lean_unbox(v_allowOffset_725_);
v_res_729_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(v_allowOffset_boxed_728_, v_c_726_, v_s_727_);
lean_dec_ref(v_c_726_);
return v_res_729_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(uint8_t v_allowOffset_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v___x_737_; lean_object* v_s_738_; lean_object* v_errorMsg_739_; lean_object* v___x_740_; uint8_t v___x_741_; 
v___x_737_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9));
v_s_738_ = l_Lake_Toml_digitPairFn(v___x_737_, v_a_735_, v_a_736_);
v_errorMsg_739_ = lean_ctor_get(v_s_738_, 4);
lean_inc(v_errorMsg_739_);
v___x_740_ = lean_box(0);
v___x_741_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_739_, v___x_740_);
if (v___x_741_ == 0)
{
return v_s_738_;
}
else
{
uint32_t v___x_742_; lean_object* v___x_743_; lean_object* v_s_744_; lean_object* v_errorMsg_745_; uint8_t v___x_746_; 
v___x_742_ = 58;
v___x_743_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7, &l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7);
v_s_744_ = l_Lake_Toml_chFn(v___x_742_, v___x_743_, v_a_735_, v_s_738_);
v_errorMsg_745_ = lean_ctor_get(v_s_744_, 4);
lean_inc(v_errorMsg_745_);
v___x_746_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_745_, v___x_740_);
if (v___x_746_ == 0)
{
return v_s_744_;
}
else
{
lean_object* v___x_747_; lean_object* v_s_748_; lean_object* v_errorMsg_749_; uint8_t v___x_750_; 
v___x_747_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__1));
v_s_748_ = l_Lake_Toml_digitPairFn(v___x_747_, v_a_735_, v_s_744_);
v_errorMsg_749_ = lean_ctor_get(v_s_748_, 4);
lean_inc(v_errorMsg_749_);
v___x_750_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_749_, v___x_740_);
if (v___x_750_ == 0)
{
return v_s_748_;
}
else
{
lean_object* v___x_751_; 
v___x_751_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(v_allowOffset_734_, v_a_735_, v_s_748_);
return v___x_751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___boxed(lean_object* v_allowOffset_752_, lean_object* v_a_753_, lean_object* v_a_754_){
_start:
{
uint8_t v_allowOffset_boxed_755_; lean_object* v_res_756_; 
v_allowOffset_boxed_755_ = lean_unbox(v_allowOffset_752_);
v_res_756_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(v_allowOffset_boxed_755_, v_a_753_, v_a_754_);
lean_dec_ref(v_a_753_);
return v_res_756_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_timeFn(uint8_t v_allowOffset_761_, lean_object* v_a_762_, lean_object* v_a_763_){
_start:
{
lean_object* v___x_764_; lean_object* v_s_765_; lean_object* v_errorMsg_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v___x_764_ = ((lean_object*)(l_Lake_Toml_timeFn___closed__1));
v_s_765_ = l_Lake_Toml_digitPairFn(v___x_764_, v_a_762_, v_a_763_);
v_errorMsg_766_ = lean_ctor_get(v_s_765_, 4);
lean_inc(v_errorMsg_766_);
v___x_767_ = lean_box(0);
v___x_768_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_766_, v___x_767_);
if (v___x_768_ == 0)
{
return v_s_765_;
}
else
{
uint32_t v___x_769_; lean_object* v___x_770_; lean_object* v_s_771_; lean_object* v_errorMsg_772_; uint8_t v___x_773_; 
v___x_769_ = 58;
v___x_770_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7, &l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7);
v_s_771_ = l_Lake_Toml_chFn(v___x_769_, v___x_770_, v_a_762_, v_s_765_);
v_errorMsg_772_ = lean_ctor_get(v_s_771_, 4);
lean_inc(v_errorMsg_772_);
v___x_773_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_772_, v___x_767_);
if (v___x_773_ == 0)
{
return v_s_771_;
}
else
{
lean_object* v___x_774_; 
v___x_774_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(v_allowOffset_761_, v_a_762_, v_s_771_);
return v___x_774_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_timeFn___boxed(lean_object* v_allowOffset_775_, lean_object* v_a_776_, lean_object* v_a_777_){
_start:
{
uint8_t v_allowOffset_boxed_778_; lean_object* v_res_779_; 
v_allowOffset_boxed_778_ = lean_unbox(v_allowOffset_775_);
v_res_779_ = l_Lake_Toml_timeFn(v_allowOffset_boxed_778_, v_a_776_, v_a_777_);
lean_dec_ref(v_a_776_);
return v_res_779_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(lean_object* v_c_780_, lean_object* v_s_781_){
_start:
{
lean_object* v_pos_782_; lean_object* v_toInputContext_783_; uint8_t v___x_784_; 
v_pos_782_ = lean_ctor_get(v_s_781_, 2);
v_toInputContext_783_ = lean_ctor_get(v_c_780_, 0);
v___x_784_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_783_, v_pos_782_);
if (v___x_784_ == 0)
{
lean_object* v_inputString_785_; uint8_t v___x_786_; uint32_t v_curr_790_; uint32_t v___x_791_; uint8_t v___x_792_; 
v_inputString_785_ = lean_ctor_get(v_toInputContext_783_, 0);
v___x_786_ = 1;
v_curr_790_ = lean_string_utf8_get_fast(v_inputString_785_, v_pos_782_);
v___x_791_ = 84;
v___x_792_ = lean_uint32_dec_eq(v_curr_790_, v___x_791_);
if (v___x_792_ == 0)
{
uint32_t v___x_793_; uint8_t v___x_794_; 
v___x_793_ = 116;
v___x_794_ = lean_uint32_dec_eq(v_curr_790_, v___x_793_);
if (v___x_794_ == 0)
{
uint32_t v___x_795_; uint8_t v___x_796_; 
v___x_795_ = 32;
v___x_796_ = lean_uint32_dec_eq(v_curr_790_, v___x_795_);
if (v___x_796_ == 0)
{
return v_s_781_;
}
else
{
lean_object* v_tPos_797_; lean_object* v___x_798_; lean_object* v_s_799_; lean_object* v_errorMsg_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
lean_inc(v_pos_782_);
v_tPos_797_ = lean_string_utf8_next_fast(v_inputString_785_, v_pos_782_);
v___x_798_ = l_Lean_Parser_ParserState_setPos(v_s_781_, v_tPos_797_);
v_s_799_ = l_Lake_Toml_timeFn(v___x_786_, v_c_780_, v___x_798_);
v_errorMsg_807_ = lean_ctor_get(v_s_799_, 4);
lean_inc(v_errorMsg_807_);
v___x_808_ = lean_box(0);
v___x_809_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_807_, v___x_808_);
if (v___x_809_ == 0)
{
goto v___jp_800_;
}
else
{
if (v___x_794_ == 0)
{
lean_dec(v_pos_782_);
return v_s_799_;
}
else
{
goto v___jp_800_;
}
}
v___jp_800_:
{
lean_object* v_pos_801_; uint8_t v___x_802_; 
v_pos_801_ = lean_ctor_get(v_s_799_, 2);
lean_inc(v_pos_801_);
v___x_802_ = lean_nat_dec_eq(v_pos_801_, v_tPos_797_);
lean_dec(v_pos_801_);
if (v___x_802_ == 0)
{
lean_dec(v_pos_782_);
return v_s_799_;
}
else
{
lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; 
v___x_803_ = l_Lean_Parser_ParserState_stackSize(v_s_799_);
v___x_804_ = lean_unsigned_to_nat(1u);
v___x_805_ = lean_nat_sub(v___x_803_, v___x_804_);
lean_dec(v___x_803_);
v___x_806_ = l_Lean_Parser_ParserState_restore(v_s_799_, v___x_805_, v_pos_782_);
lean_dec(v___x_805_);
return v___x_806_;
}
}
}
}
else
{
lean_inc(v_pos_782_);
goto v___jp_787_;
}
}
else
{
lean_inc(v_pos_782_);
goto v___jp_787_;
}
v___jp_787_:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_781_, v_c_780_, v_pos_782_);
lean_dec(v_pos_782_);
v___x_789_ = l_Lake_Toml_timeFn(v___x_786_, v_c_780_, v___x_788_);
return v___x_789_;
}
}
else
{
return v_s_781_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn___boxed(lean_object* v_c_810_, lean_object* v_s_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(v_c_810_, v_s_811_);
lean_dec_ref(v_c_810_);
return v_res_812_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2(void){
_start:
{
uint32_t v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; 
v___x_817_ = 45;
v___x_818_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_819_ = lean_string_push(v___x_818_, v___x_817_);
return v___x_819_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3(void){
_start:
{
lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_820_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2, &l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2);
v___x_821_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_822_ = lean_string_append(v___x_821_, v___x_820_);
return v___x_822_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4(void){
_start:
{
lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v___x_823_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_824_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3, &l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3);
v___x_825_ = lean_string_append(v___x_824_, v___x_823_);
return v___x_825_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5(void){
_start:
{
lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; 
v___x_826_ = lean_box(0);
v___x_827_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4, &l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4);
v___x_828_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_827_);
lean_ctor_set(v___x_828_, 1, v___x_826_);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
lean_object* v___x_835_; lean_object* v_s_836_; lean_object* v_errorMsg_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v___x_835_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__1));
v_s_836_ = l_Lake_Toml_digitPairFn(v___x_835_, v_a_833_, v_a_834_);
v_errorMsg_837_ = lean_ctor_get(v_s_836_, 4);
lean_inc(v_errorMsg_837_);
v___x_838_ = lean_box(0);
v___x_839_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_837_, v___x_838_);
if (v___x_839_ == 0)
{
return v_s_836_;
}
else
{
uint32_t v___x_840_; lean_object* v___x_841_; lean_object* v_s_842_; lean_object* v_errorMsg_843_; uint8_t v___x_844_; 
v___x_840_ = 45;
v___x_841_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5);
v_s_842_ = l_Lake_Toml_chFn(v___x_840_, v___x_841_, v_a_833_, v_s_836_);
v_errorMsg_843_ = lean_ctor_get(v_s_842_, 4);
lean_inc(v_errorMsg_843_);
v___x_844_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_843_, v___x_838_);
if (v___x_844_ == 0)
{
return v_s_842_;
}
else
{
lean_object* v___x_845_; lean_object* v_s_846_; lean_object* v_errorMsg_847_; uint8_t v___x_848_; 
v___x_845_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__7));
v_s_846_ = l_Lake_Toml_digitPairFn(v___x_845_, v_a_833_, v_s_842_);
v_errorMsg_847_ = lean_ctor_get(v_s_846_, 4);
lean_inc(v_errorMsg_847_);
v___x_848_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_847_, v___x_838_);
if (v___x_848_ == 0)
{
return v_s_846_;
}
else
{
lean_object* v___x_849_; 
v___x_849_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(v_a_833_, v_s_846_);
return v___x_849_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___boxed(lean_object* v_a_850_, lean_object* v_a_851_){
_start:
{
lean_object* v_res_852_; 
v_res_852_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(v_a_850_, v_a_851_);
lean_dec_ref(v_a_850_);
return v_res_852_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0(lean_object* v_c_857_, lean_object* v_x_858_, lean_object* v_x_859_){
_start:
{
lean_object* v_zero_860_; uint8_t v_isZero_861_; 
v_zero_860_ = lean_unsigned_to_nat(0u);
v_isZero_861_ = lean_nat_dec_eq(v_x_858_, v_zero_860_);
if (v_isZero_861_ == 1)
{
lean_dec(v_x_858_);
return v_x_859_;
}
else
{
lean_object* v___x_862_; lean_object* v_s_863_; lean_object* v_errorMsg_864_; lean_object* v___x_865_; uint8_t v___x_866_; 
v___x_862_ = ((lean_object*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__1));
v_s_863_ = l_Lake_Toml_digitFn(v___x_862_, v_c_857_, v_x_859_);
v_errorMsg_864_ = lean_ctor_get(v_s_863_, 4);
lean_inc(v_errorMsg_864_);
v___x_865_ = lean_box(0);
v___x_866_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_864_, v___x_865_);
if (v___x_866_ == 0)
{
lean_dec(v_x_858_);
return v_s_863_;
}
else
{
lean_object* v_one_867_; lean_object* v_n_868_; 
v_one_867_ = lean_unsigned_to_nat(1u);
v_n_868_ = lean_nat_sub(v_x_858_, v_one_867_);
lean_dec(v_x_858_);
v_x_858_ = v_n_868_;
v_x_859_ = v_s_863_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___boxed(lean_object* v_c_870_, lean_object* v_x_871_, lean_object* v_x_872_){
_start:
{
lean_object* v_res_873_; 
v_res_873_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0(v_c_870_, v_x_871_, v_x_872_);
lean_dec_ref(v_c_870_);
return v_res_873_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dateTimeFn(lean_object* v_a_874_, lean_object* v_a_875_){
_start:
{
lean_object* v___x_876_; lean_object* v_s_877_; lean_object* v_errorMsg_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v___x_876_ = lean_unsigned_to_nat(4u);
v_s_877_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0(v_a_874_, v___x_876_, v_a_875_);
v_errorMsg_878_ = lean_ctor_get(v_s_877_, 4);
lean_inc(v_errorMsg_878_);
v___x_879_ = lean_box(0);
v___x_880_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_878_, v___x_879_);
if (v___x_880_ == 0)
{
return v_s_877_;
}
else
{
uint32_t v___x_881_; lean_object* v___x_882_; lean_object* v_s_883_; lean_object* v_errorMsg_884_; uint8_t v___x_885_; 
v___x_881_ = 45;
v___x_882_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5);
v_s_883_ = l_Lake_Toml_chFn(v___x_881_, v___x_882_, v_a_874_, v_s_877_);
v_errorMsg_884_ = lean_ctor_get(v_s_883_, 4);
lean_inc(v_errorMsg_884_);
v___x_885_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_884_, v___x_879_);
if (v___x_885_ == 0)
{
return v_s_883_;
}
else
{
lean_object* v___x_886_; 
v___x_886_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(v_a_874_, v_s_883_);
return v___x_886_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dateTimeFn___boxed(lean_object* v_a_887_, lean_object* v_a_888_){
_start:
{
lean_object* v_res_889_; 
v_res_889_ = l_Lake_Toml_dateTimeFn(v_a_887_, v_a_888_);
lean_dec_ref(v_a_887_);
return v_res_889_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(lean_object* v_c_894_, lean_object* v_s_895_){
_start:
{
lean_object* v_toInputContext_896_; lean_object* v_pos_897_; lean_object* v_expected_898_; uint8_t v___x_899_; 
v_toInputContext_896_ = lean_ctor_get(v_c_894_, 0);
v_pos_897_ = lean_ctor_get(v_s_895_, 2);
v_expected_898_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__1));
v___x_899_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_896_, v_pos_897_);
if (v___x_899_ == 0)
{
lean_object* v_inputString_900_; lean_object* v___f_901_; uint32_t v_curr_906_; uint32_t v___x_907_; uint8_t v___x_908_; 
v_inputString_900_ = lean_ctor_get(v_toInputContext_896_, 0);
v___f_901_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0));
v_curr_906_ = lean_string_utf8_get_fast(v_inputString_900_, v_pos_897_);
v___x_907_ = 45;
v___x_908_ = lean_uint32_dec_eq(v_curr_906_, v___x_907_);
if (v___x_908_ == 0)
{
uint32_t v___x_909_; uint8_t v___x_910_; 
v___x_909_ = 43;
v___x_910_ = lean_uint32_dec_eq(v_curr_906_, v___x_909_);
if (v___x_910_ == 0)
{
uint8_t v___x_911_; uint8_t v___y_913_; uint32_t v___x_918_; uint8_t v___x_919_; 
v___x_911_ = 1;
v___x_918_ = 48;
v___x_919_ = lean_uint32_dec_le(v___x_918_, v_curr_906_);
if (v___x_919_ == 0)
{
v___y_913_ = v___x_919_;
goto v___jp_912_;
}
else
{
uint32_t v___x_920_; uint8_t v___x_921_; 
v___x_920_ = 57;
v___x_921_ = lean_uint32_dec_le(v_curr_906_, v___x_920_);
v___y_913_ = v___x_921_;
goto v___jp_912_;
}
v___jp_912_:
{
if (v___y_913_ == 0)
{
lean_object* v___x_914_; 
v___x_914_ = l_Lake_Toml_mkUnexpectedCharError(v_s_895_, v_curr_906_, v_expected_898_, v___x_911_);
return v___x_914_;
}
else
{
lean_object* v_s_915_; uint32_t v___x_916_; lean_object* v___x_917_; 
lean_inc(v_pos_897_);
v_s_915_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_895_, v_c_894_, v_pos_897_);
lean_dec(v_pos_897_);
v___x_916_ = 95;
v___x_917_ = l_Lake_Toml_sepByChar1AuxFn(v___f_901_, v___x_916_, v_expected_898_, v_c_894_, v_s_915_);
return v___x_917_;
}
}
}
else
{
lean_inc(v_pos_897_);
goto v___jp_902_;
}
}
else
{
lean_inc(v_pos_897_);
goto v___jp_902_;
}
v___jp_902_:
{
lean_object* v_s_903_; uint32_t v___x_904_; lean_object* v___x_905_; 
v_s_903_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_895_, v_c_894_, v_pos_897_);
lean_dec(v_pos_897_);
v___x_904_ = 95;
v___x_905_ = l_Lake_Toml_sepByChar1Fn(v___f_901_, v___x_904_, v_expected_898_, v_c_894_, v_s_903_);
return v___x_905_;
}
}
else
{
lean_object* v___x_922_; 
v___x_922_ = l_Lean_Parser_ParserState_mkEOIError(v_s_895_, v_expected_898_);
return v___x_922_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___boxed(lean_object* v_c_923_, lean_object* v_s_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(v_c_923_, v_s_924_);
lean_dec_ref(v_c_923_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(lean_object* v_c_926_, lean_object* v_s_927_){
_start:
{
lean_object* v_toInputContext_928_; lean_object* v_pos_929_; uint8_t v___x_933_; 
v_toInputContext_928_ = lean_ctor_get(v_c_926_, 0);
v_pos_929_ = lean_ctor_get(v_s_927_, 2);
v___x_933_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_928_, v_pos_929_);
if (v___x_933_ == 0)
{
lean_object* v_inputString_934_; uint32_t v_curr_935_; uint32_t v___x_936_; uint8_t v___x_937_; 
v_inputString_934_ = lean_ctor_get(v_toInputContext_928_, 0);
v_curr_935_ = lean_string_utf8_get_fast(v_inputString_934_, v_pos_929_);
v___x_936_ = 101;
v___x_937_ = lean_uint32_dec_eq(v_curr_935_, v___x_936_);
if (v___x_937_ == 0)
{
uint32_t v___x_938_; uint8_t v___x_939_; 
v___x_938_ = 69;
v___x_939_ = lean_uint32_dec_eq(v_curr_935_, v___x_938_);
if (v___x_939_ == 0)
{
return v_s_927_;
}
else
{
lean_inc(v_pos_929_);
goto v___jp_930_;
}
}
else
{
lean_inc(v_pos_929_);
goto v___jp_930_;
}
}
else
{
return v_s_927_;
}
v___jp_930_:
{
lean_object* v___x_931_; lean_object* v___x_932_; 
v___x_931_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_927_, v_c_926_, v_pos_929_);
lean_dec(v_pos_929_);
v___x_932_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(v_c_926_, v___x_931_);
return v___x_932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn___boxed(lean_object* v_c_940_, lean_object* v_s_941_){
_start:
{
lean_object* v_res_942_; 
v_res_942_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(v_c_940_, v_s_941_);
lean_dec_ref(v_c_940_);
return v_res_942_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(lean_object* v_startPos_960_, uint32_t v_curr_961_, lean_object* v_nextPos_962_, lean_object* v_c_963_, lean_object* v_s_964_){
_start:
{
lean_object* v___y_966_; uint32_t v___x_970_; uint8_t v___x_971_; 
v___x_970_ = 46;
v___x_971_ = lean_uint32_dec_eq(v_curr_961_, v___x_970_);
if (v___x_971_ == 0)
{
uint32_t v___x_981_; uint8_t v___x_982_; 
v___x_981_ = 101;
v___x_982_ = lean_uint32_dec_eq(v_curr_961_, v___x_981_);
if (v___x_982_ == 0)
{
uint32_t v___x_983_; uint8_t v___x_984_; 
v___x_983_ = 69;
v___x_984_ = lean_uint32_dec_eq(v_curr_961_, v___x_983_);
if (v___x_984_ == 0)
{
lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; 
lean_dec(v_nextPos_962_);
v___x_985_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_986_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_987_ = l_Lake_Toml_pushLit(v___x_985_, v_startPos_960_, v___x_986_, v_c_963_, v_s_964_);
return v___x_987_;
}
else
{
goto v___jp_972_;
}
}
else
{
goto v___jp_972_;
}
}
else
{
lean_object* v___f_988_; lean_object* v_s_989_; uint32_t v___x_990_; lean_object* v___x_991_; lean_object* v_s_992_; lean_object* v_errorMsg_998_; lean_object* v___x_999_; uint8_t v___x_1000_; 
v___f_988_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0));
v_s_989_ = l_Lean_Parser_ParserState_setPos(v_s_964_, v_nextPos_962_);
v___x_990_ = 95;
v___x_991_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__8));
v_s_992_ = l_Lake_Toml_sepByChar1Fn(v___f_988_, v___x_990_, v___x_991_, v_c_963_, v_s_989_);
v_errorMsg_998_ = lean_ctor_get(v_s_992_, 4);
lean_inc(v_errorMsg_998_);
v___x_999_ = lean_box(0);
v___x_1000_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_998_, v___x_999_);
if (v___x_1000_ == 0)
{
if (v___x_971_ == 0)
{
goto v___jp_993_;
}
else
{
lean_dec_ref(v_c_963_);
lean_dec(v_startPos_960_);
return v_s_992_;
}
}
else
{
goto v___jp_993_;
}
v___jp_993_:
{
lean_object* v_s_994_; lean_object* v_errorMsg_995_; lean_object* v___x_996_; uint8_t v___x_997_; 
v_s_994_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(v_c_963_, v_s_992_);
v_errorMsg_995_ = lean_ctor_get(v_s_994_, 4);
lean_inc(v_errorMsg_995_);
v___x_996_ = lean_box(0);
v___x_997_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_995_, v___x_996_);
if (v___x_997_ == 0)
{
if (v___x_971_ == 0)
{
v___y_966_ = v_s_994_;
goto v___jp_965_;
}
else
{
lean_dec_ref(v_c_963_);
lean_dec(v_startPos_960_);
return v_s_994_;
}
}
else
{
v___y_966_ = v_s_994_;
goto v___jp_965_;
}
}
}
v___jp_965_:
{
lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v___x_967_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_968_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_969_ = l_Lake_Toml_pushLit(v___x_967_, v_startPos_960_, v___x_968_, v_c_963_, v___y_966_);
return v___x_969_;
}
v___jp_972_:
{
lean_object* v_s_973_; lean_object* v_s_974_; lean_object* v_errorMsg_975_; lean_object* v___x_976_; uint8_t v___x_977_; 
v_s_973_ = l_Lean_Parser_ParserState_setPos(v_s_964_, v_nextPos_962_);
v_s_974_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(v_c_963_, v_s_973_);
v_errorMsg_975_ = lean_ctor_get(v_s_974_, 4);
lean_inc(v_errorMsg_975_);
v___x_976_ = lean_box(0);
v___x_977_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_975_, v___x_976_);
if (v___x_977_ == 0)
{
lean_dec_ref(v_c_963_);
lean_dec(v_startPos_960_);
return v_s_974_;
}
else
{
if (v___x_971_ == 0)
{
lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; 
v___x_978_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_979_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_980_ = l_Lake_Toml_pushLit(v___x_978_, v_startPos_960_, v___x_979_, v_c_963_, v_s_974_);
return v___x_980_;
}
else
{
lean_dec_ref(v_c_963_);
lean_dec(v_startPos_960_);
return v_s_974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___boxed(lean_object* v_startPos_1001_, lean_object* v_curr_1002_, lean_object* v_nextPos_1003_, lean_object* v_c_1004_, lean_object* v_s_1005_){
_start:
{
uint32_t v_curr_boxed_1006_; lean_object* v_res_1007_; 
v_curr_boxed_1006_ = lean_unbox_uint32(v_curr_1002_);
lean_dec(v_curr_1002_);
v_res_1007_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(v_startPos_1001_, v_curr_boxed_1006_, v_nextPos_1003_, v_c_1004_, v_s_1005_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailFn(lean_object* v_startPos_1008_, lean_object* v_c_1009_, lean_object* v_s_1010_){
_start:
{
lean_object* v_toInputContext_1011_; lean_object* v_pos_1012_; uint8_t v___x_1013_; 
v_toInputContext_1011_ = lean_ctor_get(v_c_1009_, 0);
v_pos_1012_ = lean_ctor_get(v_s_1010_, 2);
v___x_1013_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1011_, v_pos_1012_);
if (v___x_1013_ == 0)
{
lean_object* v_inputString_1014_; uint32_t v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; 
v_inputString_1014_ = lean_ctor_get(v_toInputContext_1011_, 0);
v___x_1015_ = lean_string_utf8_get_fast(v_inputString_1014_, v_pos_1012_);
v___x_1016_ = lean_string_utf8_next_fast(v_inputString_1014_, v_pos_1012_);
v___x_1017_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(v_startPos_1008_, v___x_1015_, v___x_1016_, v_c_1009_, v_s_1010_);
return v___x_1017_;
}
else
{
lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; 
v___x_1018_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1019_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1020_ = l_Lake_Toml_pushLit(v___x_1018_, v_startPos_1008_, v___x_1019_, v_c_1009_, v_s_1010_);
return v___x_1020_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(lean_object* v_startPos_1028_, lean_object* v_c_1029_, lean_object* v_s_1030_){
_start:
{
lean_object* v_toInputContext_1031_; lean_object* v_pos_1032_; uint8_t v___x_1033_; 
v_toInputContext_1031_ = lean_ctor_get(v_c_1029_, 0);
v_pos_1032_ = lean_ctor_get(v_s_1030_, 2);
v___x_1033_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1031_, v_pos_1032_);
if (v___x_1033_ == 0)
{
lean_object* v_inputString_1034_; uint32_t v_curr_1035_; uint8_t v___y_1037_; uint32_t v___x_1042_; uint8_t v___x_1043_; 
v_inputString_1034_ = lean_ctor_get(v_toInputContext_1031_, 0);
v_curr_1035_ = lean_string_utf8_get_fast(v_inputString_1034_, v_pos_1032_);
v___x_1042_ = 48;
v___x_1043_ = lean_uint32_dec_le(v___x_1042_, v_curr_1035_);
if (v___x_1043_ == 0)
{
v___y_1037_ = v___x_1043_;
goto v___jp_1036_;
}
else
{
uint32_t v___x_1044_; uint8_t v___x_1045_; 
v___x_1044_ = 57;
v___x_1045_ = lean_uint32_dec_le(v_curr_1035_, v___x_1044_);
v___y_1037_ = v___x_1045_;
goto v___jp_1036_;
}
v___jp_1036_:
{
if (v___y_1037_ == 0)
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1038_ = lean_string_utf8_next_fast(v_inputString_1034_, v_pos_1032_);
v___x_1039_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1028_, v_curr_1035_, v___x_1038_, v_c_1029_, v_s_1030_);
return v___x_1039_;
}
else
{
lean_object* v_s_1040_; 
lean_inc(v_pos_1032_);
v_s_1040_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1030_, v_c_1029_, v_pos_1032_);
lean_dec(v_pos_1032_);
v_s_1030_ = v_s_1040_;
goto _start;
}
}
}
else
{
lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; 
v___x_1046_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1047_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1048_ = l_Lake_Toml_pushLit(v___x_1046_, v_startPos_1028_, v___x_1047_, v_c_1029_, v_s_1030_);
return v___x_1048_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn(lean_object* v_startPos_1049_, lean_object* v_c_1050_, lean_object* v_s_1051_){
_start:
{
lean_object* v_pos_1052_; lean_object* v_toInputContext_1053_; lean_object* v_expected_1054_; uint8_t v___x_1055_; 
v_pos_1052_ = lean_ctor_get(v_s_1051_, 2);
v_toInputContext_1053_ = lean_ctor_get(v_c_1050_, 0);
v_expected_1054_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2));
v___x_1055_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1053_, v_pos_1052_);
if (v___x_1055_ == 0)
{
lean_object* v_inputString_1056_; uint8_t v___x_1057_; uint32_t v_curr_1058_; uint8_t v___y_1060_; uint32_t v___x_1064_; uint8_t v___x_1065_; 
v_inputString_1056_ = lean_ctor_get(v_toInputContext_1053_, 0);
v___x_1057_ = 1;
v_curr_1058_ = lean_string_utf8_get_fast(v_inputString_1056_, v_pos_1052_);
v___x_1064_ = 48;
v___x_1065_ = lean_uint32_dec_le(v___x_1064_, v_curr_1058_);
if (v___x_1065_ == 0)
{
v___y_1060_ = v___x_1065_;
goto v___jp_1059_;
}
else
{
uint32_t v___x_1066_; uint8_t v___x_1067_; 
v___x_1066_ = 57;
v___x_1067_ = lean_uint32_dec_le(v_curr_1058_, v___x_1066_);
v___y_1060_ = v___x_1067_;
goto v___jp_1059_;
}
v___jp_1059_:
{
if (v___y_1060_ == 0)
{
lean_object* v___x_1061_; 
lean_dec_ref(v_c_1050_);
lean_dec(v_startPos_1049_);
v___x_1061_ = l_Lake_Toml_mkUnexpectedCharError(v_s_1051_, v_curr_1058_, v_expected_1054_, v___x_1057_);
return v___x_1061_;
}
else
{
lean_object* v_s_1062_; lean_object* v___x_1063_; 
lean_inc(v_pos_1052_);
v_s_1062_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1051_, v_c_1050_, v_pos_1052_);
lean_dec(v_pos_1052_);
v___x_1063_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(v_startPos_1049_, v_c_1050_, v_s_1062_);
return v___x_1063_;
}
}
}
else
{
lean_object* v___x_1068_; 
lean_dec_ref(v_c_1050_);
lean_dec(v_startPos_1049_);
v___x_1068_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1051_, v_expected_1054_);
return v___x_1068_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(lean_object* v_startPos_1069_, uint32_t v_curr_1070_, lean_object* v_nextPos_1071_, lean_object* v_c_1072_, lean_object* v_s_1073_){
_start:
{
uint32_t v___x_1074_; uint8_t v___x_1075_; 
v___x_1074_ = 95;
v___x_1075_ = lean_uint32_dec_eq(v_curr_1070_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; 
v___x_1076_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(v_startPos_1069_, v_curr_1070_, v_nextPos_1071_, v_c_1072_, v_s_1073_);
return v___x_1076_;
}
else
{
lean_object* v_s_1077_; lean_object* v___x_1078_; 
v_s_1077_ = l_Lean_Parser_ParserState_setPos(v_s_1073_, v_nextPos_1071_);
v___x_1078_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn(v_startPos_1069_, v_c_1072_, v_s_1077_);
return v___x_1078_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn___boxed(lean_object* v_startPos_1079_, lean_object* v_curr_1080_, lean_object* v_nextPos_1081_, lean_object* v_c_1082_, lean_object* v_s_1083_){
_start:
{
uint32_t v_curr_boxed_1084_; lean_object* v_res_1085_; 
v_curr_boxed_1084_ = lean_unbox_uint32(v_curr_1080_);
lean_dec(v_curr_1080_);
v_res_1085_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1079_, v_curr_boxed_1084_, v_nextPos_1081_, v_c_1082_, v_s_1083_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(lean_object* v_startPos_1091_, lean_object* v_a_1092_, lean_object* v_a_1093_){
_start:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v_s_1096_; lean_object* v_errorMsg_1097_; lean_object* v___x_1098_; uint8_t v___x_1099_; 
v___x_1094_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__0));
v___x_1095_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__2));
lean_inc_ref(v_a_1092_);
v_s_1096_ = l_Lake_Toml_strFn(v___x_1094_, v___x_1095_, v_a_1092_, v_a_1093_);
v_errorMsg_1097_ = lean_ctor_get(v_s_1096_, 4);
lean_inc(v_errorMsg_1097_);
v___x_1098_ = lean_box(0);
v___x_1099_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1097_, v___x_1098_);
if (v___x_1099_ == 0)
{
lean_dec_ref(v_a_1092_);
lean_dec(v_startPos_1091_);
return v_s_1096_;
}
else
{
lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1100_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_1101_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1102_ = l_Lake_Toml_pushLit(v___x_1100_, v_startPos_1091_, v___x_1101_, v_a_1092_, v_s_1096_);
return v___x_1102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(lean_object* v_startPos_1108_, lean_object* v_a_1109_, lean_object* v_a_1110_){
_start:
{
lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v_s_1113_; lean_object* v_errorMsg_1114_; lean_object* v___x_1115_; uint8_t v___x_1116_; 
v___x_1111_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__0));
v___x_1112_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__2));
lean_inc_ref(v_a_1109_);
v_s_1113_ = l_Lake_Toml_strFn(v___x_1111_, v___x_1112_, v_a_1109_, v_a_1110_);
v_errorMsg_1114_ = lean_ctor_get(v_s_1113_, 4);
lean_inc(v_errorMsg_1114_);
v___x_1115_ = lean_box(0);
v___x_1116_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1114_, v___x_1115_);
if (v___x_1116_ == 0)
{
lean_dec_ref(v_a_1109_);
lean_dec(v_startPos_1108_);
return v_s_1113_;
}
else
{
lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1117_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_1118_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1119_ = l_Lake_Toml_pushLit(v___x_1117_, v_startPos_1108_, v___x_1118_, v_a_1109_, v_s_1113_);
return v___x_1119_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decimalFn(lean_object* v_startPos_1120_, lean_object* v_c_1121_, lean_object* v_s_1122_){
_start:
{
lean_object* v_toInputContext_1123_; lean_object* v_pos_1124_; lean_object* v_expected_1125_; uint8_t v___x_1126_; 
v_toInputContext_1123_ = lean_ctor_get(v_c_1121_, 0);
v_pos_1124_ = lean_ctor_get(v_s_1122_, 2);
v_expected_1125_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2));
v___x_1126_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1123_, v_pos_1124_);
if (v___x_1126_ == 0)
{
lean_object* v_inputString_1127_; uint32_t v_curr_1128_; uint32_t v___x_1129_; uint8_t v___x_1130_; 
v_inputString_1127_ = lean_ctor_get(v_toInputContext_1123_, 0);
v_curr_1128_ = lean_string_utf8_get_fast(v_inputString_1127_, v_pos_1124_);
v___x_1129_ = 48;
v___x_1130_ = lean_uint32_dec_eq(v_curr_1128_, v___x_1129_);
if (v___x_1130_ == 0)
{
uint8_t v___x_1131_; uint8_t v___y_1133_; uint8_t v___x_1145_; 
v___x_1131_ = 1;
v___x_1145_ = lean_uint32_dec_le(v___x_1129_, v_curr_1128_);
if (v___x_1145_ == 0)
{
v___y_1133_ = v___x_1145_;
goto v___jp_1132_;
}
else
{
uint32_t v___x_1146_; uint8_t v___x_1147_; 
v___x_1146_ = 57;
v___x_1147_ = lean_uint32_dec_le(v_curr_1128_, v___x_1146_);
v___y_1133_ = v___x_1147_;
goto v___jp_1132_;
}
v___jp_1132_:
{
if (v___y_1133_ == 0)
{
uint32_t v___x_1134_; uint8_t v___x_1135_; 
v___x_1134_ = 105;
v___x_1135_ = lean_uint32_dec_eq(v_curr_1128_, v___x_1134_);
if (v___x_1135_ == 0)
{
uint32_t v___x_1136_; uint8_t v___x_1137_; 
v___x_1136_ = 110;
v___x_1137_ = lean_uint32_dec_eq(v_curr_1128_, v___x_1136_);
if (v___x_1137_ == 0)
{
lean_object* v___x_1138_; 
lean_dec_ref(v_c_1121_);
lean_dec(v_startPos_1120_);
v___x_1138_ = l_Lake_Toml_mkUnexpectedCharError(v_s_1122_, v_curr_1128_, v_expected_1125_, v___x_1131_);
return v___x_1138_;
}
else
{
lean_object* v___x_1139_; lean_object* v___x_1140_; 
lean_inc(v_pos_1124_);
v___x_1139_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1122_, v_c_1121_, v_pos_1124_);
lean_dec(v_pos_1124_);
v___x_1140_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(v_startPos_1120_, v_c_1121_, v___x_1139_);
return v___x_1140_;
}
}
else
{
lean_object* v___x_1141_; lean_object* v___x_1142_; 
lean_inc(v_pos_1124_);
v___x_1141_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1122_, v_c_1121_, v_pos_1124_);
lean_dec(v_pos_1124_);
v___x_1142_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(v_startPos_1120_, v_c_1121_, v___x_1141_);
return v___x_1142_;
}
}
else
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
lean_inc(v_pos_1124_);
v___x_1143_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1122_, v_c_1121_, v_pos_1124_);
lean_dec(v_pos_1124_);
v___x_1144_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(v_startPos_1120_, v_c_1121_, v___x_1143_);
return v___x_1144_;
}
}
}
else
{
lean_object* v___x_1148_; lean_object* v___x_1149_; 
lean_inc(v_pos_1124_);
v___x_1148_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1122_, v_c_1121_, v_pos_1124_);
lean_dec(v_pos_1124_);
v___x_1149_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailFn(v_startPos_1120_, v_c_1121_, v___x_1148_);
return v___x_1149_;
}
}
else
{
lean_object* v___x_1150_; 
lean_dec_ref(v_c_1121_);
lean_dec(v_startPos_1120_);
v___x_1150_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1122_, v_expected_1125_);
return v___x_1150_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn(lean_object* v_startPos_1166_, lean_object* v_c_1167_, lean_object* v_s_1168_){
_start:
{
lean_object* v___y_1170_; lean_object* v___y_1171_; uint32_t v___y_1172_; uint8_t v___y_1173_; lean_object* v___y_1178_; uint8_t v___y_1179_; lean_object* v___y_1184_; uint8_t v___y_1185_; lean_object* v_toInputContext_1189_; lean_object* v_pos_1190_; uint8_t v___x_1191_; 
v_toInputContext_1189_ = lean_ctor_get(v_c_1167_, 0);
v_pos_1190_ = lean_ctor_get(v_s_1168_, 2);
v___x_1191_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1189_, v_pos_1190_);
if (v___x_1191_ == 0)
{
lean_object* v_inputString_1192_; lean_object* v___y_1194_; lean_object* v___y_1195_; uint32_t v___y_1196_; uint8_t v___y_1197_; lean_object* v___y_1219_; uint32_t v___y_1220_; lean_object* v___y_1221_; uint8_t v___y_1222_; uint32_t v_curr_1236_; lean_object* v_nextPos_1237_; uint8_t v___y_1239_; uint32_t v___x_1260_; uint8_t v___x_1261_; 
v_inputString_1192_ = lean_ctor_get(v_toInputContext_1189_, 0);
v_curr_1236_ = lean_string_utf8_get_fast(v_inputString_1192_, v_pos_1190_);
v_nextPos_1237_ = lean_string_utf8_next_fast(v_inputString_1192_, v_pos_1190_);
v___x_1260_ = 48;
v___x_1261_ = lean_uint32_dec_le(v___x_1260_, v_curr_1236_);
if (v___x_1261_ == 0)
{
v___y_1239_ = v___x_1261_;
goto v___jp_1238_;
}
else
{
uint32_t v___x_1262_; uint8_t v___x_1263_; 
v___x_1262_ = 57;
v___x_1263_ = lean_uint32_dec_le(v_curr_1236_, v___x_1262_);
v___y_1239_ = v___x_1263_;
goto v___jp_1238_;
}
v___jp_1193_:
{
if (v___y_1197_ == 0)
{
lean_object* v___x_1198_; 
v___x_1198_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1166_, v___y_1196_, v___y_1194_, v_c_1167_, v___y_1195_);
return v___x_1198_;
}
else
{
lean_object* v_s_1199_; uint8_t v___x_1200_; 
lean_inc(v___y_1194_);
v_s_1199_ = l_Lean_Parser_ParserState_setPos(v___y_1195_, v___y_1194_);
v___x_1200_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1189_, v___y_1194_);
lean_dec(v___y_1194_);
if (v___x_1200_ == 0)
{
lean_object* v_pos_1201_; uint32_t v_curr_1202_; lean_object* v_nextPos_1203_; uint32_t v___x_1204_; uint8_t v___x_1205_; 
v_pos_1201_ = lean_ctor_get(v_s_1199_, 2);
lean_inc(v_pos_1201_);
v_curr_1202_ = lean_string_utf8_get_fast(v_inputString_1192_, v_pos_1201_);
v_nextPos_1203_ = lean_string_utf8_next_fast(v_inputString_1192_, v_pos_1201_);
lean_dec(v_pos_1201_);
v___x_1204_ = 45;
v___x_1205_ = lean_uint32_dec_eq(v_curr_1202_, v___x_1204_);
if (v___x_1205_ == 0)
{
uint32_t v___x_1206_; uint8_t v___x_1207_; 
v___x_1206_ = 48;
v___x_1207_ = lean_uint32_dec_le(v___x_1206_, v_curr_1202_);
if (v___x_1207_ == 0)
{
v___y_1170_ = v_s_1199_;
v___y_1171_ = v_nextPos_1203_;
v___y_1172_ = v_curr_1202_;
v___y_1173_ = v___x_1207_;
goto v___jp_1169_;
}
else
{
uint32_t v___x_1208_; uint8_t v___x_1209_; 
v___x_1208_ = 57;
v___x_1209_ = lean_uint32_dec_le(v_curr_1202_, v___x_1208_);
v___y_1170_ = v_s_1199_;
v___y_1171_ = v_nextPos_1203_;
v___y_1172_ = v_curr_1202_;
v___y_1173_ = v___x_1209_;
goto v___jp_1169_;
}
}
else
{
lean_object* v_s_1210_; lean_object* v_s_1211_; lean_object* v_errorMsg_1212_; lean_object* v___x_1213_; uint8_t v___x_1214_; 
v_s_1210_ = l_Lean_Parser_ParserState_setPos(v_s_1199_, v_nextPos_1203_);
v_s_1211_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(v_c_1167_, v_s_1210_);
v_errorMsg_1212_ = lean_ctor_get(v_s_1211_, 4);
lean_inc(v_errorMsg_1212_);
v___x_1213_ = lean_box(0);
v___x_1214_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1212_, v___x_1213_);
if (v___x_1214_ == 0)
{
v___y_1178_ = v_s_1211_;
v___y_1179_ = v___x_1205_;
goto v___jp_1177_;
}
else
{
v___y_1178_ = v_s_1211_;
v___y_1179_ = v___x_1200_;
goto v___jp_1177_;
}
}
}
else
{
lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; 
v___x_1215_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1216_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1217_ = l_Lake_Toml_pushLit(v___x_1215_, v_startPos_1166_, v___x_1216_, v_c_1167_, v_s_1199_);
return v___x_1217_;
}
}
}
v___jp_1218_:
{
if (v___y_1222_ == 0)
{
lean_object* v___x_1223_; 
v___x_1223_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1166_, v___y_1220_, v___y_1221_, v_c_1167_, v___y_1219_);
return v___x_1223_;
}
else
{
lean_object* v_s_1224_; lean_object* v_pos_1225_; uint8_t v___x_1226_; 
v_s_1224_ = l_Lean_Parser_ParserState_setPos(v___y_1219_, v___y_1221_);
v_pos_1225_ = lean_ctor_get(v_s_1224_, 2);
lean_inc(v_pos_1225_);
v___x_1226_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1189_, v_pos_1225_);
if (v___x_1226_ == 0)
{
uint32_t v_curr_1227_; lean_object* v_nextPos_1228_; uint32_t v___x_1229_; uint8_t v___x_1230_; 
v_curr_1227_ = lean_string_utf8_get_fast(v_inputString_1192_, v_pos_1225_);
v_nextPos_1228_ = lean_string_utf8_next_fast(v_inputString_1192_, v_pos_1225_);
lean_dec(v_pos_1225_);
v___x_1229_ = 48;
v___x_1230_ = lean_uint32_dec_le(v___x_1229_, v_curr_1227_);
if (v___x_1230_ == 0)
{
v___y_1194_ = v_nextPos_1228_;
v___y_1195_ = v_s_1224_;
v___y_1196_ = v_curr_1227_;
v___y_1197_ = v___x_1230_;
goto v___jp_1193_;
}
else
{
uint32_t v___x_1231_; uint8_t v___x_1232_; 
v___x_1231_ = 57;
v___x_1232_ = lean_uint32_dec_le(v_curr_1227_, v___x_1231_);
v___y_1194_ = v_nextPos_1228_;
v___y_1195_ = v_s_1224_;
v___y_1196_ = v_curr_1227_;
v___y_1197_ = v___x_1232_;
goto v___jp_1193_;
}
}
else
{
lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
lean_dec(v_pos_1225_);
v___x_1233_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1234_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1235_ = l_Lake_Toml_pushLit(v___x_1233_, v_startPos_1166_, v___x_1234_, v_c_1167_, v_s_1224_);
return v___x_1235_;
}
}
}
v___jp_1238_:
{
if (v___y_1239_ == 0)
{
lean_object* v___x_1240_; 
v___x_1240_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1166_, v_curr_1236_, v_nextPos_1237_, v_c_1167_, v_s_1168_);
return v___x_1240_;
}
else
{
lean_object* v_s_1241_; lean_object* v_pos_1242_; uint8_t v___x_1243_; 
v_s_1241_ = l_Lean_Parser_ParserState_setPos(v_s_1168_, v_nextPos_1237_);
v_pos_1242_ = lean_ctor_get(v_s_1241_, 2);
lean_inc(v_pos_1242_);
v___x_1243_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1189_, v_pos_1242_);
if (v___x_1243_ == 0)
{
uint32_t v_curr_1244_; lean_object* v_nextPos_1245_; uint32_t v___x_1246_; uint8_t v___x_1247_; 
v_curr_1244_ = lean_string_utf8_get_fast(v_inputString_1192_, v_pos_1242_);
v_nextPos_1245_ = lean_string_utf8_next_fast(v_inputString_1192_, v_pos_1242_);
lean_dec(v_pos_1242_);
v___x_1246_ = 58;
v___x_1247_ = lean_uint32_dec_eq(v_curr_1244_, v___x_1246_);
if (v___x_1247_ == 0)
{
uint32_t v___x_1248_; uint8_t v___x_1249_; 
v___x_1248_ = 48;
v___x_1249_ = lean_uint32_dec_le(v___x_1248_, v_curr_1244_);
if (v___x_1249_ == 0)
{
v___y_1219_ = v_s_1241_;
v___y_1220_ = v_curr_1244_;
v___y_1221_ = v_nextPos_1245_;
v___y_1222_ = v___x_1249_;
goto v___jp_1218_;
}
else
{
uint32_t v___x_1250_; uint8_t v___x_1251_; 
v___x_1250_ = 57;
v___x_1251_ = lean_uint32_dec_le(v_curr_1244_, v___x_1250_);
v___y_1219_ = v_s_1241_;
v___y_1220_ = v_curr_1244_;
v___y_1221_ = v_nextPos_1245_;
v___y_1222_ = v___x_1251_;
goto v___jp_1218_;
}
}
else
{
lean_object* v_s_1252_; lean_object* v_s_1253_; lean_object* v_errorMsg_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v_s_1252_ = l_Lean_Parser_ParserState_setPos(v_s_1241_, v_nextPos_1245_);
v_s_1253_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(v___x_1243_, v_c_1167_, v_s_1252_);
v_errorMsg_1254_ = lean_ctor_get(v_s_1253_, 4);
lean_inc(v_errorMsg_1254_);
v___x_1255_ = lean_box(0);
v___x_1256_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1254_, v___x_1255_);
if (v___x_1256_ == 0)
{
v___y_1184_ = v_s_1253_;
v___y_1185_ = v___x_1247_;
goto v___jp_1183_;
}
else
{
v___y_1184_ = v_s_1253_;
v___y_1185_ = v___x_1243_;
goto v___jp_1183_;
}
}
}
else
{
lean_object* v___x_1257_; lean_object* v___x_1258_; lean_object* v___x_1259_; 
lean_dec(v_pos_1242_);
v___x_1257_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1258_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1259_ = l_Lake_Toml_pushLit(v___x_1257_, v_startPos_1166_, v___x_1258_, v_c_1167_, v_s_1241_);
return v___x_1259_;
}
}
}
}
else
{
lean_object* v___x_1264_; lean_object* v___x_1265_; 
lean_dec_ref(v_c_1167_);
lean_dec(v_startPos_1166_);
v___x_1264_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__5));
v___x_1265_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1168_, v___x_1264_);
return v___x_1265_;
}
v___jp_1169_:
{
if (v___y_1173_ == 0)
{
lean_object* v___x_1174_; 
v___x_1174_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1166_, v___y_1172_, v___y_1171_, v_c_1167_, v___y_1170_);
return v___x_1174_;
}
else
{
lean_object* v_s_1175_; lean_object* v___x_1176_; 
v_s_1175_ = l_Lean_Parser_ParserState_setPos(v___y_1170_, v___y_1171_);
v___x_1176_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(v_startPos_1166_, v_c_1167_, v_s_1175_);
return v___x_1176_;
}
}
v___jp_1177_:
{
if (v___y_1179_ == 0)
{
lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1180_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_1181_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1182_ = l_Lake_Toml_pushLit(v___x_1180_, v_startPos_1166_, v___x_1181_, v_c_1167_, v___y_1178_);
return v___x_1182_;
}
else
{
lean_dec_ref(v_c_1167_);
lean_dec(v_startPos_1166_);
return v___y_1178_;
}
}
v___jp_1183_:
{
if (v___y_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; 
v___x_1186_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_1187_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1188_ = l_Lake_Toml_pushLit(v___x_1186_, v_startPos_1166_, v___x_1187_, v_c_1167_, v___y_1184_);
return v___x_1188_;
}
else
{
lean_dec_ref(v_c_1167_);
lean_dec(v_startPos_1166_);
return v___y_1184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralFn___lam__0(lean_object* v_c_1301_, lean_object* v_s_1302_){
_start:
{
lean_object* v_pos_1303_; lean_object* v_toInputContext_1307_; lean_object* v_expected_1308_; uint8_t v___x_1309_; 
v_pos_1303_ = lean_ctor_get(v_s_1302_, 2);
v_toInputContext_1307_ = lean_ctor_get(v_c_1301_, 0);
v_expected_1308_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__1));
v___x_1309_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1307_, v_pos_1303_);
if (v___x_1309_ == 0)
{
lean_object* v_inputString_1310_; uint32_t v_curr_1311_; uint32_t v___x_1312_; uint8_t v___x_1313_; 
v_inputString_1310_ = lean_ctor_get(v_toInputContext_1307_, 0);
v_curr_1311_ = lean_string_utf8_get_fast(v_inputString_1310_, v_pos_1303_);
v___x_1312_ = 48;
v___x_1313_ = lean_uint32_dec_eq(v_curr_1311_, v___x_1312_);
if (v___x_1313_ == 0)
{
uint8_t v___x_1314_; uint8_t v___y_1316_; uint8_t v___x_1338_; 
v___x_1314_ = 1;
v___x_1338_ = lean_uint32_dec_le(v___x_1312_, v_curr_1311_);
if (v___x_1338_ == 0)
{
v___y_1316_ = v___x_1338_;
goto v___jp_1315_;
}
else
{
uint32_t v___x_1339_; uint8_t v___x_1340_; 
v___x_1339_ = 57;
v___x_1340_ = lean_uint32_dec_le(v_curr_1311_, v___x_1339_);
v___y_1316_ = v___x_1340_;
goto v___jp_1315_;
}
v___jp_1315_:
{
if (v___y_1316_ == 0)
{
uint32_t v___x_1317_; uint8_t v___x_1318_; 
v___x_1317_ = 43;
v___x_1318_ = lean_uint32_dec_eq(v_curr_1311_, v___x_1317_);
if (v___x_1318_ == 0)
{
uint32_t v___x_1319_; uint8_t v___x_1320_; 
v___x_1319_ = 45;
v___x_1320_ = lean_uint32_dec_eq(v_curr_1311_, v___x_1319_);
if (v___x_1320_ == 0)
{
uint32_t v___x_1321_; uint8_t v___x_1322_; 
v___x_1321_ = 105;
v___x_1322_ = lean_uint32_dec_eq(v_curr_1311_, v___x_1321_);
if (v___x_1322_ == 0)
{
uint32_t v___x_1323_; uint8_t v___x_1324_; 
v___x_1323_ = 110;
v___x_1324_ = lean_uint32_dec_eq(v_curr_1311_, v___x_1323_);
if (v___x_1324_ == 0)
{
lean_object* v___x_1325_; lean_object* v___x_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_dec_ref(v_c_1301_);
v___x_1325_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__2));
v___x_1326_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_1327_ = lean_string_push(v___x_1326_, v_curr_1311_);
v___x_1328_ = lean_string_append(v___x_1325_, v___x_1327_);
lean_dec_ref(v___x_1327_);
v___x_1329_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1330_ = lean_string_append(v___x_1328_, v___x_1329_);
v___x_1331_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1302_, v___x_1330_, v_expected_1308_, v___x_1314_);
return v___x_1331_;
}
else
{
lean_object* v___x_1332_; lean_object* v___x_1333_; 
lean_inc(v_pos_1303_);
v___x_1332_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1302_, v_c_1301_, v_pos_1303_);
v___x_1333_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(v_pos_1303_, v_c_1301_, v___x_1332_);
return v___x_1333_;
}
}
else
{
lean_object* v___x_1334_; lean_object* v___x_1335_; 
lean_inc(v_pos_1303_);
v___x_1334_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1302_, v_c_1301_, v_pos_1303_);
v___x_1335_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(v_pos_1303_, v_c_1301_, v___x_1334_);
return v___x_1335_;
}
}
else
{
lean_inc(v_pos_1303_);
goto v___jp_1304_;
}
}
else
{
lean_inc(v_pos_1303_);
goto v___jp_1304_;
}
}
else
{
lean_object* v___x_1336_; lean_object* v___x_1337_; 
lean_inc(v_pos_1303_);
v___x_1336_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1302_, v_c_1301_, v_pos_1303_);
v___x_1337_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn(v_pos_1303_, v_c_1301_, v___x_1336_);
return v___x_1337_;
}
}
}
else
{
lean_object* v_s_1341_; lean_object* v_pos_1342_; uint8_t v___x_1343_; 
lean_inc(v_pos_1303_);
v_s_1341_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1302_, v_c_1301_, v_pos_1303_);
v_pos_1342_ = lean_ctor_get(v_s_1341_, 2);
lean_inc(v_pos_1342_);
v___x_1343_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1307_, v_pos_1342_);
if (v___x_1343_ == 0)
{
uint32_t v_curr_1344_; uint32_t v___x_1345_; uint8_t v___x_1346_; 
v_curr_1344_ = lean_string_utf8_get_fast(v_inputString_1310_, v_pos_1342_);
v___x_1345_ = 98;
v___x_1346_ = lean_uint32_dec_eq(v_curr_1344_, v___x_1345_);
if (v___x_1346_ == 0)
{
uint32_t v___x_1347_; uint8_t v___x_1348_; 
v___x_1347_ = 111;
v___x_1348_ = lean_uint32_dec_eq(v_curr_1344_, v___x_1347_);
if (v___x_1348_ == 0)
{
uint32_t v___x_1349_; uint8_t v___x_1350_; lean_object* v___y_1352_; uint8_t v___y_1360_; 
v___x_1349_ = 120;
v___x_1350_ = lean_uint32_dec_eq(v_curr_1344_, v___x_1349_);
if (v___x_1350_ == 0)
{
uint8_t v___x_1371_; 
v___x_1371_ = lean_uint32_dec_le(v___x_1312_, v_curr_1344_);
if (v___x_1371_ == 0)
{
v___y_1360_ = v___x_1371_;
goto v___jp_1359_;
}
else
{
uint32_t v___x_1372_; uint8_t v___x_1373_; 
v___x_1372_ = 57;
v___x_1373_ = lean_uint32_dec_le(v_curr_1344_, v___x_1372_);
v___y_1360_ = v___x_1373_;
goto v___jp_1359_;
}
}
else
{
lean_object* v_s_1374_; lean_object* v___x_1375_; uint32_t v___x_1376_; lean_object* v___x_1377_; lean_object* v_s_1378_; uint8_t v___y_1380_; lean_object* v_errorMsg_1384_; lean_object* v___x_1385_; uint8_t v___x_1386_; 
v_s_1374_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1341_, v_c_1301_, v_pos_1342_);
lean_dec(v_pos_1342_);
v___x_1375_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__3));
v___x_1376_ = 95;
v___x_1377_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__5));
v_s_1378_ = l_Lake_Toml_sepByChar1Fn(v___x_1375_, v___x_1376_, v___x_1377_, v_c_1301_, v_s_1374_);
v_errorMsg_1384_ = lean_ctor_get(v_s_1378_, 4);
lean_inc(v_errorMsg_1384_);
v___x_1385_ = lean_box(0);
v___x_1386_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1384_, v___x_1385_);
if (v___x_1386_ == 0)
{
v___y_1380_ = v___x_1350_;
goto v___jp_1379_;
}
else
{
v___y_1380_ = v___x_1348_;
goto v___jp_1379_;
}
v___jp_1379_:
{
if (v___y_1380_ == 0)
{
lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
v___x_1381_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__7));
v___x_1382_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1383_ = l_Lake_Toml_pushLit(v___x_1381_, v_pos_1303_, v___x_1382_, v_c_1301_, v_s_1378_);
return v___x_1383_;
}
else
{
lean_dec(v_pos_1303_);
lean_dec_ref(v_c_1301_);
return v_s_1378_;
}
}
}
v___jp_1351_:
{
lean_object* v_errorMsg_1353_; lean_object* v___x_1354_; uint8_t v___x_1355_; 
v_errorMsg_1353_ = lean_ctor_get(v___y_1352_, 4);
v___x_1354_ = lean_box(0);
lean_inc(v_errorMsg_1353_);
v___x_1355_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1353_, v___x_1354_);
if (v___x_1355_ == 0)
{
lean_dec(v_pos_1303_);
lean_dec_ref(v_c_1301_);
return v___y_1352_;
}
else
{
if (v___x_1350_ == 0)
{
lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
v___x_1356_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_1357_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1358_ = l_Lake_Toml_pushLit(v___x_1356_, v_pos_1303_, v___x_1357_, v_c_1301_, v___y_1352_);
return v___x_1358_;
}
else
{
lean_dec(v_pos_1303_);
lean_dec_ref(v_c_1301_);
return v___y_1352_;
}
}
}
v___jp_1359_:
{
if (v___y_1360_ == 0)
{
lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1361_ = lean_string_utf8_next_fast(v_inputString_1310_, v_pos_1342_);
lean_dec(v_pos_1342_);
v___x_1362_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(v_pos_1303_, v_curr_1344_, v___x_1361_, v_c_1301_, v_s_1341_);
return v___x_1362_;
}
else
{
lean_object* v_s_1363_; uint32_t v___x_1364_; lean_object* v___x_1365_; lean_object* v_s_1366_; lean_object* v_errorMsg_1367_; lean_object* v___x_1368_; uint8_t v___x_1369_; 
v_s_1363_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1341_, v_c_1301_, v_pos_1342_);
lean_dec(v_pos_1342_);
v___x_1364_ = 58;
v___x_1365_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7, &l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7);
v_s_1366_ = l_Lake_Toml_chFn(v___x_1364_, v___x_1365_, v_c_1301_, v_s_1363_);
v_errorMsg_1367_ = lean_ctor_get(v_s_1366_, 4);
lean_inc(v_errorMsg_1367_);
v___x_1368_ = lean_box(0);
v___x_1369_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1367_, v___x_1368_);
if (v___x_1369_ == 0)
{
v___y_1352_ = v_s_1366_;
goto v___jp_1351_;
}
else
{
lean_object* v___x_1370_; 
v___x_1370_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(v___x_1350_, v_c_1301_, v_s_1366_);
v___y_1352_ = v___x_1370_;
goto v___jp_1351_;
}
}
}
}
else
{
lean_object* v_s_1387_; lean_object* v___x_1388_; uint32_t v___x_1389_; lean_object* v___x_1390_; lean_object* v_s_1391_; uint8_t v___y_1393_; lean_object* v_errorMsg_1397_; lean_object* v___x_1398_; uint8_t v___x_1399_; 
v_s_1387_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1341_, v_c_1301_, v_pos_1342_);
lean_dec(v_pos_1342_);
v___x_1388_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__8));
v___x_1389_ = 95;
v___x_1390_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__10));
v_s_1391_ = l_Lake_Toml_sepByChar1Fn(v___x_1388_, v___x_1389_, v___x_1390_, v_c_1301_, v_s_1387_);
v_errorMsg_1397_ = lean_ctor_get(v_s_1391_, 4);
lean_inc(v_errorMsg_1397_);
v___x_1398_ = lean_box(0);
v___x_1399_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1397_, v___x_1398_);
if (v___x_1399_ == 0)
{
v___y_1393_ = v___x_1348_;
goto v___jp_1392_;
}
else
{
v___y_1393_ = v___x_1346_;
goto v___jp_1392_;
}
v___jp_1392_:
{
if (v___y_1393_ == 0)
{
lean_object* v___x_1394_; lean_object* v___x_1395_; lean_object* v___x_1396_; 
v___x_1394_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__12));
v___x_1395_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1396_ = l_Lake_Toml_pushLit(v___x_1394_, v_pos_1303_, v___x_1395_, v_c_1301_, v_s_1391_);
return v___x_1396_;
}
else
{
lean_dec(v_pos_1303_);
lean_dec_ref(v_c_1301_);
return v_s_1391_;
}
}
}
}
else
{
lean_object* v_s_1400_; lean_object* v___x_1401_; uint32_t v___x_1402_; lean_object* v___x_1403_; lean_object* v_s_1404_; uint8_t v___y_1406_; lean_object* v_errorMsg_1410_; lean_object* v___x_1411_; uint8_t v___x_1412_; 
v_s_1400_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1341_, v_c_1301_, v_pos_1342_);
lean_dec(v_pos_1342_);
v___x_1401_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__13));
v___x_1402_ = 95;
v___x_1403_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__15));
v_s_1404_ = l_Lake_Toml_sepByChar1Fn(v___x_1401_, v___x_1402_, v___x_1403_, v_c_1301_, v_s_1400_);
v_errorMsg_1410_ = lean_ctor_get(v_s_1404_, 4);
lean_inc(v_errorMsg_1410_);
v___x_1411_ = lean_box(0);
v___x_1412_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1410_, v___x_1411_);
if (v___x_1412_ == 0)
{
v___y_1406_ = v___x_1346_;
goto v___jp_1405_;
}
else
{
v___y_1406_ = v___x_1343_;
goto v___jp_1405_;
}
v___jp_1405_:
{
if (v___y_1406_ == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1407_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__17));
v___x_1408_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1409_ = l_Lake_Toml_pushLit(v___x_1407_, v_pos_1303_, v___x_1408_, v_c_1301_, v_s_1404_);
return v___x_1409_;
}
else
{
lean_dec(v_pos_1303_);
lean_dec_ref(v_c_1301_);
return v_s_1404_;
}
}
}
}
else
{
lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; 
lean_dec(v_pos_1342_);
v___x_1413_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1414_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1415_ = l_Lake_Toml_pushLit(v___x_1413_, v_pos_1303_, v___x_1414_, v_c_1301_, v_s_1341_);
return v___x_1415_;
}
}
}
else
{
lean_object* v___x_1416_; 
lean_dec_ref(v_c_1301_);
v___x_1416_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1302_, v_expected_1308_);
return v___x_1416_;
}
v___jp_1304_:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1302_, v_c_1301_, v_pos_1303_);
v___x_1306_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decimalFn(v_pos_1303_, v_c_1301_, v___x_1305_);
return v___x_1306_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralFn(lean_object* v_a_1418_, lean_object* v_a_1419_){
_start:
{
lean_object* v___f_1420_; lean_object* v___x_1421_; 
v___f_1420_ = ((lean_object*)(l_Lake_Toml_numeralFn___closed__0));
v___x_1421_ = l_Lean_Parser_atomicFn(v___f_1420_, v_a_1418_, v_a_1419_);
return v___x_1421_;
}
}
static lean_object* _init_l_Lake_Toml_trailingWs___closed__0(void){
_start:
{
lean_object* v___x_1422_; lean_object* v___x_1423_; 
v___x_1422_ = lean_alloc_closure((void*)(l_Lake_Toml_wsFn___boxed), 2, 0);
v___x_1423_ = l_Lake_Toml_trailing(v___x_1422_);
return v___x_1423_;
}
}
static lean_object* _init_l_Lake_Toml_trailingWs(void){
_start:
{
lean_object* v___x_1424_; 
v___x_1424_ = lean_obj_once(&l_Lake_Toml_trailingWs___closed__0, &l_Lake_Toml_trailingWs___closed__0_once, _init_l_Lake_Toml_trailingWs___closed__0);
return v___x_1424_;
}
}
static lean_object* _init_l_Lake_Toml_trailingSep___closed__1(void){
_start:
{
lean_object* v___x_1426_; lean_object* v___x_1427_; 
v___x_1426_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1427_ = l_Lake_Toml_trailing(v___x_1426_);
return v___x_1427_;
}
}
static lean_object* _init_l_Lake_Toml_trailingSep(void){
_start:
{
lean_object* v___x_1428_; 
v___x_1428_ = lean_obj_once(&l_Lake_Toml_trailingSep___closed__1, &l_Lake_Toml_trailingSep___closed__1_once, _init_l_Lake_Toml_trailingSep___closed__1);
return v___x_1428_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_unquotedKeyFn___lam__0(uint32_t v_c_1429_){
_start:
{
uint8_t v___y_1431_; uint8_t v___y_1437_; uint32_t v___x_1447_; uint8_t v___x_1448_; 
v___x_1447_ = 65;
v___x_1448_ = lean_uint32_dec_le(v___x_1447_, v_c_1429_);
if (v___x_1448_ == 0)
{
goto v___jp_1442_;
}
else
{
uint32_t v___x_1449_; uint8_t v___x_1450_; 
v___x_1449_ = 90;
v___x_1450_ = lean_uint32_dec_le(v_c_1429_, v___x_1449_);
if (v___x_1450_ == 0)
{
goto v___jp_1442_;
}
else
{
return v___x_1450_;
}
}
v___jp_1430_:
{
if (v___y_1431_ == 0)
{
uint32_t v___x_1432_; uint8_t v___x_1433_; 
v___x_1432_ = 95;
v___x_1433_ = lean_uint32_dec_eq(v_c_1429_, v___x_1432_);
if (v___x_1433_ == 0)
{
uint32_t v___x_1434_; uint8_t v___x_1435_; 
v___x_1434_ = 45;
v___x_1435_ = lean_uint32_dec_eq(v_c_1429_, v___x_1434_);
return v___x_1435_;
}
else
{
return v___x_1433_;
}
}
else
{
return v___y_1431_;
}
}
v___jp_1436_:
{
if (v___y_1437_ == 0)
{
uint32_t v___x_1438_; uint8_t v___x_1439_; 
v___x_1438_ = 48;
v___x_1439_ = lean_uint32_dec_le(v___x_1438_, v_c_1429_);
if (v___x_1439_ == 0)
{
v___y_1431_ = v___x_1439_;
goto v___jp_1430_;
}
else
{
uint32_t v___x_1440_; uint8_t v___x_1441_; 
v___x_1440_ = 57;
v___x_1441_ = lean_uint32_dec_le(v_c_1429_, v___x_1440_);
v___y_1431_ = v___x_1441_;
goto v___jp_1430_;
}
}
else
{
return v___y_1437_;
}
}
v___jp_1442_:
{
uint32_t v___x_1443_; uint8_t v___x_1444_; 
v___x_1443_ = 97;
v___x_1444_ = lean_uint32_dec_le(v___x_1443_, v_c_1429_);
if (v___x_1444_ == 0)
{
v___y_1437_ = v___x_1444_;
goto v___jp_1436_;
}
else
{
uint32_t v___x_1445_; uint8_t v___x_1446_; 
v___x_1445_ = 122;
v___x_1446_ = lean_uint32_dec_le(v_c_1429_, v___x_1445_);
v___y_1437_ = v___x_1446_;
goto v___jp_1436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn___lam__0___boxed(lean_object* v_c_1451_){
_start:
{
uint32_t v_c_boxed_1452_; uint8_t v_res_1453_; lean_object* v_r_1454_; 
v_c_boxed_1452_ = lean_unbox_uint32(v_c_1451_);
lean_dec(v_c_1451_);
v_res_1453_ = l_Lake_Toml_unquotedKeyFn___lam__0(v_c_boxed_1452_);
v_r_1454_ = lean_box(v_res_1453_);
return v_r_1454_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn(lean_object* v_a_1460_, lean_object* v_a_1461_){
_start:
{
lean_object* v___f_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___f_1462_ = ((lean_object*)(l_Lake_Toml_unquotedKeyFn___closed__0));
v___x_1463_ = ((lean_object*)(l_Lake_Toml_unquotedKeyFn___closed__2));
v___x_1464_ = l_Lake_Toml_takeWhile1Fn(v___f_1462_, v___x_1463_, v_a_1460_, v_a_1461_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn___boxed(lean_object* v_a_1465_, lean_object* v_a_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_Lake_Toml_unquotedKeyFn(v_a_1465_, v_a_1466_);
lean_dec_ref(v_a_1465_);
return v_res_1467_;
}
}
static lean_object* _init_l_Lake_Toml_unquotedKey___closed__2(void){
_start:
{
uint8_t v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
v___x_1473_ = 0;
v___x_1474_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1475_ = lean_alloc_closure((void*)(l_Lake_Toml_unquotedKeyFn___boxed), 2, 0);
v___x_1476_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__1));
v___x_1477_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__0));
v___x_1478_ = l_Lake_Toml_litWithAntiquot(v___x_1477_, v___x_1476_, v___x_1475_, v___x_1474_, v___x_1473_);
return v___x_1478_;
}
}
static lean_object* _init_l_Lake_Toml_unquotedKey(void){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = lean_obj_once(&l_Lake_Toml_unquotedKey___closed__2, &l_Lake_Toml_unquotedKey___closed__2_once, _init_l_Lake_Toml_unquotedKey___closed__2);
return v___x_1479_;
}
}
static lean_object* _init_l_Lake_Toml_basicString___closed__2(void){
_start:
{
uint8_t v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1489_; lean_object* v___x_1490_; 
v___x_1485_ = 0;
v___x_1486_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1487_ = lean_alloc_closure((void*)(l_Lake_Toml_basicStringFn), 2, 0);
v___x_1488_ = ((lean_object*)(l_Lake_Toml_basicString___closed__1));
v___x_1489_ = ((lean_object*)(l_Lake_Toml_basicString___closed__0));
v___x_1490_ = l_Lake_Toml_litWithAntiquot(v___x_1489_, v___x_1488_, v___x_1487_, v___x_1486_, v___x_1485_);
return v___x_1490_;
}
}
static lean_object* _init_l_Lake_Toml_basicString(void){
_start:
{
lean_object* v___x_1491_; 
v___x_1491_ = lean_obj_once(&l_Lake_Toml_basicString___closed__2, &l_Lake_Toml_basicString___closed__2_once, _init_l_Lake_Toml_basicString___closed__2);
return v___x_1491_;
}
}
static lean_object* _init_l_Lake_Toml_literalString___closed__2(void){
_start:
{
uint8_t v___x_1497_; lean_object* v___x_1498_; lean_object* v___x_1499_; lean_object* v___x_1500_; lean_object* v___x_1501_; lean_object* v___x_1502_; 
v___x_1497_ = 0;
v___x_1498_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1499_ = lean_alloc_closure((void*)(l_Lake_Toml_literalStringFn___boxed), 2, 0);
v___x_1500_ = ((lean_object*)(l_Lake_Toml_literalString___closed__1));
v___x_1501_ = ((lean_object*)(l_Lake_Toml_literalString___closed__0));
v___x_1502_ = l_Lake_Toml_litWithAntiquot(v___x_1501_, v___x_1500_, v___x_1499_, v___x_1498_, v___x_1497_);
return v___x_1502_;
}
}
static lean_object* _init_l_Lake_Toml_literalString(void){
_start:
{
lean_object* v___x_1503_; 
v___x_1503_ = lean_obj_once(&l_Lake_Toml_literalString___closed__2, &l_Lake_Toml_literalString___closed__2_once, _init_l_Lake_Toml_literalString___closed__2);
return v___x_1503_;
}
}
static lean_object* _init_l_Lake_Toml_mlBasicString___closed__2(void){
_start:
{
uint8_t v___x_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1514_; 
v___x_1509_ = 0;
v___x_1510_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1511_ = lean_alloc_closure((void*)(l_Lake_Toml_mlBasicStringFn), 2, 0);
v___x_1512_ = ((lean_object*)(l_Lake_Toml_mlBasicString___closed__1));
v___x_1513_ = ((lean_object*)(l_Lake_Toml_mlBasicString___closed__0));
v___x_1514_ = l_Lake_Toml_litWithAntiquot(v___x_1513_, v___x_1512_, v___x_1511_, v___x_1510_, v___x_1509_);
return v___x_1514_;
}
}
static lean_object* _init_l_Lake_Toml_mlBasicString(void){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = lean_obj_once(&l_Lake_Toml_mlBasicString___closed__2, &l_Lake_Toml_mlBasicString___closed__2_once, _init_l_Lake_Toml_mlBasicString___closed__2);
return v___x_1515_;
}
}
static lean_object* _init_l_Lake_Toml_mlLiteralString___closed__2(void){
_start:
{
uint8_t v___x_1521_; lean_object* v___x_1522_; lean_object* v___x_1523_; lean_object* v___x_1524_; lean_object* v___x_1525_; lean_object* v___x_1526_; 
v___x_1521_ = 0;
v___x_1522_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1523_ = lean_alloc_closure((void*)(l_Lake_Toml_mlLiteralStringFn), 2, 0);
v___x_1524_ = ((lean_object*)(l_Lake_Toml_mlLiteralString___closed__1));
v___x_1525_ = ((lean_object*)(l_Lake_Toml_mlLiteralString___closed__0));
v___x_1526_ = l_Lake_Toml_litWithAntiquot(v___x_1525_, v___x_1524_, v___x_1523_, v___x_1522_, v___x_1521_);
return v___x_1526_;
}
}
static lean_object* _init_l_Lake_Toml_mlLiteralString(void){
_start:
{
lean_object* v___x_1527_; 
v___x_1527_ = lean_obj_once(&l_Lake_Toml_mlLiteralString___closed__2, &l_Lake_Toml_mlLiteralString___closed__2_once, _init_l_Lake_Toml_mlLiteralString___closed__2);
return v___x_1527_;
}
}
static lean_object* _init_l_Lake_Toml_quotedKey___closed__0(void){
_start:
{
lean_object* v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; 
v___x_1528_ = l_Lake_Toml_literalString;
v___x_1529_ = l_Lake_Toml_basicString;
v___x_1530_ = l_Lean_Parser_orelse(v___x_1529_, v___x_1528_);
return v___x_1530_;
}
}
static lean_object* _init_l_Lake_Toml_quotedKey(void){
_start:
{
lean_object* v___x_1531_; 
v___x_1531_ = lean_obj_once(&l_Lake_Toml_quotedKey___closed__0, &l_Lake_Toml_quotedKey___closed__0_once, _init_l_Lake_Toml_quotedKey___closed__0);
return v___x_1531_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey___closed__2(void){
_start:
{
lean_object* v___x_1537_; lean_object* v___x_1538_; lean_object* v___x_1539_; 
v___x_1537_ = l_Lake_Toml_quotedKey;
v___x_1538_ = l_Lake_Toml_unquotedKey;
v___x_1539_ = l_Lean_Parser_orelse(v___x_1538_, v___x_1537_);
return v___x_1539_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey___closed__3(void){
_start:
{
uint8_t v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; 
v___x_1540_ = 1;
v___x_1541_ = lean_obj_once(&l_Lake_Toml_simpleKey___closed__2, &l_Lake_Toml_simpleKey___closed__2_once, _init_l_Lake_Toml_simpleKey___closed__2);
v___x_1542_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__1));
v___x_1543_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__0));
v___x_1544_ = l_Lean_Parser_nodeWithAntiquot(v___x_1543_, v___x_1542_, v___x_1541_, v___x_1540_);
return v___x_1544_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey(void){
_start:
{
lean_object* v___x_1545_; 
v___x_1545_ = lean_obj_once(&l_Lake_Toml_simpleKey___closed__3, &l_Lake_Toml_simpleKey___closed__3_once, _init_l_Lake_Toml_simpleKey___closed__3);
return v___x_1545_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__4(void){
_start:
{
uint32_t v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1555_ = 46;
v___x_1556_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_1557_ = lean_string_push(v___x_1556_, v___x_1555_);
return v___x_1557_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__5(void){
_start:
{
lean_object* v___x_1558_; lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1558_ = lean_obj_once(&l_Lake_Toml_key___closed__4, &l_Lake_Toml_key___closed__4_once, _init_l_Lake_Toml_key___closed__4);
v___x_1559_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1560_ = lean_string_append(v___x_1559_, v___x_1558_);
return v___x_1560_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__6(void){
_start:
{
lean_object* v___x_1561_; lean_object* v___x_1562_; lean_object* v___x_1563_; 
v___x_1561_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1562_ = lean_obj_once(&l_Lake_Toml_key___closed__5, &l_Lake_Toml_key___closed__5_once, _init_l_Lake_Toml_key___closed__5);
v___x_1563_ = lean_string_append(v___x_1562_, v___x_1561_);
return v___x_1563_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__7(void){
_start:
{
lean_object* v___x_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1564_ = lean_box(0);
v___x_1565_ = lean_obj_once(&l_Lake_Toml_key___closed__6, &l_Lake_Toml_key___closed__6_once, _init_l_Lake_Toml_key___closed__6);
v___x_1566_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1566_, 0, v___x_1565_);
lean_ctor_set(v___x_1566_, 1, v___x_1564_);
return v___x_1566_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__8(void){
_start:
{
lean_object* v___x_1567_; lean_object* v___x_1568_; uint32_t v___x_1569_; lean_object* v___x_1570_; 
v___x_1567_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1568_ = lean_obj_once(&l_Lake_Toml_key___closed__7, &l_Lake_Toml_key___closed__7_once, _init_l_Lake_Toml_key___closed__7);
v___x_1569_ = 46;
v___x_1570_ = l_Lake_Toml_chAtom(v___x_1569_, v___x_1568_, v___x_1567_);
return v___x_1570_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__9(void){
_start:
{
lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; 
v___x_1571_ = l_Lake_Toml_trailingWs;
v___x_1572_ = lean_obj_once(&l_Lake_Toml_key___closed__8, &l_Lake_Toml_key___closed__8_once, _init_l_Lake_Toml_key___closed__8);
v___x_1573_ = l_Lean_Parser_andthen(v___x_1572_, v___x_1571_);
return v___x_1573_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__10(void){
_start:
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1576_; 
v___x_1574_ = lean_obj_once(&l_Lake_Toml_key___closed__9, &l_Lake_Toml_key___closed__9_once, _init_l_Lake_Toml_key___closed__9);
v___x_1575_ = l_Lake_Toml_trailingWs;
v___x_1576_ = l_Lean_Parser_andthen(v___x_1575_, v___x_1574_);
return v___x_1576_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__11(void){
_start:
{
uint8_t v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; 
v___x_1577_ = 0;
v___x_1578_ = lean_obj_once(&l_Lake_Toml_key___closed__10, &l_Lake_Toml_key___closed__10_once, _init_l_Lake_Toml_key___closed__10);
v___x_1579_ = ((lean_object*)(l_Lake_Toml_key___closed__3));
v___x_1580_ = l_Lake_Toml_simpleKey;
v___x_1581_ = l_Lean_Parser_sepBy1(v___x_1580_, v___x_1579_, v___x_1578_, v___x_1577_);
return v___x_1581_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__12(void){
_start:
{
lean_object* v___x_1582_; lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1582_ = lean_obj_once(&l_Lake_Toml_key___closed__11, &l_Lake_Toml_key___closed__11_once, _init_l_Lake_Toml_key___closed__11);
v___x_1583_ = ((lean_object*)(l_Lake_Toml_key___closed__2));
v___x_1584_ = l_Lean_Parser_setExpected(v___x_1583_, v___x_1582_);
return v___x_1584_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__13(void){
_start:
{
uint8_t v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1589_; 
v___x_1585_ = 1;
v___x_1586_ = lean_obj_once(&l_Lake_Toml_key___closed__12, &l_Lake_Toml_key___closed__12_once, _init_l_Lake_Toml_key___closed__12);
v___x_1587_ = ((lean_object*)(l_Lake_Toml_key___closed__1));
v___x_1588_ = ((lean_object*)(l_Lake_Toml_key___closed__0));
v___x_1589_ = l_Lean_Parser_nodeWithAntiquot(v___x_1588_, v___x_1587_, v___x_1586_, v___x_1585_);
return v___x_1589_;
}
}
static lean_object* _init_l_Lake_Toml_key(void){
_start:
{
lean_object* v___x_1590_; 
v___x_1590_ = lean_obj_once(&l_Lake_Toml_key___closed__13, &l_Lake_Toml_key___closed__13_once, _init_l_Lake_Toml_key___closed__13);
return v___x_1590_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__4(void){
_start:
{
lean_object* v___x_1600_; lean_object* v___x_1601_; uint32_t v___x_1602_; lean_object* v___x_1603_; 
v___x_1600_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1601_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__3));
v___x_1602_ = 91;
v___x_1603_ = l_Lake_Toml_chAtom(v___x_1602_, v___x_1601_, v___x_1600_);
return v___x_1603_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__5(void){
_start:
{
uint32_t v___x_1604_; lean_object* v___x_1605_; lean_object* v___x_1606_; 
v___x_1604_ = 91;
v___x_1605_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_1606_ = lean_string_push(v___x_1605_, v___x_1604_);
return v___x_1606_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__6(void){
_start:
{
lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1609_; 
v___x_1607_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__5, &l_Lake_Toml_stdTable___closed__5_once, _init_l_Lake_Toml_stdTable___closed__5);
v___x_1608_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1609_ = lean_string_append(v___x_1608_, v___x_1607_);
return v___x_1609_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__7(void){
_start:
{
lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1610_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1611_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__6, &l_Lake_Toml_stdTable___closed__6_once, _init_l_Lake_Toml_stdTable___closed__6);
v___x_1612_ = lean_string_append(v___x_1611_, v___x_1610_);
return v___x_1612_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__8(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1613_ = lean_box(0);
v___x_1614_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__7, &l_Lake_Toml_stdTable___closed__7_once, _init_l_Lake_Toml_stdTable___closed__7);
v___x_1615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1615_, 0, v___x_1614_);
lean_ctor_set(v___x_1615_, 1, v___x_1613_);
return v___x_1615_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__9(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; uint32_t v___x_1618_; lean_object* v___x_1619_; 
v___x_1616_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1617_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__8, &l_Lake_Toml_stdTable___closed__8_once, _init_l_Lake_Toml_stdTable___closed__8);
v___x_1618_ = 91;
v___x_1619_ = l_Lake_Toml_chAtom(v___x_1618_, v___x_1617_, v___x_1616_);
return v___x_1619_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__11(void){
_start:
{
lean_object* v___x_1621_; lean_object* v___x_1622_; lean_object* v___x_1623_; 
v___x_1621_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__10));
v___x_1622_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__9, &l_Lake_Toml_stdTable___closed__9_once, _init_l_Lake_Toml_stdTable___closed__9);
v___x_1623_ = l_Lean_Parser_notFollowedBy(v___x_1622_, v___x_1621_);
return v___x_1623_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__12(void){
_start:
{
lean_object* v___x_1624_; lean_object* v___x_1625_; lean_object* v___x_1626_; 
v___x_1624_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__11, &l_Lake_Toml_stdTable___closed__11_once, _init_l_Lake_Toml_stdTable___closed__11);
v___x_1625_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__4, &l_Lake_Toml_stdTable___closed__4_once, _init_l_Lake_Toml_stdTable___closed__4);
v___x_1626_ = l_Lean_Parser_andthen(v___x_1625_, v___x_1624_);
return v___x_1626_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__13(void){
_start:
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
v___x_1627_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__12, &l_Lake_Toml_stdTable___closed__12_once, _init_l_Lake_Toml_stdTable___closed__12);
v___x_1628_ = l_Lean_Parser_atomic(v___x_1627_);
return v___x_1628_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__14(void){
_start:
{
uint32_t v___x_1629_; lean_object* v___x_1630_; lean_object* v___x_1631_; 
v___x_1629_ = 93;
v___x_1630_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_1631_ = lean_string_push(v___x_1630_, v___x_1629_);
return v___x_1631_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__15(void){
_start:
{
lean_object* v___x_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; 
v___x_1632_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__14, &l_Lake_Toml_stdTable___closed__14_once, _init_l_Lake_Toml_stdTable___closed__14);
v___x_1633_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1634_ = lean_string_append(v___x_1633_, v___x_1632_);
return v___x_1634_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__16(void){
_start:
{
lean_object* v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1635_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1636_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__15, &l_Lake_Toml_stdTable___closed__15_once, _init_l_Lake_Toml_stdTable___closed__15);
v___x_1637_ = lean_string_append(v___x_1636_, v___x_1635_);
return v___x_1637_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__17(void){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1638_ = lean_box(0);
v___x_1639_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__16, &l_Lake_Toml_stdTable___closed__16_once, _init_l_Lake_Toml_stdTable___closed__16);
v___x_1640_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1640_, 0, v___x_1639_);
lean_ctor_set(v___x_1640_, 1, v___x_1638_);
return v___x_1640_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__18(void){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; uint32_t v___x_1643_; lean_object* v___x_1644_; 
v___x_1641_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1642_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__17, &l_Lake_Toml_stdTable___closed__17_once, _init_l_Lake_Toml_stdTable___closed__17);
v___x_1643_ = 93;
v___x_1644_ = l_Lake_Toml_chAtom(v___x_1643_, v___x_1642_, v___x_1641_);
return v___x_1644_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__19(void){
_start:
{
lean_object* v___x_1645_; lean_object* v___x_1646_; lean_object* v___x_1647_; 
v___x_1645_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__18, &l_Lake_Toml_stdTable___closed__18_once, _init_l_Lake_Toml_stdTable___closed__18);
v___x_1646_ = l_Lake_Toml_trailingWs;
v___x_1647_ = l_Lean_Parser_andthen(v___x_1646_, v___x_1645_);
return v___x_1647_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__20(void){
_start:
{
lean_object* v___x_1648_; lean_object* v___x_1649_; lean_object* v___x_1650_; 
v___x_1648_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__19, &l_Lake_Toml_stdTable___closed__19_once, _init_l_Lake_Toml_stdTable___closed__19);
v___x_1649_ = l_Lake_Toml_key;
v___x_1650_ = l_Lean_Parser_andthen(v___x_1649_, v___x_1648_);
return v___x_1650_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__21(void){
_start:
{
lean_object* v___x_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; 
v___x_1651_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__20, &l_Lake_Toml_stdTable___closed__20_once, _init_l_Lake_Toml_stdTable___closed__20);
v___x_1652_ = l_Lake_Toml_trailingWs;
v___x_1653_ = l_Lean_Parser_andthen(v___x_1652_, v___x_1651_);
return v___x_1653_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__22(void){
_start:
{
lean_object* v___x_1654_; lean_object* v___x_1655_; lean_object* v___x_1656_; 
v___x_1654_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__21, &l_Lake_Toml_stdTable___closed__21_once, _init_l_Lake_Toml_stdTable___closed__21);
v___x_1655_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__13, &l_Lake_Toml_stdTable___closed__13_once, _init_l_Lake_Toml_stdTable___closed__13);
v___x_1656_ = l_Lean_Parser_andthen(v___x_1655_, v___x_1654_);
return v___x_1656_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__23(void){
_start:
{
uint8_t v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v___x_1657_ = 0;
v___x_1658_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__22, &l_Lake_Toml_stdTable___closed__22_once, _init_l_Lake_Toml_stdTable___closed__22);
v___x_1659_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__1));
v___x_1660_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__0));
v___x_1661_ = l_Lean_Parser_nodeWithAntiquot(v___x_1660_, v___x_1659_, v___x_1658_, v___x_1657_);
return v___x_1661_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable(void){
_start:
{
lean_object* v___x_1662_; 
v___x_1662_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__23, &l_Lake_Toml_stdTable___closed__23_once, _init_l_Lake_Toml_stdTable___closed__23);
return v___x_1662_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__2(void){
_start:
{
lean_object* v___x_1668_; lean_object* v___x_1669_; lean_object* v___x_1670_; 
v___x_1668_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__9, &l_Lake_Toml_stdTable___closed__9_once, _init_l_Lake_Toml_stdTable___closed__9);
v___x_1669_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__4, &l_Lake_Toml_stdTable___closed__4_once, _init_l_Lake_Toml_stdTable___closed__4);
v___x_1670_ = l_Lean_Parser_andthen(v___x_1669_, v___x_1668_);
return v___x_1670_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__3(void){
_start:
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__2, &l_Lake_Toml_arrayTable___closed__2_once, _init_l_Lake_Toml_arrayTable___closed__2);
v___x_1672_ = l_Lean_Parser_atomic(v___x_1671_);
return v___x_1672_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__4(void){
_start:
{
lean_object* v___x_1673_; lean_object* v___x_1674_; 
v___x_1673_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__18, &l_Lake_Toml_stdTable___closed__18_once, _init_l_Lake_Toml_stdTable___closed__18);
v___x_1674_ = l_Lean_Parser_andthen(v___x_1673_, v___x_1673_);
return v___x_1674_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__5(void){
_start:
{
lean_object* v___x_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
v___x_1675_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__4, &l_Lake_Toml_arrayTable___closed__4_once, _init_l_Lake_Toml_arrayTable___closed__4);
v___x_1676_ = l_Lake_Toml_trailingWs;
v___x_1677_ = l_Lean_Parser_andthen(v___x_1676_, v___x_1675_);
return v___x_1677_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__6(void){
_start:
{
lean_object* v___x_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; 
v___x_1678_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__5, &l_Lake_Toml_arrayTable___closed__5_once, _init_l_Lake_Toml_arrayTable___closed__5);
v___x_1679_ = l_Lake_Toml_key;
v___x_1680_ = l_Lean_Parser_andthen(v___x_1679_, v___x_1678_);
return v___x_1680_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__7(void){
_start:
{
lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; 
v___x_1681_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__6, &l_Lake_Toml_arrayTable___closed__6_once, _init_l_Lake_Toml_arrayTable___closed__6);
v___x_1682_ = l_Lake_Toml_trailingWs;
v___x_1683_ = l_Lean_Parser_andthen(v___x_1682_, v___x_1681_);
return v___x_1683_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__8(void){
_start:
{
lean_object* v___x_1684_; lean_object* v___x_1685_; lean_object* v___x_1686_; 
v___x_1684_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__7, &l_Lake_Toml_arrayTable___closed__7_once, _init_l_Lake_Toml_arrayTable___closed__7);
v___x_1685_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__3, &l_Lake_Toml_arrayTable___closed__3_once, _init_l_Lake_Toml_arrayTable___closed__3);
v___x_1686_ = l_Lean_Parser_andthen(v___x_1685_, v___x_1684_);
return v___x_1686_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__9(void){
_start:
{
uint8_t v___x_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; 
v___x_1687_ = 0;
v___x_1688_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__8, &l_Lake_Toml_arrayTable___closed__8_once, _init_l_Lake_Toml_arrayTable___closed__8);
v___x_1689_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__1));
v___x_1690_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__0));
v___x_1691_ = l_Lean_Parser_nodeWithAntiquot(v___x_1690_, v___x_1689_, v___x_1688_, v___x_1687_);
return v___x_1691_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable(void){
_start:
{
lean_object* v___x_1692_; 
v___x_1692_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__9, &l_Lake_Toml_arrayTable___closed__9_once, _init_l_Lake_Toml_arrayTable___closed__9);
return v___x_1692_;
}
}
static lean_object* _init_l_Lake_Toml_table___closed__0(void){
_start:
{
lean_object* v___x_1693_; lean_object* v___x_1694_; lean_object* v___x_1695_; 
v___x_1693_ = l_Lake_Toml_arrayTable;
v___x_1694_ = l_Lake_Toml_stdTable;
v___x_1695_ = l_Lean_Parser_orelse(v___x_1694_, v___x_1693_);
return v___x_1695_;
}
}
static lean_object* _init_l_Lake_Toml_table(void){
_start:
{
lean_object* v___x_1696_; 
v___x_1696_ = lean_obj_once(&l_Lake_Toml_table___closed__0, &l_Lake_Toml_table___closed__0_once, _init_l_Lake_Toml_table___closed__0);
return v___x_1696_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2(void){
_start:
{
uint32_t v___x_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
v___x_1702_ = 61;
v___x_1703_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_1704_ = lean_string_push(v___x_1703_, v___x_1702_);
return v___x_1704_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3(void){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; lean_object* v___x_1707_; 
v___x_1705_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2);
v___x_1706_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1707_ = lean_string_append(v___x_1706_, v___x_1705_);
return v___x_1707_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4(void){
_start:
{
lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1710_; 
v___x_1708_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1709_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3);
v___x_1710_ = lean_string_append(v___x_1709_, v___x_1708_);
return v___x_1710_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5(void){
_start:
{
lean_object* v___x_1711_; lean_object* v___x_1712_; lean_object* v___x_1713_; 
v___x_1711_ = lean_box(0);
v___x_1712_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4);
v___x_1713_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1713_, 0, v___x_1712_);
lean_ctor_set(v___x_1713_, 1, v___x_1711_);
return v___x_1713_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6(void){
_start:
{
lean_object* v___x_1714_; lean_object* v___x_1715_; uint32_t v___x_1716_; lean_object* v___x_1717_; 
v___x_1714_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1715_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5);
v___x_1716_ = 61;
v___x_1717_ = l_Lake_Toml_chAtom(v___x_1716_, v___x_1715_, v___x_1714_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(lean_object* v_val_1718_){
_start:
{
lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; lean_object* v___x_1723_; lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; lean_object* v___x_1727_; uint8_t v___x_1728_; lean_object* v___x_1729_; 
v___x_1719_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0));
v___x_1720_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1));
v___x_1721_ = l_Lake_Toml_key;
v___x_1722_ = l_Lake_Toml_trailingWs;
v___x_1723_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6);
v___x_1724_ = l_Lean_Parser_andthen(v___x_1722_, v_val_1718_);
v___x_1725_ = l_Lean_Parser_andthen(v___x_1723_, v___x_1724_);
v___x_1726_ = l_Lean_Parser_andthen(v___x_1722_, v___x_1725_);
v___x_1727_ = l_Lean_Parser_andthen(v___x_1721_, v___x_1726_);
v___x_1728_ = 1;
v___x_1729_ = l_Lean_Parser_nodeWithAntiquot(v___x_1719_, v___x_1720_, v___x_1727_, v___x_1728_);
return v___x_1729_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2(void){
_start:
{
uint8_t v___x_1735_; lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1735_ = 1;
v___x_1736_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1));
v___x_1737_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0));
v___x_1738_ = l_Lean_Parser_mkAntiquot(v___x_1737_, v___x_1736_, v___x_1735_, v___x_1735_);
return v___x_1738_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(lean_object* v_val_1739_){
_start:
{
lean_object* v___x_1740_; lean_object* v___x_1741_; lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1740_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2, &l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2);
v___x_1741_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(v_val_1739_);
v___x_1742_ = l_Lake_Toml_table;
v___x_1743_ = l_Lean_Parser_orelse(v___x_1741_, v___x_1742_);
v___x_1744_ = l_Lean_Parser_withAntiquot(v___x_1740_, v___x_1743_);
return v___x_1744_;
}
}
static lean_object* _init_l_Lake_Toml_header___closed__2(void){
_start:
{
uint8_t v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; 
v___x_1750_ = 0;
v___x_1751_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1752_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1753_ = ((lean_object*)(l_Lake_Toml_header___closed__1));
v___x_1754_ = ((lean_object*)(l_Lake_Toml_header___closed__0));
v___x_1755_ = l_Lake_Toml_litWithAntiquot(v___x_1754_, v___x_1753_, v___x_1752_, v___x_1751_, v___x_1750_);
return v___x_1755_;
}
}
static lean_object* _init_l_Lake_Toml_header(void){
_start:
{
lean_object* v___x_1756_; 
v___x_1756_ = lean_obj_once(&l_Lake_Toml_header___closed__2, &l_Lake_Toml_header___closed__2_once, _init_l_Lake_Toml_header___closed__2);
return v___x_1756_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5(void){
_start:
{
lean_object* v___x_1766_; lean_object* v___x_1767_; 
v___x_1766_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__4));
v___x_1767_ = l_Lean_Parser_symbol(v___x_1766_);
return v___x_1767_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7(void){
_start:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
v___x_1769_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__6));
v___x_1770_ = l_Lean_Parser_checkLinebreakBefore(v___x_1769_);
return v___x_1770_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8(void){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; 
v___x_1771_ = l_Lean_Parser_pushNone;
v___x_1772_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7, &l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7);
v___x_1773_ = l_Lean_Parser_andthen(v___x_1772_, v___x_1771_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore(lean_object* v_val_1774_){
_start:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; lean_object* v___x_1778_; lean_object* v___x_1779_; lean_object* v___x_1780_; uint8_t v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v_p_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; 
v___x_1775_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0));
v___x_1776_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1));
v___x_1777_ = l_Lake_Toml_header;
v___x_1778_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(v_val_1774_);
v___x_1779_ = l_Lake_Toml_trailingSep;
v___x_1780_ = l_Lean_Parser_andthen(v___x_1778_, v___x_1779_);
v___x_1781_ = 1;
v___x_1782_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__3));
v___x_1783_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5);
v_p_1784_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1782_, v___x_1780_, v___x_1783_);
v___x_1785_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8, &l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8);
v___x_1786_ = l_Lean_Parser_sepByNoAntiquot(v_p_1784_, v___x_1785_, v___x_1781_);
v___x_1787_ = l_Lean_Parser_andthen(v___x_1777_, v___x_1786_);
v___x_1788_ = l_Lean_Parser_nodeWithAntiquot(v___x_1775_, v___x_1776_, v___x_1787_, v___x_1781_);
return v___x_1788_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4(void){
_start:
{
lean_object* v___x_1798_; lean_object* v___x_1799_; uint32_t v___x_1800_; lean_object* v___x_1801_; 
v___x_1798_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1799_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__3));
v___x_1800_ = 123;
v___x_1801_ = l_Lake_Toml_chAtom(v___x_1800_, v___x_1799_, v___x_1798_);
return v___x_1801_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6(void){
_start:
{
uint32_t v___x_1803_; lean_object* v___x_1804_; lean_object* v___x_1805_; 
v___x_1803_ = 44;
v___x_1804_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_1805_ = lean_string_push(v___x_1804_, v___x_1803_);
return v___x_1805_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7(void){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; 
v___x_1806_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6);
v___x_1807_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1808_ = lean_string_append(v___x_1807_, v___x_1806_);
return v___x_1808_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8(void){
_start:
{
lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; 
v___x_1809_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1810_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7);
v___x_1811_ = lean_string_append(v___x_1810_, v___x_1809_);
return v___x_1811_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9(void){
_start:
{
lean_object* v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; 
v___x_1812_ = lean_box(0);
v___x_1813_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8);
v___x_1814_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1814_, 0, v___x_1813_);
lean_ctor_set(v___x_1814_, 1, v___x_1812_);
return v___x_1814_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10(void){
_start:
{
lean_object* v___x_1815_; lean_object* v___x_1816_; uint32_t v___x_1817_; lean_object* v___x_1818_; 
v___x_1815_ = lean_alloc_closure((void*)(l_Lake_Toml_wsFn___boxed), 2, 0);
v___x_1816_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9);
v___x_1817_ = 44;
v___x_1818_ = l_Lake_Toml_chAtom(v___x_1817_, v___x_1816_, v___x_1815_);
return v___x_1818_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11(void){
_start:
{
uint32_t v___x_1819_; lean_object* v___x_1820_; lean_object* v___x_1821_; 
v___x_1819_ = 125;
v___x_1820_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_1821_ = lean_string_push(v___x_1820_, v___x_1819_);
return v___x_1821_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12(void){
_start:
{
lean_object* v___x_1822_; lean_object* v___x_1823_; lean_object* v___x_1824_; 
v___x_1822_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11);
v___x_1823_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1824_ = lean_string_append(v___x_1823_, v___x_1822_);
return v___x_1824_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13(void){
_start:
{
lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; 
v___x_1825_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1826_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12);
v___x_1827_ = lean_string_append(v___x_1826_, v___x_1825_);
return v___x_1827_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14(void){
_start:
{
lean_object* v___x_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; 
v___x_1828_ = lean_box(0);
v___x_1829_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13);
v___x_1830_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1830_, 0, v___x_1829_);
lean_ctor_set(v___x_1830_, 1, v___x_1828_);
return v___x_1830_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15(void){
_start:
{
lean_object* v___x_1831_; lean_object* v___x_1832_; uint32_t v___x_1833_; lean_object* v___x_1834_; 
v___x_1831_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1832_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14);
v___x_1833_ = 125;
v___x_1834_ = l_Lake_Toml_chAtom(v___x_1833_, v___x_1832_, v___x_1831_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(lean_object* v_val_1835_){
_start:
{
lean_object* v___x_1836_; lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; lean_object* v___x_1843_; uint8_t v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1849_; 
v___x_1836_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0));
v___x_1837_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1));
v___x_1838_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4);
v___x_1839_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(v_val_1835_);
v___x_1840_ = l_Lake_Toml_trailingWs;
v___x_1841_ = l_Lean_Parser_andthen(v___x_1839_, v___x_1840_);
v___x_1842_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5));
v___x_1843_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10);
v___x_1844_ = 0;
v___x_1845_ = l_Lean_Parser_sepBy(v___x_1841_, v___x_1842_, v___x_1843_, v___x_1844_);
v___x_1846_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15);
v___x_1847_ = l_Lean_Parser_andthen(v___x_1845_, v___x_1846_);
v___x_1848_ = l_Lean_Parser_andthen(v___x_1838_, v___x_1847_);
v___x_1849_ = l_Lean_Parser_nodeWithAntiquot(v___x_1836_, v___x_1837_, v___x_1848_, v___x_1844_);
return v___x_1849_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3(void){
_start:
{
lean_object* v___x_1858_; lean_object* v___x_1859_; uint32_t v___x_1860_; lean_object* v___x_1861_; 
v___x_1858_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1859_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__2));
v___x_1860_ = 91;
v___x_1861_ = l_Lake_Toml_chAtom(v___x_1860_, v___x_1859_, v___x_1858_);
return v___x_1861_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4(void){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; uint32_t v___x_1864_; lean_object* v___x_1865_; 
v___x_1862_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1863_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9);
v___x_1864_ = 44;
v___x_1865_ = l_Lake_Toml_chAtom(v___x_1864_, v___x_1863_, v___x_1862_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(lean_object* v_val_1866_){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; uint8_t v___x_1874_; lean_object* v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; uint8_t v___x_1879_; lean_object* v___x_1880_; 
v___x_1867_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0));
v___x_1868_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1));
v___x_1869_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3, &l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3);
v___x_1870_ = l_Lake_Toml_trailingSep;
v___x_1871_ = l_Lean_Parser_andthen(v_val_1866_, v___x_1870_);
v___x_1872_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5));
v___x_1873_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4, &l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4);
v___x_1874_ = 1;
v___x_1875_ = l_Lean_Parser_sepBy(v___x_1871_, v___x_1872_, v___x_1873_, v___x_1874_);
v___x_1876_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__18, &l_Lake_Toml_stdTable___closed__18_once, _init_l_Lake_Toml_stdTable___closed__18);
v___x_1877_ = l_Lean_Parser_andthen(v___x_1875_, v___x_1876_);
v___x_1878_ = l_Lean_Parser_andthen(v___x_1869_, v___x_1877_);
v___x_1879_ = 0;
v___x_1880_ = l_Lean_Parser_nodeWithAntiquot(v___x_1867_, v___x_1868_, v___x_1878_, v___x_1879_);
return v___x_1880_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__3(void){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; lean_object* v___x_1891_; 
v___x_1889_ = l_Lake_Toml_literalString;
v___x_1890_ = l_Lake_Toml_mlLiteralString;
v___x_1891_ = l_Lean_Parser_orelse(v___x_1890_, v___x_1889_);
return v___x_1891_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__4(void){
_start:
{
lean_object* v___x_1892_; lean_object* v___x_1893_; lean_object* v___x_1894_; 
v___x_1892_ = lean_obj_once(&l_Lake_Toml_string___closed__3, &l_Lake_Toml_string___closed__3_once, _init_l_Lake_Toml_string___closed__3);
v___x_1893_ = l_Lake_Toml_basicString;
v___x_1894_ = l_Lean_Parser_orelse(v___x_1893_, v___x_1892_);
return v___x_1894_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__5(void){
_start:
{
lean_object* v___x_1895_; lean_object* v___x_1896_; lean_object* v___x_1897_; 
v___x_1895_ = lean_obj_once(&l_Lake_Toml_string___closed__4, &l_Lake_Toml_string___closed__4_once, _init_l_Lake_Toml_string___closed__4);
v___x_1896_ = l_Lake_Toml_mlBasicString;
v___x_1897_ = l_Lean_Parser_orelse(v___x_1896_, v___x_1895_);
return v___x_1897_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__6(void){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1898_ = lean_obj_once(&l_Lake_Toml_string___closed__5, &l_Lake_Toml_string___closed__5_once, _init_l_Lake_Toml_string___closed__5);
v___x_1899_ = ((lean_object*)(l_Lake_Toml_string___closed__2));
v___x_1900_ = l_Lean_Parser_setExpected(v___x_1899_, v___x_1898_);
return v___x_1900_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__7(void){
_start:
{
uint8_t v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; 
v___x_1901_ = 0;
v___x_1902_ = lean_obj_once(&l_Lake_Toml_string___closed__6, &l_Lake_Toml_string___closed__6_once, _init_l_Lake_Toml_string___closed__6);
v___x_1903_ = ((lean_object*)(l_Lake_Toml_string___closed__1));
v___x_1904_ = ((lean_object*)(l_Lake_Toml_string___closed__0));
v___x_1905_ = l_Lean_Parser_nodeWithAntiquot(v___x_1904_, v___x_1903_, v___x_1902_, v___x_1901_);
return v___x_1905_;
}
}
static lean_object* _init_l_Lake_Toml_string(void){
_start:
{
lean_object* v___x_1906_; 
v___x_1906_ = lean_obj_once(&l_Lake_Toml_string___closed__7, &l_Lake_Toml_string___closed__7_once, _init_l_Lake_Toml_string___closed__7);
return v___x_1906_;
}
}
static lean_object* _init_l_Lake_Toml_true___closed__5(void){
_start:
{
lean_object* v___x_1919_; lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1919_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1920_ = ((lean_object*)(l_Lake_Toml_true___closed__4));
v___x_1921_ = ((lean_object*)(l_Lake_Toml_true___closed__1));
v___x_1922_ = l_Lake_Toml_lit(v___x_1921_, v___x_1920_, v___x_1919_);
return v___x_1922_;
}
}
static lean_object* _init_l_Lake_Toml_true(void){
_start:
{
lean_object* v___x_1923_; 
v___x_1923_ = lean_obj_once(&l_Lake_Toml_true___closed__5, &l_Lake_Toml_true___closed__5_once, _init_l_Lake_Toml_true___closed__5);
return v___x_1923_;
}
}
static lean_object* _init_l_Lake_Toml_false___closed__5(void){
_start:
{
lean_object* v___x_1936_; lean_object* v___x_1937_; lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1936_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1937_ = ((lean_object*)(l_Lake_Toml_false___closed__4));
v___x_1938_ = ((lean_object*)(l_Lake_Toml_false___closed__1));
v___x_1939_ = l_Lake_Toml_lit(v___x_1938_, v___x_1937_, v___x_1936_);
return v___x_1939_;
}
}
static lean_object* _init_l_Lake_Toml_false(void){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = lean_obj_once(&l_Lake_Toml_false___closed__5, &l_Lake_Toml_false___closed__5_once, _init_l_Lake_Toml_false___closed__5);
return v___x_1940_;
}
}
static lean_object* _init_l_Lake_Toml_boolean___closed__2(void){
_start:
{
lean_object* v___x_1946_; lean_object* v___x_1947_; lean_object* v___x_1948_; 
v___x_1946_ = l_Lake_Toml_false;
v___x_1947_ = l_Lake_Toml_true;
v___x_1948_ = l_Lean_Parser_orelse(v___x_1947_, v___x_1946_);
return v___x_1948_;
}
}
static lean_object* _init_l_Lake_Toml_boolean___closed__3(void){
_start:
{
uint8_t v___x_1949_; lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1949_ = 0;
v___x_1950_ = lean_obj_once(&l_Lake_Toml_boolean___closed__2, &l_Lake_Toml_boolean___closed__2_once, _init_l_Lake_Toml_boolean___closed__2);
v___x_1951_ = ((lean_object*)(l_Lake_Toml_boolean___closed__1));
v___x_1952_ = ((lean_object*)(l_Lake_Toml_boolean___closed__0));
v___x_1953_ = l_Lean_Parser_nodeWithAntiquot(v___x_1952_, v___x_1951_, v___x_1950_, v___x_1949_);
return v___x_1953_;
}
}
static lean_object* _init_l_Lake_Toml_boolean(void){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = lean_obj_once(&l_Lake_Toml_boolean___closed__3, &l_Lake_Toml_boolean___closed__3_once, _init_l_Lake_Toml_boolean___closed__3);
return v___x_1954_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__0(void){
_start:
{
uint8_t v___x_1955_; lean_object* v___x_1956_; lean_object* v___x_1957_; lean_object* v___x_1958_; 
v___x_1955_ = 0;
v___x_1956_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_1957_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2));
v___x_1958_ = l_Lean_Parser_mkAntiquot(v___x_1957_, v___x_1956_, v___x_1955_, v___x_1955_);
return v___x_1958_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__1(void){
_start:
{
uint8_t v___x_1959_; lean_object* v___x_1960_; lean_object* v___x_1961_; lean_object* v___x_1962_; 
v___x_1959_ = 0;
v___x_1960_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1961_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5));
v___x_1962_ = l_Lean_Parser_mkAntiquot(v___x_1961_, v___x_1960_, v___x_1959_, v___x_1959_);
return v___x_1962_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__2(void){
_start:
{
uint8_t v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; lean_object* v___x_1966_; 
v___x_1963_ = 0;
v___x_1964_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__17));
v___x_1965_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__16));
v___x_1966_ = l_Lean_Parser_mkAntiquot(v___x_1965_, v___x_1964_, v___x_1963_, v___x_1963_);
return v___x_1966_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__3(void){
_start:
{
uint8_t v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1967_ = 0;
v___x_1968_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__12));
v___x_1969_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__11));
v___x_1970_ = l_Lean_Parser_mkAntiquot(v___x_1969_, v___x_1968_, v___x_1967_, v___x_1967_);
return v___x_1970_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__4(void){
_start:
{
uint8_t v___x_1971_; lean_object* v___x_1972_; lean_object* v___x_1973_; lean_object* v___x_1974_; 
v___x_1971_ = 0;
v___x_1972_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__7));
v___x_1973_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__6));
v___x_1974_ = l_Lean_Parser_mkAntiquot(v___x_1973_, v___x_1972_, v___x_1971_, v___x_1971_);
return v___x_1974_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__5(void){
_start:
{
uint8_t v___x_1975_; lean_object* v___x_1976_; lean_object* v___x_1977_; lean_object* v___x_1978_; 
v___x_1975_ = 0;
v___x_1976_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_1977_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0));
v___x_1978_ = l_Lean_Parser_mkAntiquot(v___x_1977_, v___x_1976_, v___x_1975_, v___x_1975_);
return v___x_1978_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__8(void){
_start:
{
uint8_t v___x_1984_; lean_object* v___x_1985_; lean_object* v___x_1986_; lean_object* v___x_1987_; 
v___x_1984_ = 1;
v___x_1985_ = ((lean_object*)(l_Lake_Toml_numeralAntiquot___closed__7));
v___x_1986_ = ((lean_object*)(l_Lake_Toml_numeralAntiquot___closed__6));
v___x_1987_ = l_Lean_Parser_mkAntiquot(v___x_1986_, v___x_1985_, v___x_1984_, v___x_1984_);
return v___x_1987_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__9(void){
_start:
{
lean_object* v___x_1988_; lean_object* v___x_1989_; lean_object* v___x_1990_; 
v___x_1988_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__8, &l_Lake_Toml_numeralAntiquot___closed__8_once, _init_l_Lake_Toml_numeralAntiquot___closed__8);
v___x_1989_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__5, &l_Lake_Toml_numeralAntiquot___closed__5_once, _init_l_Lake_Toml_numeralAntiquot___closed__5);
v___x_1990_ = l_Lean_Parser_orelse(v___x_1989_, v___x_1988_);
return v___x_1990_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__10(void){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1991_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__9, &l_Lake_Toml_numeralAntiquot___closed__9_once, _init_l_Lake_Toml_numeralAntiquot___closed__9);
v___x_1992_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__4, &l_Lake_Toml_numeralAntiquot___closed__4_once, _init_l_Lake_Toml_numeralAntiquot___closed__4);
v___x_1993_ = l_Lean_Parser_orelse(v___x_1992_, v___x_1991_);
return v___x_1993_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__11(void){
_start:
{
lean_object* v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; 
v___x_1994_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__10, &l_Lake_Toml_numeralAntiquot___closed__10_once, _init_l_Lake_Toml_numeralAntiquot___closed__10);
v___x_1995_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__3, &l_Lake_Toml_numeralAntiquot___closed__3_once, _init_l_Lake_Toml_numeralAntiquot___closed__3);
v___x_1996_ = l_Lean_Parser_orelse(v___x_1995_, v___x_1994_);
return v___x_1996_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__12(void){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; lean_object* v___x_1999_; 
v___x_1997_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__11, &l_Lake_Toml_numeralAntiquot___closed__11_once, _init_l_Lake_Toml_numeralAntiquot___closed__11);
v___x_1998_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__2, &l_Lake_Toml_numeralAntiquot___closed__2_once, _init_l_Lake_Toml_numeralAntiquot___closed__2);
v___x_1999_ = l_Lean_Parser_orelse(v___x_1998_, v___x_1997_);
return v___x_1999_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__13(void){
_start:
{
lean_object* v___x_2000_; lean_object* v___x_2001_; lean_object* v___x_2002_; 
v___x_2000_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__12, &l_Lake_Toml_numeralAntiquot___closed__12_once, _init_l_Lake_Toml_numeralAntiquot___closed__12);
v___x_2001_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__1, &l_Lake_Toml_numeralAntiquot___closed__1_once, _init_l_Lake_Toml_numeralAntiquot___closed__1);
v___x_2002_ = l_Lean_Parser_orelse(v___x_2001_, v___x_2000_);
return v___x_2002_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__14(void){
_start:
{
lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2003_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__13, &l_Lake_Toml_numeralAntiquot___closed__13_once, _init_l_Lake_Toml_numeralAntiquot___closed__13);
v___x_2004_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__0, &l_Lake_Toml_numeralAntiquot___closed__0_once, _init_l_Lake_Toml_numeralAntiquot___closed__0);
v___x_2005_ = l_Lean_Parser_orelse(v___x_2004_, v___x_2003_);
return v___x_2005_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot(void){
_start:
{
lean_object* v___x_2006_; 
v___x_2006_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__14, &l_Lake_Toml_numeralAntiquot___closed__14_once, _init_l_Lake_Toml_numeralAntiquot___closed__14);
return v___x_2006_;
}
}
static lean_object* _init_l_Lake_Toml_numeral___closed__0(void){
_start:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = lean_alloc_closure((void*)(l_Lake_Toml_numeralFn), 2, 0);
v___x_2008_ = l_Lake_Toml_dynamicNode(v___x_2007_);
return v___x_2008_;
}
}
static lean_object* _init_l_Lake_Toml_numeral___closed__1(void){
_start:
{
lean_object* v___x_2009_; lean_object* v___x_2010_; lean_object* v___x_2011_; 
v___x_2009_ = lean_obj_once(&l_Lake_Toml_numeral___closed__0, &l_Lake_Toml_numeral___closed__0_once, _init_l_Lake_Toml_numeral___closed__0);
v___x_2010_ = l_Lake_Toml_numeralAntiquot;
v___x_2011_ = l_Lean_Parser_withAntiquot(v___x_2010_, v___x_2009_);
return v___x_2011_;
}
}
static lean_object* _init_l_Lake_Toml_numeral(void){
_start:
{
lean_object* v___x_2012_; 
v___x_2012_ = lean_obj_once(&l_Lake_Toml_numeral___closed__1, &l_Lake_Toml_numeral___closed__1_once, _init_l_Lake_Toml_numeral___closed__1);
return v___x_2012_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_numeralOfKind___lam__0(lean_object* v_kind_2013_, lean_object* v_x_2014_){
_start:
{
uint8_t v___x_2015_; 
v___x_2015_ = l_Lean_Syntax_isOfKind(v_x_2014_, v_kind_2013_);
return v___x_2015_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralOfKind___lam__0___boxed(lean_object* v_kind_2016_, lean_object* v_x_2017_){
_start:
{
uint8_t v_res_2018_; lean_object* v_r_2019_; 
v_res_2018_ = l_Lake_Toml_numeralOfKind___lam__0(v_kind_2016_, v_x_2017_);
lean_dec(v_kind_2016_);
v_r_2019_ = lean_box(v_res_2018_);
return v_r_2019_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralOfKind(lean_object* v_name_2021_, lean_object* v_kind_2022_){
_start:
{
lean_object* v___f_2023_; lean_object* v___x_2024_; lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___f_2023_ = lean_alloc_closure((void*)(l_Lake_Toml_numeralOfKind___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2023_, 0, v_kind_2022_);
v___x_2024_ = l_Lake_Toml_numeral;
v___x_2025_ = lean_box(0);
v___x_2026_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2026_, 0, v_name_2021_);
lean_ctor_set(v___x_2026_, 1, v___x_2025_);
v___x_2027_ = ((lean_object*)(l_Lake_Toml_numeralOfKind___closed__0));
v___x_2028_ = l_Lean_Parser_checkStackTop(v___f_2023_, v___x_2027_);
v___x_2029_ = l_Lean_Parser_setExpected(v___x_2026_, v___x_2028_);
v___x_2030_ = l_Lean_Parser_andthen(v___x_2024_, v___x_2029_);
return v___x_2030_;
}
}
static lean_object* _init_l_Lake_Toml_float___closed__0(void){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2031_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_2032_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2));
v___x_2033_ = l_Lake_Toml_numeralOfKind(v___x_2032_, v___x_2031_);
return v___x_2033_;
}
}
static lean_object* _init_l_Lake_Toml_float(void){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = lean_obj_once(&l_Lake_Toml_float___closed__0, &l_Lake_Toml_float___closed__0_once, _init_l_Lake_Toml_float___closed__0);
return v___x_2034_;
}
}
static lean_object* _init_l_Lake_Toml_decInt___closed__0(void){
_start:
{
lean_object* v___x_2035_; lean_object* v___x_2036_; lean_object* v___x_2037_; 
v___x_2035_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_2036_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0));
v___x_2037_ = l_Lake_Toml_numeralOfKind(v___x_2036_, v___x_2035_);
return v___x_2037_;
}
}
static lean_object* _init_l_Lake_Toml_decInt(void){
_start:
{
lean_object* v___x_2038_; 
v___x_2038_ = lean_obj_once(&l_Lake_Toml_decInt___closed__0, &l_Lake_Toml_decInt___closed__0_once, _init_l_Lake_Toml_decInt___closed__0);
return v___x_2038_;
}
}
static lean_object* _init_l_Lake_Toml_binNum___closed__1(void){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2040_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__17));
v___x_2041_ = ((lean_object*)(l_Lake_Toml_binNum___closed__0));
v___x_2042_ = l_Lake_Toml_numeralOfKind(v___x_2041_, v___x_2040_);
return v___x_2042_;
}
}
static lean_object* _init_l_Lake_Toml_binNum(void){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = lean_obj_once(&l_Lake_Toml_binNum___closed__1, &l_Lake_Toml_binNum___closed__1_once, _init_l_Lake_Toml_binNum___closed__1);
return v___x_2043_;
}
}
static lean_object* _init_l_Lake_Toml_octNum___closed__1(void){
_start:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; lean_object* v___x_2047_; 
v___x_2045_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__12));
v___x_2046_ = ((lean_object*)(l_Lake_Toml_octNum___closed__0));
v___x_2047_ = l_Lake_Toml_numeralOfKind(v___x_2046_, v___x_2045_);
return v___x_2047_;
}
}
static lean_object* _init_l_Lake_Toml_octNum(void){
_start:
{
lean_object* v___x_2048_; 
v___x_2048_ = lean_obj_once(&l_Lake_Toml_octNum___closed__1, &l_Lake_Toml_octNum___closed__1_once, _init_l_Lake_Toml_octNum___closed__1);
return v___x_2048_;
}
}
static lean_object* _init_l_Lake_Toml_hexNum___closed__1(void){
_start:
{
lean_object* v___x_2050_; lean_object* v___x_2051_; lean_object* v___x_2052_; 
v___x_2050_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__7));
v___x_2051_ = ((lean_object*)(l_Lake_Toml_hexNum___closed__0));
v___x_2052_ = l_Lake_Toml_numeralOfKind(v___x_2051_, v___x_2050_);
return v___x_2052_;
}
}
static lean_object* _init_l_Lake_Toml_hexNum(void){
_start:
{
lean_object* v___x_2053_; 
v___x_2053_ = lean_obj_once(&l_Lake_Toml_hexNum___closed__1, &l_Lake_Toml_hexNum___closed__1_once, _init_l_Lake_Toml_hexNum___closed__1);
return v___x_2053_;
}
}
static lean_object* _init_l_Lake_Toml_dateTime___closed__0(void){
_start:
{
lean_object* v___x_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; 
v___x_2054_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_2055_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2));
v___x_2056_ = l_Lake_Toml_numeralOfKind(v___x_2055_, v___x_2054_);
return v___x_2056_;
}
}
static lean_object* _init_l_Lake_Toml_dateTime(void){
_start:
{
lean_object* v___x_2057_; 
v___x_2057_ = lean_obj_once(&l_Lake_Toml_dateTime___closed__0, &l_Lake_Toml_dateTime___closed__0_once, _init_l_Lake_Toml_dateTime___closed__0);
return v___x_2057_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_valCore(lean_object* v_val_2058_){
_start:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; lean_object* v___x_2065_; lean_object* v___x_2066_; lean_object* v___x_2067_; 
v___x_2059_ = l_Lake_Toml_string;
v___x_2060_ = l_Lake_Toml_boolean;
v___x_2061_ = l_Lake_Toml_numeral;
lean_inc_ref(v_val_2058_);
v___x_2062_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(v_val_2058_);
v___x_2063_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(v_val_2058_);
v___x_2064_ = l_Lean_Parser_orelse(v___x_2062_, v___x_2063_);
v___x_2065_ = l_Lean_Parser_orelse(v___x_2061_, v___x_2064_);
v___x_2066_ = l_Lean_Parser_orelse(v___x_2060_, v___x_2065_);
v___x_2067_ = l_Lean_Parser_orelse(v___x_2059_, v___x_2066_);
return v___x_2067_;
}
}
static lean_object* _init_l_Lake_Toml_val___closed__3(void){
_start:
{
uint8_t v___x_2074_; lean_object* v___x_2075_; lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2074_ = 1;
v___x_2075_ = ((lean_object*)(l_Lake_Toml_val___closed__2));
v___x_2076_ = ((lean_object*)(l_Lake_Toml_val___closed__1));
v___x_2077_ = ((lean_object*)(l_Lake_Toml_val___closed__0));
v___x_2078_ = l_Lake_Toml_recNodeWithAntiquot(v___x_2077_, v___x_2076_, v___x_2075_, v___x_2074_);
return v___x_2078_;
}
}
static lean_object* _init_l_Lake_Toml_val(void){
_start:
{
lean_object* v___x_2079_; 
v___x_2079_ = lean_obj_once(&l_Lake_Toml_val___closed__3, &l_Lake_Toml_val___closed__3_once, _init_l_Lake_Toml_val___closed__3);
return v___x_2079_;
}
}
static lean_object* _init_l_Lake_Toml_array___closed__0(void){
_start:
{
lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2080_ = l_Lake_Toml_val;
v___x_2081_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(v___x_2080_);
return v___x_2081_;
}
}
static lean_object* _init_l_Lake_Toml_array(void){
_start:
{
lean_object* v___x_2082_; 
v___x_2082_ = lean_obj_once(&l_Lake_Toml_array___closed__0, &l_Lake_Toml_array___closed__0_once, _init_l_Lake_Toml_array___closed__0);
return v___x_2082_;
}
}
static lean_object* _init_l_Lake_Toml_inlineTable___closed__0(void){
_start:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; 
v___x_2083_ = l_Lake_Toml_val;
v___x_2084_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(v___x_2083_);
return v___x_2084_;
}
}
static lean_object* _init_l_Lake_Toml_inlineTable(void){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = lean_obj_once(&l_Lake_Toml_inlineTable___closed__0, &l_Lake_Toml_inlineTable___closed__0_once, _init_l_Lake_Toml_inlineTable___closed__0);
return v___x_2085_;
}
}
static lean_object* _init_l_Lake_Toml_keyval___closed__0(void){
_start:
{
lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2086_ = l_Lake_Toml_val;
v___x_2087_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(v___x_2086_);
return v___x_2087_;
}
}
static lean_object* _init_l_Lake_Toml_keyval(void){
_start:
{
lean_object* v___x_2088_; 
v___x_2088_ = lean_obj_once(&l_Lake_Toml_keyval___closed__0, &l_Lake_Toml_keyval___closed__0_once, _init_l_Lake_Toml_keyval___closed__0);
return v___x_2088_;
}
}
static lean_object* _init_l_Lake_Toml_expression___closed__0(void){
_start:
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
v___x_2089_ = l_Lake_Toml_val;
v___x_2090_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(v___x_2089_);
return v___x_2090_;
}
}
static lean_object* _init_l_Lake_Toml_expression(void){
_start:
{
lean_object* v___x_2091_; 
v___x_2091_ = lean_obj_once(&l_Lake_Toml_expression___closed__0, &l_Lake_Toml_expression___closed__0_once, _init_l_Lake_Toml_expression___closed__0);
return v___x_2091_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_header_formatter(lean_object* v_a_2092_, lean_object* v_a_2093_, lean_object* v_a_2094_, lean_object* v_a_2095_){
_start:
{
lean_object* v___x_2097_; lean_object* v___x_2098_; uint8_t v___x_2099_; lean_object* v___x_2100_; 
v___x_2097_ = ((lean_object*)(l_Lake_Toml_header___closed__0));
v___x_2098_ = ((lean_object*)(l_Lake_Toml_header___closed__1));
v___x_2099_ = 0;
v___x_2100_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v___x_2097_, v___x_2098_, v___x_2099_, v_a_2092_, v_a_2093_, v_a_2094_, v_a_2095_);
return v___x_2100_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_header_formatter___boxed(lean_object* v_a_2101_, lean_object* v_a_2102_, lean_object* v_a_2103_, lean_object* v_a_2104_, lean_object* v_a_2105_){
_start:
{
lean_object* v_res_2106_; 
v_res_2106_ = l_Lake_Toml_header_formatter(v_a_2101_, v_a_2102_, v_a_2103_, v_a_2104_);
lean_dec(v_a_2104_);
lean_dec_ref(v_a_2103_);
lean_dec(v_a_2102_);
lean_dec_ref(v_a_2101_);
return v_res_2106_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_formatter(lean_object* v_a_2107_, lean_object* v_a_2108_, lean_object* v_a_2109_, lean_object* v_a_2110_){
_start:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; uint8_t v___x_2114_; lean_object* v___x_2115_; 
v___x_2112_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__0));
v___x_2113_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__1));
v___x_2114_ = 0;
v___x_2115_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v___x_2112_, v___x_2113_, v___x_2114_, v_a_2107_, v_a_2108_, v_a_2109_, v_a_2110_);
return v___x_2115_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_formatter___boxed(lean_object* v_a_2116_, lean_object* v_a_2117_, lean_object* v_a_2118_, lean_object* v_a_2119_, lean_object* v_a_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l_Lake_Toml_unquotedKey_formatter(v_a_2116_, v_a_2117_, v_a_2118_, v_a_2119_);
lean_dec(v_a_2119_);
lean_dec_ref(v_a_2118_);
lean_dec(v_a_2117_);
lean_dec_ref(v_a_2116_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_formatter(lean_object* v_a_2122_, lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_){
_start:
{
lean_object* v___x_2127_; lean_object* v___x_2128_; uint8_t v___x_2129_; lean_object* v___x_2130_; 
v___x_2127_ = ((lean_object*)(l_Lake_Toml_basicString___closed__0));
v___x_2128_ = ((lean_object*)(l_Lake_Toml_basicString___closed__1));
v___x_2129_ = 0;
v___x_2130_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v___x_2127_, v___x_2128_, v___x_2129_, v_a_2122_, v_a_2123_, v_a_2124_, v_a_2125_);
return v___x_2130_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_formatter___boxed(lean_object* v_a_2131_, lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_){
_start:
{
lean_object* v_res_2136_; 
v_res_2136_ = l_Lake_Toml_basicString_formatter(v_a_2131_, v_a_2132_, v_a_2133_, v_a_2134_);
lean_dec(v_a_2134_);
lean_dec_ref(v_a_2133_);
lean_dec(v_a_2132_);
lean_dec_ref(v_a_2131_);
return v_res_2136_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_formatter(lean_object* v_a_2137_, lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_){
_start:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; uint8_t v___x_2144_; lean_object* v___x_2145_; 
v___x_2142_ = ((lean_object*)(l_Lake_Toml_literalString___closed__0));
v___x_2143_ = ((lean_object*)(l_Lake_Toml_literalString___closed__1));
v___x_2144_ = 0;
v___x_2145_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v___x_2142_, v___x_2143_, v___x_2144_, v_a_2137_, v_a_2138_, v_a_2139_, v_a_2140_);
return v___x_2145_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_formatter___boxed(lean_object* v_a_2146_, lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_){
_start:
{
lean_object* v_res_2151_; 
v_res_2151_ = l_Lake_Toml_literalString_formatter(v_a_2146_, v_a_2147_, v_a_2148_, v_a_2149_);
lean_dec(v_a_2149_);
lean_dec_ref(v_a_2148_);
lean_dec(v_a_2147_);
lean_dec_ref(v_a_2146_);
return v_res_2151_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_formatter(lean_object* v_a_2152_, lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_){
_start:
{
lean_object* v___x_2157_; lean_object* v___x_2158_; lean_object* v___x_2159_; 
v___x_2157_ = lean_alloc_closure((void*)(l_Lake_Toml_basicString_formatter___boxed), 5, 0);
v___x_2158_ = lean_alloc_closure((void*)(l_Lake_Toml_literalString_formatter___boxed), 5, 0);
v___x_2159_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2157_, v___x_2158_, v_a_2152_, v_a_2153_, v_a_2154_, v_a_2155_);
return v___x_2159_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_formatter___boxed(lean_object* v_a_2160_, lean_object* v_a_2161_, lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l_Lake_Toml_quotedKey_formatter(v_a_2160_, v_a_2161_, v_a_2162_, v_a_2163_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
lean_dec(v_a_2161_);
lean_dec_ref(v_a_2160_);
return v_res_2165_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey_formatter___closed__0(void){
_start:
{
lean_object* v___x_2166_; lean_object* v___x_2167_; lean_object* v___x_2168_; 
v___x_2166_ = lean_alloc_closure((void*)(l_Lake_Toml_quotedKey_formatter___boxed), 5, 0);
v___x_2167_ = lean_alloc_closure((void*)(l_Lake_Toml_unquotedKey_formatter___boxed), 5, 0);
v___x_2168_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2168_, 0, v___x_2167_);
lean_closure_set(v___x_2168_, 1, v___x_2166_);
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_formatter(lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_){
_start:
{
lean_object* v___x_2174_; lean_object* v___x_2175_; lean_object* v___x_2176_; uint8_t v___x_2177_; lean_object* v___x_2178_; 
v___x_2174_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__0));
v___x_2175_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__1));
v___x_2176_ = lean_obj_once(&l_Lake_Toml_simpleKey_formatter___closed__0, &l_Lake_Toml_simpleKey_formatter___closed__0_once, _init_l_Lake_Toml_simpleKey_formatter___closed__0);
v___x_2177_ = 1;
v___x_2178_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2174_, v___x_2175_, v___x_2176_, v___x_2177_, v_a_2169_, v_a_2170_, v_a_2171_, v_a_2172_);
return v___x_2178_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_formatter___boxed(lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_, lean_object* v_a_2182_, lean_object* v_a_2183_){
_start:
{
lean_object* v_res_2184_; 
v_res_2184_ = l_Lake_Toml_simpleKey_formatter(v_a_2179_, v_a_2180_, v_a_2181_, v_a_2182_);
lean_dec(v_a_2182_);
lean_dec_ref(v_a_2181_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
return v_res_2184_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter___redArg(){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter___redArg___boxed(lean_object* v_a_2187_){
_start:
{
lean_object* v_res_2188_; 
v_res_2188_ = l_Lake_Toml_trailingWs_formatter___redArg();
return v_res_2188_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter(lean_object* v_a_2189_, lean_object* v_a_2190_, lean_object* v_a_2191_, lean_object* v_a_2192_){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter___boxed(lean_object* v_a_2195_, lean_object* v_a_2196_, lean_object* v_a_2197_, lean_object* v_a_2198_, lean_object* v_a_2199_){
_start:
{
lean_object* v_res_2200_; 
v_res_2200_ = l_Lake_Toml_trailingWs_formatter(v_a_2195_, v_a_2196_, v_a_2197_, v_a_2198_);
lean_dec(v_a_2198_);
lean_dec_ref(v_a_2197_);
lean_dec(v_a_2196_);
lean_dec_ref(v_a_2195_);
return v_res_2200_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_2201_; lean_object* v___x_2202_; 
v___x_2201_ = 46;
v___x_2202_ = lean_box_uint32(v___x_2201_);
return v___x_2202_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__0(void){
_start:
{
lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; 
v___x_2203_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2204_ = lean_obj_once(&l_Lake_Toml_key___closed__7, &l_Lake_Toml_key___closed__7_once, _init_l_Lake_Toml_key___closed__7);
v___x_2205_ = l_Lake_Toml_key_formatter___closed__0___boxed__const__1;
v___x_2206_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2206_, 0, v___x_2205_);
lean_closure_set(v___x_2206_, 1, v___x_2204_);
lean_closure_set(v___x_2206_, 2, v___x_2203_);
return v___x_2206_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__1(void){
_start:
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
v___x_2207_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2208_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__0, &l_Lake_Toml_key_formatter___closed__0_once, _init_l_Lake_Toml_key_formatter___closed__0);
v___x_2209_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2209_, 0, v___x_2208_);
lean_closure_set(v___x_2209_, 1, v___x_2207_);
return v___x_2209_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__2(void){
_start:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__1, &l_Lake_Toml_key_formatter___closed__1_once, _init_l_Lake_Toml_key_formatter___closed__1);
v___x_2211_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2212_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2212_, 0, v___x_2211_);
lean_closure_set(v___x_2212_, 1, v___x_2210_);
return v___x_2212_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__3(void){
_start:
{
uint8_t v___x_2213_; lean_object* v___x_2214_; lean_object* v___x_2215_; lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
v___x_2213_ = 0;
v___x_2214_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__2, &l_Lake_Toml_key_formatter___closed__2_once, _init_l_Lake_Toml_key_formatter___closed__2);
v___x_2215_ = ((lean_object*)(l_Lake_Toml_key___closed__3));
v___x_2216_ = lean_alloc_closure((void*)(l_Lake_Toml_simpleKey_formatter___boxed), 5, 0);
v___x_2217_ = lean_box(v___x_2213_);
v___x_2218_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_formatter___boxed), 9, 4);
lean_closure_set(v___x_2218_, 0, v___x_2216_);
lean_closure_set(v___x_2218_, 1, v___x_2215_);
lean_closure_set(v___x_2218_, 2, v___x_2214_);
lean_closure_set(v___x_2218_, 3, v___x_2217_);
return v___x_2218_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__4(void){
_start:
{
lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; 
v___x_2219_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__3, &l_Lake_Toml_key_formatter___closed__3_once, _init_l_Lake_Toml_key_formatter___closed__3);
v___x_2220_ = ((lean_object*)(l_Lake_Toml_key___closed__2));
v___x_2221_ = lean_alloc_closure((void*)(l_Lean_Parser_setExpected_formatter___boxed), 7, 2);
lean_closure_set(v___x_2221_, 0, v___x_2220_);
lean_closure_set(v___x_2221_, 1, v___x_2219_);
return v___x_2221_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_key_formatter(lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_a_2224_, lean_object* v_a_2225_){
_start:
{
lean_object* v___x_2227_; lean_object* v___x_2228_; lean_object* v___x_2229_; uint8_t v___x_2230_; lean_object* v___x_2231_; 
v___x_2227_ = ((lean_object*)(l_Lake_Toml_key___closed__0));
v___x_2228_ = ((lean_object*)(l_Lake_Toml_key___closed__1));
v___x_2229_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__4, &l_Lake_Toml_key_formatter___closed__4_once, _init_l_Lake_Toml_key_formatter___closed__4);
v___x_2230_ = 1;
v___x_2231_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2227_, v___x_2228_, v___x_2229_, v___x_2230_, v_a_2222_, v_a_2223_, v_a_2224_, v_a_2225_);
return v___x_2231_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_key_formatter___boxed(lean_object* v_a_2232_, lean_object* v_a_2233_, lean_object* v_a_2234_, lean_object* v_a_2235_, lean_object* v_a_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l_Lake_Toml_key_formatter(v_a_2232_, v_a_2233_, v_a_2234_, v_a_2235_);
lean_dec(v_a_2235_);
lean_dec_ref(v_a_2234_);
lean_dec(v_a_2233_);
lean_dec_ref(v_a_2232_);
return v_res_2237_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_2238_; lean_object* v___x_2239_; 
v___x_2238_ = 61;
v___x_2239_ = lean_box_uint32(v___x_2238_);
return v___x_2239_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0(void){
_start:
{
lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2240_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2241_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5);
v___x_2242_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1;
v___x_2243_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2243_, 0, v___x_2242_);
lean_closure_set(v___x_2243_, 1, v___x_2241_);
lean_closure_set(v___x_2243_, 2, v___x_2240_);
return v___x_2243_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter(lean_object* v_val_2244_, lean_object* v_a_2245_, lean_object* v_a_2246_, lean_object* v_a_2247_, lean_object* v_a_2248_){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; uint8_t v___x_2259_; lean_object* v___x_2260_; 
v___x_2250_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0));
v___x_2251_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1));
v___x_2252_ = lean_alloc_closure((void*)(l_Lake_Toml_key_formatter___boxed), 5, 0);
v___x_2253_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2254_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0);
lean_inc_ref(v___x_2253_);
v___x_2255_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2255_, 0, v___x_2253_);
lean_closure_set(v___x_2255_, 1, v_val_2244_);
v___x_2256_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2256_, 0, v___x_2254_);
lean_closure_set(v___x_2256_, 1, v___x_2255_);
v___x_2257_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2257_, 0, v___x_2253_);
lean_closure_set(v___x_2257_, 1, v___x_2256_);
v___x_2258_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2258_, 0, v___x_2252_);
lean_closure_set(v___x_2258_, 1, v___x_2257_);
v___x_2259_ = 1;
v___x_2260_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2250_, v___x_2251_, v___x_2258_, v___x_2259_, v_a_2245_, v_a_2246_, v_a_2247_, v_a_2248_);
return v___x_2260_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___boxed(lean_object* v_val_2261_, lean_object* v_a_2262_, lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_){
_start:
{
lean_object* v_res_2267_; 
v_res_2267_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter(v_val_2261_, v_a_2262_, v_a_2263_, v_a_2264_, v_a_2265_);
lean_dec(v_a_2265_);
lean_dec_ref(v_a_2264_);
lean_dec(v_a_2263_);
lean_dec_ref(v_a_2262_);
return v_res_2267_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_2268_; lean_object* v___x_2269_; 
v___x_2268_ = 91;
v___x_2269_ = lean_box_uint32(v___x_2268_);
return v___x_2269_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__0(void){
_start:
{
lean_object* v___x_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2270_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2271_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__3));
v___x_2272_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
v___x_2273_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2273_, 0, v___x_2272_);
lean_closure_set(v___x_2273_, 1, v___x_2271_);
lean_closure_set(v___x_2273_, 2, v___x_2270_);
return v___x_2273_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__1(void){
_start:
{
lean_object* v___x_2274_; lean_object* v___x_2275_; lean_object* v___x_2276_; lean_object* v___x_2277_; 
v___x_2274_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2275_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__8, &l_Lake_Toml_stdTable___closed__8_once, _init_l_Lake_Toml_stdTable___closed__8);
v___x_2276_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
v___x_2277_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2277_, 0, v___x_2276_);
lean_closure_set(v___x_2277_, 1, v___x_2275_);
lean_closure_set(v___x_2277_, 2, v___x_2274_);
return v___x_2277_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__2(void){
_start:
{
lean_object* v___x_2278_; lean_object* v___x_2279_; 
v___x_2278_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__1, &l_Lake_Toml_stdTable_formatter___closed__1_once, _init_l_Lake_Toml_stdTable_formatter___closed__1);
v___x_2279_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed), 6, 1);
lean_closure_set(v___x_2279_, 0, v___x_2278_);
return v___x_2279_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__3(void){
_start:
{
lean_object* v___x_2280_; lean_object* v___x_2281_; lean_object* v___x_2282_; 
v___x_2280_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__2, &l_Lake_Toml_stdTable_formatter___closed__2_once, _init_l_Lake_Toml_stdTable_formatter___closed__2);
v___x_2281_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__0, &l_Lake_Toml_stdTable_formatter___closed__0_once, _init_l_Lake_Toml_stdTable_formatter___closed__0);
v___x_2282_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2282_, 0, v___x_2281_);
lean_closure_set(v___x_2282_, 1, v___x_2280_);
return v___x_2282_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__4(void){
_start:
{
lean_object* v___x_2283_; lean_object* v___x_2284_; 
v___x_2283_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__3, &l_Lake_Toml_stdTable_formatter___closed__3_once, _init_l_Lake_Toml_stdTable_formatter___closed__3);
v___x_2284_ = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter___boxed), 6, 1);
lean_closure_set(v___x_2284_, 0, v___x_2283_);
return v___x_2284_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1(void){
_start:
{
uint32_t v___x_2285_; lean_object* v___x_2286_; 
v___x_2285_ = 93;
v___x_2286_ = lean_box_uint32(v___x_2285_);
return v___x_2286_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__5(void){
_start:
{
lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; lean_object* v___x_2290_; 
v___x_2287_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2288_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__17, &l_Lake_Toml_stdTable___closed__17_once, _init_l_Lake_Toml_stdTable___closed__17);
v___x_2289_ = l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1;
v___x_2290_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2290_, 0, v___x_2289_);
lean_closure_set(v___x_2290_, 1, v___x_2288_);
lean_closure_set(v___x_2290_, 2, v___x_2287_);
return v___x_2290_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__6(void){
_start:
{
lean_object* v___x_2291_; lean_object* v___x_2292_; lean_object* v___x_2293_; 
v___x_2291_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__5, &l_Lake_Toml_stdTable_formatter___closed__5_once, _init_l_Lake_Toml_stdTable_formatter___closed__5);
v___x_2292_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2293_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2293_, 0, v___x_2292_);
lean_closure_set(v___x_2293_, 1, v___x_2291_);
return v___x_2293_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__7(void){
_start:
{
lean_object* v___x_2294_; lean_object* v___x_2295_; lean_object* v___x_2296_; 
v___x_2294_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__6, &l_Lake_Toml_stdTable_formatter___closed__6_once, _init_l_Lake_Toml_stdTable_formatter___closed__6);
v___x_2295_ = lean_alloc_closure((void*)(l_Lake_Toml_key_formatter___boxed), 5, 0);
v___x_2296_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2296_, 0, v___x_2295_);
lean_closure_set(v___x_2296_, 1, v___x_2294_);
return v___x_2296_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__8(void){
_start:
{
lean_object* v___x_2297_; lean_object* v___x_2298_; lean_object* v___x_2299_; 
v___x_2297_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__7, &l_Lake_Toml_stdTable_formatter___closed__7_once, _init_l_Lake_Toml_stdTable_formatter___closed__7);
v___x_2298_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2299_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2299_, 0, v___x_2298_);
lean_closure_set(v___x_2299_, 1, v___x_2297_);
return v___x_2299_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__9(void){
_start:
{
lean_object* v___x_2300_; lean_object* v___x_2301_; lean_object* v___x_2302_; 
v___x_2300_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__8, &l_Lake_Toml_stdTable_formatter___closed__8_once, _init_l_Lake_Toml_stdTable_formatter___closed__8);
v___x_2301_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__4, &l_Lake_Toml_stdTable_formatter___closed__4_once, _init_l_Lake_Toml_stdTable_formatter___closed__4);
v___x_2302_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2302_, 0, v___x_2301_);
lean_closure_set(v___x_2302_, 1, v___x_2300_);
return v___x_2302_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_formatter(lean_object* v_a_2303_, lean_object* v_a_2304_, lean_object* v_a_2305_, lean_object* v_a_2306_){
_start:
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; uint8_t v___x_2311_; lean_object* v___x_2312_; 
v___x_2308_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__0));
v___x_2309_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__1));
v___x_2310_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__9, &l_Lake_Toml_stdTable_formatter___closed__9_once, _init_l_Lake_Toml_stdTable_formatter___closed__9);
v___x_2311_ = 0;
v___x_2312_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2308_, v___x_2309_, v___x_2310_, v___x_2311_, v_a_2303_, v_a_2304_, v_a_2305_, v_a_2306_);
return v___x_2312_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_formatter___boxed(lean_object* v_a_2313_, lean_object* v_a_2314_, lean_object* v_a_2315_, lean_object* v_a_2316_, lean_object* v_a_2317_){
_start:
{
lean_object* v_res_2318_; 
v_res_2318_ = l_Lake_Toml_stdTable_formatter(v_a_2313_, v_a_2314_, v_a_2315_, v_a_2316_);
lean_dec(v_a_2316_);
lean_dec_ref(v_a_2315_);
lean_dec(v_a_2314_);
lean_dec_ref(v_a_2313_);
return v_res_2318_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__0(void){
_start:
{
lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2319_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__1, &l_Lake_Toml_stdTable_formatter___closed__1_once, _init_l_Lake_Toml_stdTable_formatter___closed__1);
v___x_2320_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__0, &l_Lake_Toml_stdTable_formatter___closed__0_once, _init_l_Lake_Toml_stdTable_formatter___closed__0);
v___x_2321_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2321_, 0, v___x_2320_);
lean_closure_set(v___x_2321_, 1, v___x_2319_);
return v___x_2321_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__1(void){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; 
v___x_2322_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__0, &l_Lake_Toml_arrayTable_formatter___closed__0_once, _init_l_Lake_Toml_arrayTable_formatter___closed__0);
v___x_2323_ = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter___boxed), 6, 1);
lean_closure_set(v___x_2323_, 0, v___x_2322_);
return v___x_2323_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__2(void){
_start:
{
lean_object* v___x_2324_; lean_object* v___x_2325_; 
v___x_2324_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__5, &l_Lake_Toml_stdTable_formatter___closed__5_once, _init_l_Lake_Toml_stdTable_formatter___closed__5);
v___x_2325_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2325_, 0, v___x_2324_);
lean_closure_set(v___x_2325_, 1, v___x_2324_);
return v___x_2325_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__3(void){
_start:
{
lean_object* v___x_2326_; lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2326_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__2, &l_Lake_Toml_arrayTable_formatter___closed__2_once, _init_l_Lake_Toml_arrayTable_formatter___closed__2);
v___x_2327_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2328_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2328_, 0, v___x_2327_);
lean_closure_set(v___x_2328_, 1, v___x_2326_);
return v___x_2328_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__4(void){
_start:
{
lean_object* v___x_2329_; lean_object* v___x_2330_; lean_object* v___x_2331_; 
v___x_2329_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__3, &l_Lake_Toml_arrayTable_formatter___closed__3_once, _init_l_Lake_Toml_arrayTable_formatter___closed__3);
v___x_2330_ = lean_alloc_closure((void*)(l_Lake_Toml_key_formatter___boxed), 5, 0);
v___x_2331_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2331_, 0, v___x_2330_);
lean_closure_set(v___x_2331_, 1, v___x_2329_);
return v___x_2331_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__5(void){
_start:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2332_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__4, &l_Lake_Toml_arrayTable_formatter___closed__4_once, _init_l_Lake_Toml_arrayTable_formatter___closed__4);
v___x_2333_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2334_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2334_, 0, v___x_2333_);
lean_closure_set(v___x_2334_, 1, v___x_2332_);
return v___x_2334_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__6(void){
_start:
{
lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; 
v___x_2335_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__5, &l_Lake_Toml_arrayTable_formatter___closed__5_once, _init_l_Lake_Toml_arrayTable_formatter___closed__5);
v___x_2336_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__1, &l_Lake_Toml_arrayTable_formatter___closed__1_once, _init_l_Lake_Toml_arrayTable_formatter___closed__1);
v___x_2337_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2337_, 0, v___x_2336_);
lean_closure_set(v___x_2337_, 1, v___x_2335_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_formatter(lean_object* v_a_2338_, lean_object* v_a_2339_, lean_object* v_a_2340_, lean_object* v_a_2341_){
_start:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; uint8_t v___x_2346_; lean_object* v___x_2347_; 
v___x_2343_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__0));
v___x_2344_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__1));
v___x_2345_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__6, &l_Lake_Toml_arrayTable_formatter___closed__6_once, _init_l_Lake_Toml_arrayTable_formatter___closed__6);
v___x_2346_ = 0;
v___x_2347_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2343_, v___x_2344_, v___x_2345_, v___x_2346_, v_a_2338_, v_a_2339_, v_a_2340_, v_a_2341_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_formatter___boxed(lean_object* v_a_2348_, lean_object* v_a_2349_, lean_object* v_a_2350_, lean_object* v_a_2351_, lean_object* v_a_2352_){
_start:
{
lean_object* v_res_2353_; 
v_res_2353_ = l_Lake_Toml_arrayTable_formatter(v_a_2348_, v_a_2349_, v_a_2350_, v_a_2351_);
lean_dec(v_a_2351_);
lean_dec_ref(v_a_2350_);
lean_dec(v_a_2349_);
lean_dec_ref(v_a_2348_);
return v_res_2353_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_table_formatter(lean_object* v_a_2354_, lean_object* v_a_2355_, lean_object* v_a_2356_, lean_object* v_a_2357_){
_start:
{
lean_object* v___x_2359_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
v___x_2359_ = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_formatter___boxed), 5, 0);
v___x_2360_ = lean_alloc_closure((void*)(l_Lake_Toml_arrayTable_formatter___boxed), 5, 0);
v___x_2361_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2359_, v___x_2360_, v_a_2354_, v_a_2355_, v_a_2356_, v_a_2357_);
return v___x_2361_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_table_formatter___boxed(lean_object* v_a_2362_, lean_object* v_a_2363_, lean_object* v_a_2364_, lean_object* v_a_2365_, lean_object* v_a_2366_){
_start:
{
lean_object* v_res_2367_; 
v_res_2367_ = l_Lake_Toml_table_formatter(v_a_2362_, v_a_2363_, v_a_2364_, v_a_2365_);
lean_dec(v_a_2365_);
lean_dec_ref(v_a_2364_);
lean_dec(v_a_2363_);
lean_dec_ref(v_a_2362_);
return v_res_2367_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter(lean_object* v_val_2374_, lean_object* v_a_2375_, lean_object* v_a_2376_, lean_object* v_a_2377_, lean_object* v_a_2378_){
_start:
{
lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; lean_object* v___x_2383_; lean_object* v___x_2384_; 
v___x_2380_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___closed__0));
v___x_2381_ = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___boxed), 6, 1);
lean_closure_set(v___x_2381_, 0, v_val_2374_);
v___x_2382_ = lean_alloc_closure((void*)(l_Lake_Toml_table_formatter___boxed), 5, 0);
v___x_2383_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2383_, 0, v___x_2381_);
lean_closure_set(v___x_2383_, 1, v___x_2382_);
v___x_2384_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2380_, v___x_2383_, v_a_2375_, v_a_2376_, v_a_2377_, v_a_2378_);
return v___x_2384_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___boxed(lean_object* v_val_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_, lean_object* v_a_2389_, lean_object* v_a_2390_){
_start:
{
lean_object* v_res_2391_; 
v_res_2391_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter(v_val_2385_, v_a_2386_, v_a_2387_, v_a_2388_, v_a_2389_);
lean_dec(v_a_2389_);
lean_dec_ref(v_a_2388_);
lean_dec(v_a_2387_);
lean_dec_ref(v_a_2386_);
return v_res_2391_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter___redArg(){
_start:
{
lean_object* v___x_2393_; 
v___x_2393_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_2393_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter___redArg___boxed(lean_object* v_a_2394_){
_start:
{
lean_object* v_res_2395_; 
v_res_2395_ = l_Lake_Toml_trailingSep_formatter___redArg();
return v_res_2395_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter(lean_object* v_a_2396_, lean_object* v_a_2397_, lean_object* v_a_2398_, lean_object* v_a_2399_){
_start:
{
lean_object* v___x_2401_; 
v___x_2401_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_2401_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter___boxed(lean_object* v_a_2402_, lean_object* v_a_2403_, lean_object* v_a_2404_, lean_object* v_a_2405_, lean_object* v_a_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_Lake_Toml_trailingSep_formatter(v_a_2402_, v_a_2403_, v_a_2404_, v_a_2405_);
lean_dec(v_a_2405_);
lean_dec_ref(v_a_2404_);
lean_dec(v_a_2403_);
lean_dec_ref(v_a_2402_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(lean_object* v_val_2408_, lean_object* v_a_2409_, lean_object* v_a_2410_, lean_object* v_a_2411_, lean_object* v_a_2412_){
_start:
{
lean_object* v___x_2414_; lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; uint8_t v___x_2420_; lean_object* v___x_2421_; lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
v___x_2414_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0));
v___x_2415_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1));
v___x_2416_ = lean_alloc_closure((void*)(l_Lake_Toml_header_formatter___boxed), 5, 0);
v___x_2417_ = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___boxed), 6, 1);
lean_closure_set(v___x_2417_, 0, v_val_2408_);
v___x_2418_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingSep_formatter___boxed), 5, 0);
v___x_2419_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2419_, 0, v___x_2417_);
lean_closure_set(v___x_2419_, 1, v___x_2418_);
v___x_2420_ = 1;
v___x_2421_ = lean_box(v___x_2420_);
v___x_2422_ = lean_alloc_closure((void*)(l_Lake_Toml_sepByLinebreak_formatter___boxed), 7, 2);
lean_closure_set(v___x_2422_, 0, v___x_2419_);
lean_closure_set(v___x_2422_, 1, v___x_2421_);
v___x_2423_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2423_, 0, v___x_2416_);
lean_closure_set(v___x_2423_, 1, v___x_2422_);
v___x_2424_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2414_, v___x_2415_, v___x_2423_, v___x_2420_, v_a_2409_, v_a_2410_, v_a_2411_, v_a_2412_);
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter___boxed(lean_object* v_val_2425_, lean_object* v_a_2426_, lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v_res_2431_; 
v_res_2431_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(v_val_2425_, v_a_2426_, v_a_2427_, v_a_2428_, v_a_2429_);
lean_dec(v_a_2429_);
lean_dec_ref(v_a_2428_);
lean_dec(v_a_2427_);
lean_dec_ref(v_a_2426_);
return v_res_2431_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_val_formatter(lean_object* v_a_2432_, lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_){
_start:
{
lean_object* v___x_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; uint8_t v___x_2440_; lean_object* v___x_2441_; 
v___x_2437_ = ((lean_object*)(l_Lake_Toml_val___closed__0));
v___x_2438_ = ((lean_object*)(l_Lake_Toml_val___closed__1));
v___x_2439_ = ((lean_object*)(l_Lake_Toml_val___closed__2));
v___x_2440_ = 1;
v___x_2441_ = l_Lake_Toml_recNodeWithAntiquot_formatter(v___x_2437_, v___x_2438_, v___x_2439_, v___x_2440_, v_a_2432_, v_a_2433_, v_a_2434_, v_a_2435_);
return v___x_2441_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_val_formatter___boxed(lean_object* v_a_2442_, lean_object* v_a_2443_, lean_object* v_a_2444_, lean_object* v_a_2445_, lean_object* v_a_2446_){
_start:
{
lean_object* v_res_2447_; 
v_res_2447_ = l_Lake_Toml_val_formatter(v_a_2442_, v_a_2443_, v_a_2444_, v_a_2445_);
lean_dec(v_a_2445_);
lean_dec_ref(v_a_2444_);
lean_dec(v_a_2443_);
lean_dec_ref(v_a_2442_);
return v_res_2447_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_toml_formatter(lean_object* v_a_2448_, lean_object* v_a_2449_, lean_object* v_a_2450_, lean_object* v_a_2451_){
_start:
{
lean_object* v___x_2453_; lean_object* v___x_2454_; 
v___x_2453_ = lean_alloc_closure((void*)(l_Lake_Toml_val_formatter___boxed), 5, 0);
v___x_2454_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(v___x_2453_, v_a_2448_, v_a_2449_, v_a_2450_, v_a_2451_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_toml_formatter___boxed(lean_object* v_a_2455_, lean_object* v_a_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l_Lake_Toml_toml_formatter(v_a_2455_, v_a_2456_, v_a_2457_, v_a_2458_);
lean_dec(v_a_2458_);
lean_dec_ref(v_a_2457_);
lean_dec(v_a_2456_);
lean_dec_ref(v_a_2455_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_header_parenthesizer(lean_object* v_a_2461_, lean_object* v_a_2462_, lean_object* v_a_2463_, lean_object* v_a_2464_){
_start:
{
lean_object* v___x_2466_; lean_object* v___x_2467_; uint8_t v___x_2468_; lean_object* v___x_2469_; 
v___x_2466_ = ((lean_object*)(l_Lake_Toml_header___closed__0));
v___x_2467_ = ((lean_object*)(l_Lake_Toml_header___closed__1));
v___x_2468_ = 0;
v___x_2469_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v___x_2466_, v___x_2467_, v___x_2468_, v_a_2461_, v_a_2462_, v_a_2463_, v_a_2464_);
return v___x_2469_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_header_parenthesizer___boxed(lean_object* v_a_2470_, lean_object* v_a_2471_, lean_object* v_a_2472_, lean_object* v_a_2473_, lean_object* v_a_2474_){
_start:
{
lean_object* v_res_2475_; 
v_res_2475_ = l_Lake_Toml_header_parenthesizer(v_a_2470_, v_a_2471_, v_a_2472_, v_a_2473_);
lean_dec(v_a_2473_);
lean_dec_ref(v_a_2472_);
lean_dec(v_a_2471_);
lean_dec_ref(v_a_2470_);
return v_res_2475_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_parenthesizer(lean_object* v_a_2476_, lean_object* v_a_2477_, lean_object* v_a_2478_, lean_object* v_a_2479_){
_start:
{
lean_object* v___x_2481_; lean_object* v___x_2482_; uint8_t v___x_2483_; lean_object* v___x_2484_; 
v___x_2481_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__0));
v___x_2482_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__1));
v___x_2483_ = 0;
v___x_2484_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v___x_2481_, v___x_2482_, v___x_2483_, v_a_2476_, v_a_2477_, v_a_2478_, v_a_2479_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_parenthesizer___boxed(lean_object* v_a_2485_, lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_){
_start:
{
lean_object* v_res_2490_; 
v_res_2490_ = l_Lake_Toml_unquotedKey_parenthesizer(v_a_2485_, v_a_2486_, v_a_2487_, v_a_2488_);
lean_dec(v_a_2488_);
lean_dec_ref(v_a_2487_);
lean_dec(v_a_2486_);
lean_dec_ref(v_a_2485_);
return v_res_2490_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_parenthesizer(lean_object* v_a_2491_, lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_){
_start:
{
lean_object* v___x_2496_; lean_object* v___x_2497_; uint8_t v___x_2498_; lean_object* v___x_2499_; 
v___x_2496_ = ((lean_object*)(l_Lake_Toml_basicString___closed__0));
v___x_2497_ = ((lean_object*)(l_Lake_Toml_basicString___closed__1));
v___x_2498_ = 0;
v___x_2499_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v___x_2496_, v___x_2497_, v___x_2498_, v_a_2491_, v_a_2492_, v_a_2493_, v_a_2494_);
return v___x_2499_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_parenthesizer___boxed(lean_object* v_a_2500_, lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_){
_start:
{
lean_object* v_res_2505_; 
v_res_2505_ = l_Lake_Toml_basicString_parenthesizer(v_a_2500_, v_a_2501_, v_a_2502_, v_a_2503_);
lean_dec(v_a_2503_);
lean_dec_ref(v_a_2502_);
lean_dec(v_a_2501_);
lean_dec_ref(v_a_2500_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_parenthesizer(lean_object* v_a_2506_, lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_){
_start:
{
lean_object* v___x_2511_; lean_object* v___x_2512_; uint8_t v___x_2513_; lean_object* v___x_2514_; 
v___x_2511_ = ((lean_object*)(l_Lake_Toml_literalString___closed__0));
v___x_2512_ = ((lean_object*)(l_Lake_Toml_literalString___closed__1));
v___x_2513_ = 0;
v___x_2514_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v___x_2511_, v___x_2512_, v___x_2513_, v_a_2506_, v_a_2507_, v_a_2508_, v_a_2509_);
return v___x_2514_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_parenthesizer___boxed(lean_object* v_a_2515_, lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_){
_start:
{
lean_object* v_res_2520_; 
v_res_2520_ = l_Lake_Toml_literalString_parenthesizer(v_a_2515_, v_a_2516_, v_a_2517_, v_a_2518_);
lean_dec(v_a_2518_);
lean_dec_ref(v_a_2517_);
lean_dec(v_a_2516_);
lean_dec_ref(v_a_2515_);
return v_res_2520_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_parenthesizer(lean_object* v_a_2521_, lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_){
_start:
{
lean_object* v___x_2526_; lean_object* v___x_2527_; lean_object* v___x_2528_; 
v___x_2526_ = lean_alloc_closure((void*)(l_Lake_Toml_basicString_parenthesizer___boxed), 5, 0);
v___x_2527_ = lean_alloc_closure((void*)(l_Lake_Toml_literalString_parenthesizer___boxed), 5, 0);
v___x_2528_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___x_2526_, v___x_2527_, v_a_2521_, v_a_2522_, v_a_2523_, v_a_2524_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_parenthesizer___boxed(lean_object* v_a_2529_, lean_object* v_a_2530_, lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_Lake_Toml_quotedKey_parenthesizer(v_a_2529_, v_a_2530_, v_a_2531_, v_a_2532_);
lean_dec(v_a_2532_);
lean_dec_ref(v_a_2531_);
lean_dec(v_a_2530_);
lean_dec_ref(v_a_2529_);
return v_res_2534_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2535_ = lean_alloc_closure((void*)(l_Lake_Toml_quotedKey_parenthesizer___boxed), 5, 0);
v___x_2536_ = lean_alloc_closure((void*)(l_Lake_Toml_unquotedKey_parenthesizer___boxed), 5, 0);
v___x_2537_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2537_, 0, v___x_2536_);
lean_closure_set(v___x_2537_, 1, v___x_2535_);
return v___x_2537_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_parenthesizer(lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_, lean_object* v_a_2541_){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; lean_object* v___x_2547_; 
v___x_2543_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__0));
v___x_2544_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__1));
v___x_2545_ = lean_obj_once(&l_Lake_Toml_simpleKey_parenthesizer___closed__0, &l_Lake_Toml_simpleKey_parenthesizer___closed__0_once, _init_l_Lake_Toml_simpleKey_parenthesizer___closed__0);
v___x_2546_ = 1;
v___x_2547_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2543_, v___x_2544_, v___x_2545_, v___x_2546_, v_a_2538_, v_a_2539_, v_a_2540_, v_a_2541_);
return v___x_2547_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_parenthesizer___boxed(lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_, lean_object* v_a_2551_, lean_object* v_a_2552_){
_start:
{
lean_object* v_res_2553_; 
v_res_2553_ = l_Lake_Toml_simpleKey_parenthesizer(v_a_2548_, v_a_2549_, v_a_2550_, v_a_2551_);
lean_dec(v_a_2551_);
lean_dec_ref(v_a_2550_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
return v_res_2553_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer___redArg(){
_start:
{
lean_object* v___x_2555_; 
v___x_2555_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_2555_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer___redArg___boxed(lean_object* v_a_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Lake_Toml_trailingWs_parenthesizer___redArg();
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer(lean_object* v_a_2558_, lean_object* v_a_2559_, lean_object* v_a_2560_, lean_object* v_a_2561_){
_start:
{
lean_object* v___x_2563_; 
v___x_2563_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_2563_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer___boxed(lean_object* v_a_2564_, lean_object* v_a_2565_, lean_object* v_a_2566_, lean_object* v_a_2567_, lean_object* v_a_2568_){
_start:
{
lean_object* v_res_2569_; 
v_res_2569_ = l_Lake_Toml_trailingWs_parenthesizer(v_a_2564_, v_a_2565_, v_a_2566_, v_a_2567_);
lean_dec(v_a_2567_);
lean_dec_ref(v_a_2566_);
lean_dec(v_a_2565_);
lean_dec_ref(v_a_2564_);
return v_res_2569_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2570_; lean_object* v___x_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2570_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2571_ = lean_obj_once(&l_Lake_Toml_key___closed__7, &l_Lake_Toml_key___closed__7_once, _init_l_Lake_Toml_key___closed__7);
v___x_2572_ = l_Lake_Toml_key_formatter___closed__0___boxed__const__1;
v___x_2573_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2573_, 0, v___x_2572_);
lean_closure_set(v___x_2573_, 1, v___x_2571_);
lean_closure_set(v___x_2573_, 2, v___x_2570_);
return v___x_2573_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; 
v___x_2574_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2575_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__0, &l_Lake_Toml_key_parenthesizer___closed__0_once, _init_l_Lake_Toml_key_parenthesizer___closed__0);
v___x_2576_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2576_, 0, v___x_2575_);
lean_closure_set(v___x_2576_, 1, v___x_2574_);
return v___x_2576_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; 
v___x_2577_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__1, &l_Lake_Toml_key_parenthesizer___closed__1_once, _init_l_Lake_Toml_key_parenthesizer___closed__1);
v___x_2578_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2579_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2579_, 0, v___x_2578_);
lean_closure_set(v___x_2579_, 1, v___x_2577_);
return v___x_2579_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__3(void){
_start:
{
uint8_t v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2582_; lean_object* v___x_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; 
v___x_2580_ = 0;
v___x_2581_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__2, &l_Lake_Toml_key_parenthesizer___closed__2_once, _init_l_Lake_Toml_key_parenthesizer___closed__2);
v___x_2582_ = ((lean_object*)(l_Lake_Toml_key___closed__3));
v___x_2583_ = lean_alloc_closure((void*)(l_Lake_Toml_simpleKey_parenthesizer___boxed), 5, 0);
v___x_2584_ = lean_box(v___x_2580_);
v___x_2585_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_2585_, 0, v___x_2583_);
lean_closure_set(v___x_2585_, 1, v___x_2582_);
lean_closure_set(v___x_2585_, 2, v___x_2581_);
lean_closure_set(v___x_2585_, 3, v___x_2584_);
return v___x_2585_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2588_; 
v___x_2586_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__3, &l_Lake_Toml_key_parenthesizer___closed__3_once, _init_l_Lake_Toml_key_parenthesizer___closed__3);
v___x_2587_ = ((lean_object*)(l_Lake_Toml_key___closed__2));
v___x_2588_ = lean_alloc_closure((void*)(l_Lean_Parser_setExpected_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2588_, 0, v___x_2587_);
lean_closure_set(v___x_2588_, 1, v___x_2586_);
return v___x_2588_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_key_parenthesizer(lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_){
_start:
{
lean_object* v___x_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; uint8_t v___x_2597_; lean_object* v___x_2598_; 
v___x_2594_ = ((lean_object*)(l_Lake_Toml_key___closed__0));
v___x_2595_ = ((lean_object*)(l_Lake_Toml_key___closed__1));
v___x_2596_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__4, &l_Lake_Toml_key_parenthesizer___closed__4_once, _init_l_Lake_Toml_key_parenthesizer___closed__4);
v___x_2597_ = 1;
v___x_2598_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2594_, v___x_2595_, v___x_2596_, v___x_2597_, v_a_2589_, v_a_2590_, v_a_2591_, v_a_2592_);
return v___x_2598_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_key_parenthesizer___boxed(lean_object* v_a_2599_, lean_object* v_a_2600_, lean_object* v_a_2601_, lean_object* v_a_2602_, lean_object* v_a_2603_){
_start:
{
lean_object* v_res_2604_; 
v_res_2604_ = l_Lake_Toml_key_parenthesizer(v_a_2599_, v_a_2600_, v_a_2601_, v_a_2602_);
lean_dec(v_a_2602_);
lean_dec_ref(v_a_2601_);
lean_dec(v_a_2600_);
lean_dec_ref(v_a_2599_);
return v_res_2604_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; 
v___x_2605_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2606_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5);
v___x_2607_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1;
v___x_2608_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2608_, 0, v___x_2607_);
lean_closure_set(v___x_2608_, 1, v___x_2606_);
lean_closure_set(v___x_2608_, 2, v___x_2605_);
return v___x_2608_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer(lean_object* v_val_2609_, lean_object* v_a_2610_, lean_object* v_a_2611_, lean_object* v_a_2612_, lean_object* v_a_2613_){
_start:
{
lean_object* v___x_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; uint8_t v___x_2624_; lean_object* v___x_2625_; 
v___x_2615_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0));
v___x_2616_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1));
v___x_2617_ = lean_alloc_closure((void*)(l_Lake_Toml_key_parenthesizer___boxed), 5, 0);
v___x_2618_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2619_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0);
lean_inc_ref(v___x_2618_);
v___x_2620_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2620_, 0, v___x_2618_);
lean_closure_set(v___x_2620_, 1, v_val_2609_);
v___x_2621_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2621_, 0, v___x_2619_);
lean_closure_set(v___x_2621_, 1, v___x_2620_);
v___x_2622_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2622_, 0, v___x_2618_);
lean_closure_set(v___x_2622_, 1, v___x_2621_);
v___x_2623_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2623_, 0, v___x_2617_);
lean_closure_set(v___x_2623_, 1, v___x_2622_);
v___x_2624_ = 1;
v___x_2625_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2615_, v___x_2616_, v___x_2623_, v___x_2624_, v_a_2610_, v_a_2611_, v_a_2612_, v_a_2613_);
return v___x_2625_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___boxed(lean_object* v_val_2626_, lean_object* v_a_2627_, lean_object* v_a_2628_, lean_object* v_a_2629_, lean_object* v_a_2630_, lean_object* v_a_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer(v_val_2626_, v_a_2627_, v_a_2628_, v_a_2629_, v_a_2630_);
lean_dec(v_a_2630_);
lean_dec_ref(v_a_2629_);
lean_dec(v_a_2628_);
lean_dec_ref(v_a_2627_);
return v_res_2632_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer___lam__0(lean_object* v___x_2633_, lean_object* v___x_2634_, lean_object* v___y_2635_, lean_object* v___y_2636_, lean_object* v___y_2637_, lean_object* v___y_2638_){
_start:
{
lean_object* v___x_2640_; 
v___x_2640_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(v___x_2633_, v___x_2634_, v___y_2635_, v___y_2636_, v___y_2637_, v___y_2638_);
return v___x_2640_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer___lam__0___boxed(lean_object* v___x_2641_, lean_object* v___x_2642_, lean_object* v___y_2643_, lean_object* v___y_2644_, lean_object* v___y_2645_, lean_object* v___y_2646_, lean_object* v___y_2647_){
_start:
{
lean_object* v_res_2648_; 
v_res_2648_ = l_Lake_Toml_stdTable_parenthesizer___lam__0(v___x_2641_, v___x_2642_, v___y_2643_, v___y_2644_, v___y_2645_, v___y_2646_);
lean_dec(v___y_2646_);
lean_dec_ref(v___y_2645_);
lean_dec(v___y_2644_);
lean_dec_ref(v___y_2643_);
return v_res_2648_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; 
v___x_2649_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2650_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__3));
v___x_2651_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
v___x_2652_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2652_, 0, v___x_2651_);
lean_closure_set(v___x_2652_, 1, v___x_2650_);
lean_closure_set(v___x_2652_, 2, v___x_2649_);
return v___x_2652_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; lean_object* v___x_2656_; 
v___x_2653_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2654_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__8, &l_Lake_Toml_stdTable___closed__8_once, _init_l_Lake_Toml_stdTable___closed__8);
v___x_2655_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
v___x_2656_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2656_, 0, v___x_2655_);
lean_closure_set(v___x_2656_, 1, v___x_2654_);
lean_closure_set(v___x_2656_, 2, v___x_2653_);
return v___x_2656_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__1, &l_Lake_Toml_stdTable_parenthesizer___closed__1_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__1);
v___x_2658_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2658_, 0, v___x_2657_);
return v___x_2658_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___f_2661_; 
v___x_2659_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__2, &l_Lake_Toml_stdTable_parenthesizer___closed__2_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__2);
v___x_2660_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__0, &l_Lake_Toml_stdTable_parenthesizer___closed__0_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__0);
v___f_2661_ = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_parenthesizer___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2661_, 0, v___x_2660_);
lean_closure_set(v___f_2661_, 1, v___x_2659_);
return v___f_2661_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; 
v___x_2662_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2663_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__17, &l_Lake_Toml_stdTable___closed__17_once, _init_l_Lake_Toml_stdTable___closed__17);
v___x_2664_ = l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1;
v___x_2665_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2665_, 0, v___x_2664_);
lean_closure_set(v___x_2665_, 1, v___x_2663_);
lean_closure_set(v___x_2665_, 2, v___x_2662_);
return v___x_2665_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_2666_; lean_object* v___x_2667_; lean_object* v___x_2668_; 
v___x_2666_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__4, &l_Lake_Toml_stdTable_parenthesizer___closed__4_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__4);
v___x_2667_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2668_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2668_, 0, v___x_2667_);
lean_closure_set(v___x_2668_, 1, v___x_2666_);
return v___x_2668_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v___x_2669_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__5, &l_Lake_Toml_stdTable_parenthesizer___closed__5_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__5);
v___x_2670_ = lean_alloc_closure((void*)(l_Lake_Toml_key_parenthesizer___boxed), 5, 0);
v___x_2671_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2671_, 0, v___x_2670_);
lean_closure_set(v___x_2671_, 1, v___x_2669_);
return v___x_2671_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v___x_2672_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__6, &l_Lake_Toml_stdTable_parenthesizer___closed__6_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__6);
v___x_2673_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2674_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2674_, 0, v___x_2673_);
lean_closure_set(v___x_2674_, 1, v___x_2672_);
return v___x_2674_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_2675_; lean_object* v___f_2676_; lean_object* v___x_2677_; 
v___x_2675_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__7, &l_Lake_Toml_stdTable_parenthesizer___closed__7_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__7);
v___f_2676_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__3, &l_Lake_Toml_stdTable_parenthesizer___closed__3_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__3);
v___x_2677_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2677_, 0, v___f_2676_);
lean_closure_set(v___x_2677_, 1, v___x_2675_);
return v___x_2677_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer(lean_object* v_a_2678_, lean_object* v_a_2679_, lean_object* v_a_2680_, lean_object* v_a_2681_){
_start:
{
lean_object* v___x_2683_; lean_object* v___x_2684_; lean_object* v___x_2685_; uint8_t v___x_2686_; lean_object* v___x_2687_; 
v___x_2683_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__0));
v___x_2684_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__1));
v___x_2685_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__8, &l_Lake_Toml_stdTable_parenthesizer___closed__8_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__8);
v___x_2686_ = 0;
v___x_2687_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2683_, v___x_2684_, v___x_2685_, v___x_2686_, v_a_2678_, v_a_2679_, v_a_2680_, v_a_2681_);
return v___x_2687_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer___boxed(lean_object* v_a_2688_, lean_object* v_a_2689_, lean_object* v_a_2690_, lean_object* v_a_2691_, lean_object* v_a_2692_){
_start:
{
lean_object* v_res_2693_; 
v_res_2693_ = l_Lake_Toml_stdTable_parenthesizer(v_a_2688_, v_a_2689_, v_a_2690_, v_a_2691_);
lean_dec(v_a_2691_);
lean_dec_ref(v_a_2690_);
lean_dec(v_a_2689_);
lean_dec_ref(v_a_2688_);
return v_res_2693_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___f_2696_; 
v___x_2694_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__1, &l_Lake_Toml_stdTable_parenthesizer___closed__1_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__1);
v___x_2695_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__0, &l_Lake_Toml_stdTable_parenthesizer___closed__0_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__0);
v___f_2696_ = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_parenthesizer___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2696_, 0, v___x_2695_);
lean_closure_set(v___f_2696_, 1, v___x_2694_);
return v___f_2696_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2697_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__4, &l_Lake_Toml_stdTable_parenthesizer___closed__4_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__4);
v___x_2698_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2698_, 0, v___x_2697_);
lean_closure_set(v___x_2698_, 1, v___x_2697_);
return v___x_2698_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v___x_2699_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__1, &l_Lake_Toml_arrayTable_parenthesizer___closed__1_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__1);
v___x_2700_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2701_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2701_, 0, v___x_2700_);
lean_closure_set(v___x_2701_, 1, v___x_2699_);
return v___x_2701_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; 
v___x_2702_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__2, &l_Lake_Toml_arrayTable_parenthesizer___closed__2_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__2);
v___x_2703_ = lean_alloc_closure((void*)(l_Lake_Toml_key_parenthesizer___boxed), 5, 0);
v___x_2704_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2704_, 0, v___x_2703_);
lean_closure_set(v___x_2704_, 1, v___x_2702_);
return v___x_2704_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; 
v___x_2705_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__3, &l_Lake_Toml_arrayTable_parenthesizer___closed__3_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__3);
v___x_2706_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2707_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2707_, 0, v___x_2706_);
lean_closure_set(v___x_2707_, 1, v___x_2705_);
return v___x_2707_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_2708_; lean_object* v___f_2709_; lean_object* v___x_2710_; 
v___x_2708_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__4, &l_Lake_Toml_arrayTable_parenthesizer___closed__4_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__4);
v___f_2709_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__0, &l_Lake_Toml_arrayTable_parenthesizer___closed__0_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__0);
v___x_2710_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2710_, 0, v___f_2709_);
lean_closure_set(v___x_2710_, 1, v___x_2708_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_parenthesizer(lean_object* v_a_2711_, lean_object* v_a_2712_, lean_object* v_a_2713_, lean_object* v_a_2714_){
_start:
{
lean_object* v___x_2716_; lean_object* v___x_2717_; lean_object* v___x_2718_; uint8_t v___x_2719_; lean_object* v___x_2720_; 
v___x_2716_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__0));
v___x_2717_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__1));
v___x_2718_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__5, &l_Lake_Toml_arrayTable_parenthesizer___closed__5_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__5);
v___x_2719_ = 0;
v___x_2720_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2716_, v___x_2717_, v___x_2718_, v___x_2719_, v_a_2711_, v_a_2712_, v_a_2713_, v_a_2714_);
return v___x_2720_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_parenthesizer___boxed(lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_, lean_object* v_a_2724_, lean_object* v_a_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l_Lake_Toml_arrayTable_parenthesizer(v_a_2721_, v_a_2722_, v_a_2723_, v_a_2724_);
lean_dec(v_a_2724_);
lean_dec_ref(v_a_2723_);
lean_dec(v_a_2722_);
lean_dec_ref(v_a_2721_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_table_parenthesizer(lean_object* v_a_2727_, lean_object* v_a_2728_, lean_object* v_a_2729_, lean_object* v_a_2730_){
_start:
{
lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; 
v___x_2732_ = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_parenthesizer___boxed), 5, 0);
v___x_2733_ = lean_alloc_closure((void*)(l_Lake_Toml_arrayTable_parenthesizer___boxed), 5, 0);
v___x_2734_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___x_2732_, v___x_2733_, v_a_2727_, v_a_2728_, v_a_2729_, v_a_2730_);
return v___x_2734_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_table_parenthesizer___boxed(lean_object* v_a_2735_, lean_object* v_a_2736_, lean_object* v_a_2737_, lean_object* v_a_2738_, lean_object* v_a_2739_){
_start:
{
lean_object* v_res_2740_; 
v_res_2740_ = l_Lake_Toml_table_parenthesizer(v_a_2735_, v_a_2736_, v_a_2737_, v_a_2738_);
lean_dec(v_a_2738_);
lean_dec_ref(v_a_2737_);
lean_dec(v_a_2736_);
lean_dec_ref(v_a_2735_);
return v_res_2740_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer(lean_object* v_val_2747_, lean_object* v_a_2748_, lean_object* v_a_2749_, lean_object* v_a_2750_, lean_object* v_a_2751_){
_start:
{
lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2757_; 
v___x_2753_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___closed__0));
v___x_2754_ = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2754_, 0, v_val_2747_);
v___x_2755_ = lean_alloc_closure((void*)(l_Lake_Toml_table_parenthesizer___boxed), 5, 0);
v___x_2756_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2756_, 0, v___x_2754_);
lean_closure_set(v___x_2756_, 1, v___x_2755_);
v___x_2757_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2753_, v___x_2756_, v_a_2748_, v_a_2749_, v_a_2750_, v_a_2751_);
return v___x_2757_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___boxed(lean_object* v_val_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_, lean_object* v_a_2762_, lean_object* v_a_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer(v_val_2758_, v_a_2759_, v_a_2760_, v_a_2761_, v_a_2762_);
lean_dec(v_a_2762_);
lean_dec_ref(v_a_2761_);
lean_dec(v_a_2760_);
lean_dec_ref(v_a_2759_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer___redArg(){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer___redArg___boxed(lean_object* v_a_2767_){
_start:
{
lean_object* v_res_2768_; 
v_res_2768_ = l_Lake_Toml_trailingSep_parenthesizer___redArg();
return v_res_2768_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer(lean_object* v_a_2769_, lean_object* v_a_2770_, lean_object* v_a_2771_, lean_object* v_a_2772_){
_start:
{
lean_object* v___x_2774_; 
v___x_2774_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_2774_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer___boxed(lean_object* v_a_2775_, lean_object* v_a_2776_, lean_object* v_a_2777_, lean_object* v_a_2778_, lean_object* v_a_2779_){
_start:
{
lean_object* v_res_2780_; 
v_res_2780_ = l_Lake_Toml_trailingSep_parenthesizer(v_a_2775_, v_a_2776_, v_a_2777_, v_a_2778_);
lean_dec(v_a_2778_);
lean_dec_ref(v_a_2777_);
lean_dec(v_a_2776_);
lean_dec_ref(v_a_2775_);
return v_res_2780_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(lean_object* v_val_2781_, lean_object* v_a_2782_, lean_object* v_a_2783_, lean_object* v_a_2784_, lean_object* v_a_2785_){
_start:
{
lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; uint8_t v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; 
v___x_2787_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0));
v___x_2788_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1));
v___x_2789_ = lean_alloc_closure((void*)(l_Lake_Toml_header_parenthesizer___boxed), 5, 0);
v___x_2790_ = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2790_, 0, v_val_2781_);
v___x_2791_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingSep_parenthesizer___boxed), 5, 0);
v___x_2792_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2792_, 0, v___x_2790_);
lean_closure_set(v___x_2792_, 1, v___x_2791_);
v___x_2793_ = 1;
v___x_2794_ = lean_box(v___x_2793_);
v___x_2795_ = lean_alloc_closure((void*)(l_Lake_Toml_sepByLinebreak_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2795_, 0, v___x_2792_);
lean_closure_set(v___x_2795_, 1, v___x_2794_);
v___x_2796_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2796_, 0, v___x_2789_);
lean_closure_set(v___x_2796_, 1, v___x_2795_);
v___x_2797_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2787_, v___x_2788_, v___x_2796_, v___x_2793_, v_a_2782_, v_a_2783_, v_a_2784_, v_a_2785_);
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer___boxed(lean_object* v_val_2798_, lean_object* v_a_2799_, lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_){
_start:
{
lean_object* v_res_2804_; 
v_res_2804_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(v_val_2798_, v_a_2799_, v_a_2800_, v_a_2801_, v_a_2802_);
lean_dec(v_a_2802_);
lean_dec_ref(v_a_2801_);
lean_dec(v_a_2800_);
lean_dec_ref(v_a_2799_);
return v_res_2804_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_val_parenthesizer(lean_object* v_a_2805_, lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_){
_start:
{
lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; uint8_t v___x_2813_; lean_object* v___x_2814_; 
v___x_2810_ = ((lean_object*)(l_Lake_Toml_val___closed__0));
v___x_2811_ = ((lean_object*)(l_Lake_Toml_val___closed__1));
v___x_2812_ = ((lean_object*)(l_Lake_Toml_val___closed__2));
v___x_2813_ = 1;
v___x_2814_ = l_Lake_Toml_recNodeWithAntiquot_parenthesizer(v___x_2810_, v___x_2811_, v___x_2812_, v___x_2813_, v_a_2805_, v_a_2806_, v_a_2807_, v_a_2808_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_val_parenthesizer___boxed(lean_object* v_a_2815_, lean_object* v_a_2816_, lean_object* v_a_2817_, lean_object* v_a_2818_, lean_object* v_a_2819_){
_start:
{
lean_object* v_res_2820_; 
v_res_2820_ = l_Lake_Toml_val_parenthesizer(v_a_2815_, v_a_2816_, v_a_2817_, v_a_2818_);
lean_dec(v_a_2818_);
lean_dec_ref(v_a_2817_);
lean_dec(v_a_2816_);
lean_dec_ref(v_a_2815_);
return v_res_2820_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_toml_parenthesizer(lean_object* v_a_2821_, lean_object* v_a_2822_, lean_object* v_a_2823_, lean_object* v_a_2824_){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = lean_alloc_closure((void*)(l_Lake_Toml_val_parenthesizer___boxed), 5, 0);
v___x_2827_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(v___x_2826_, v_a_2821_, v_a_2822_, v_a_2823_, v_a_2824_);
return v___x_2827_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_toml_parenthesizer___boxed(lean_object* v_a_2828_, lean_object* v_a_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_){
_start:
{
lean_object* v_res_2833_; 
v_res_2833_ = l_Lake_Toml_toml_parenthesizer(v_a_2828_, v_a_2829_, v_a_2830_, v_a_2831_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
lean_dec(v_a_2829_);
lean_dec_ref(v_a_2828_);
return v_res_2833_;
}
}
static lean_object* _init_l_Lake_Toml_toml___closed__0(void){
_start:
{
lean_object* v___x_2834_; lean_object* v___x_2835_; 
v___x_2834_ = l_Lake_Toml_val;
v___x_2835_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore(v___x_2834_);
return v___x_2835_;
}
}
static lean_object* _init_l_Lake_Toml_toml___closed__1(void){
_start:
{
lean_object* v___x_2836_; lean_object* v___x_2837_; lean_object* v___x_2838_; 
v___x_2836_ = lean_obj_once(&l_Lake_Toml_toml___closed__0, &l_Lake_Toml_toml___closed__0_once, _init_l_Lake_Toml_toml___closed__0);
v___x_2837_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1));
v___x_2838_ = l_Lean_Parser_withCache(v___x_2837_, v___x_2836_);
return v___x_2838_;
}
}
static lean_object* _init_l_Lake_Toml_toml(void){
_start:
{
lean_object* v___x_2839_; 
v___x_2839_ = lean_obj_once(&l_Lake_Toml_toml___closed__1, &l_Lake_Toml_toml___closed__1_once, _init_l_Lake_Toml_toml___closed__1);
return v___x_2839_;
}
}
lean_object* runtime_initialize_Lake_Toml_ParserUtil(uint8_t builtin);
lean_object* runtime_initialize_Lean_Parser(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter_Formatter(uint8_t builtin);
lean_object* runtime_initialize_Lean_PrettyPrinter_Parenthesizer(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lake_Toml_Grammar(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
