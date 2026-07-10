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
uint8_t lean_bool_not(uint8_t);
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
uint32_t v___x_6_; uint8_t v___x_7_; uint8_t v___x_8_; 
v___x_6_ = 9;
v___x_7_ = lean_uint32_dec_eq(v_c_1_, v___x_6_);
v___x_8_ = lean_bool_not(v___x_7_);
return v___x_8_;
}
}
else
{
return v___x_3_;
}
}
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
LEAN_EXPORT uint8_t l_Lake_Toml_wsFn___lam__0(uint32_t v_c_13_){
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
LEAN_EXPORT lean_object* l_Lake_Toml_wsFn___lam__0___boxed(lean_object* v_c_18_){
_start:
{
uint32_t v_c_boxed_19_; uint8_t v_res_20_; lean_object* v_r_21_; 
v_c_boxed_19_ = lean_unbox_uint32(v_c_18_);
lean_dec(v_c_18_);
v_res_20_ = l_Lake_Toml_wsFn___lam__0(v_c_boxed_19_);
v_r_21_ = lean_box(v_res_20_);
return v_r_21_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_wsFn(lean_object* v_a_23_, lean_object* v_a_24_){
_start:
{
lean_object* v___f_25_; lean_object* v___x_26_; 
v___f_25_ = ((lean_object*)(l_Lake_Toml_wsFn___closed__0));
v___x_26_ = l_Lean_Parser_takeWhileFn(v___f_25_, v_a_23_, v_a_24_);
return v___x_26_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_wsFn___boxed(lean_object* v_a_27_, lean_object* v_a_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Lake_Toml_wsFn(v_a_27_, v_a_28_);
lean_dec_ref(v_a_27_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(lean_object* v_c_31_, lean_object* v_s_32_){
_start:
{
lean_object* v_toInputContext_33_; lean_object* v_pos_34_; lean_object* v_errMsg_35_; uint8_t v___x_36_; uint8_t v___x_37_; 
v_toInputContext_33_ = lean_ctor_get(v_c_31_, 0);
v_pos_34_ = lean_ctor_get(v_s_32_, 2);
v_errMsg_35_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___closed__0));
v___x_36_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_33_, v_pos_34_);
v___x_37_ = 1;
if (v___x_36_ == 0)
{
lean_object* v_inputString_38_; uint32_t v_curr_39_; uint32_t v___x_40_; uint8_t v___x_41_; 
v_inputString_38_ = lean_ctor_get(v_toInputContext_33_, 0);
v_curr_39_ = lean_string_utf8_get_fast(v_inputString_38_, v_pos_34_);
v___x_40_ = 10;
v___x_41_ = lean_uint32_dec_eq(v_curr_39_, v___x_40_);
if (v___x_41_ == 0)
{
lean_object* v___x_42_; lean_object* v___x_43_; 
v___x_42_ = lean_box(0);
v___x_43_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_32_, v_errMsg_35_, v___x_42_, v___x_37_);
return v___x_43_;
}
else
{
lean_object* v___x_44_; 
lean_inc(v_pos_34_);
v___x_44_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_32_, v_c_31_, v_pos_34_);
lean_dec(v_pos_34_);
return v___x_44_;
}
}
else
{
lean_object* v___x_45_; lean_object* v___x_46_; 
v___x_45_ = lean_box(0);
v___x_46_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_32_, v_errMsg_35_, v___x_45_, v___x_37_);
return v___x_46_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___boxed(lean_object* v_c_47_, lean_object* v_s_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_47_, v_s_48_);
lean_dec_ref(v_c_47_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_newlineFn(lean_object* v_c_54_, lean_object* v_s_55_){
_start:
{
lean_object* v_toInputContext_56_; lean_object* v_pos_57_; uint8_t v___x_58_; 
v_toInputContext_56_ = lean_ctor_get(v_c_54_, 0);
v_pos_57_ = lean_ctor_get(v_s_55_, 2);
v___x_58_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_56_, v_pos_57_);
if (v___x_58_ == 0)
{
lean_object* v_inputString_59_; uint32_t v_curr_60_; uint32_t v___x_61_; uint8_t v___x_62_; 
v_inputString_59_ = lean_ctor_get(v_toInputContext_56_, 0);
v_curr_60_ = lean_string_utf8_get_fast(v_inputString_59_, v_pos_57_);
v___x_61_ = 10;
v___x_62_ = lean_uint32_dec_eq(v_curr_60_, v___x_61_);
if (v___x_62_ == 0)
{
uint32_t v___x_63_; uint8_t v___x_64_; 
v___x_63_ = 13;
v___x_64_ = lean_uint32_dec_eq(v_curr_60_, v___x_63_);
if (v___x_64_ == 0)
{
uint8_t v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; 
v___x_65_ = 1;
v___x_66_ = ((lean_object*)(l_Lake_Toml_newlineFn___closed__1));
v___x_67_ = l_Lake_Toml_mkUnexpectedCharError(v_s_55_, v_curr_60_, v___x_66_, v___x_65_);
return v___x_67_;
}
else
{
lean_object* v___x_68_; lean_object* v___x_69_; 
lean_inc(v_pos_57_);
v___x_68_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_55_, v_c_54_, v_pos_57_);
lean_dec(v_pos_57_);
v___x_69_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_54_, v___x_68_);
return v___x_69_;
}
}
else
{
lean_object* v___x_70_; 
lean_inc(v_pos_57_);
v___x_70_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_55_, v_c_54_, v_pos_57_);
lean_dec(v_pos_57_);
return v___x_70_;
}
}
else
{
lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_71_ = ((lean_object*)(l_Lake_Toml_newlineFn___closed__1));
v___x_72_ = l_Lean_Parser_ParserState_mkEOIError(v_s_55_, v___x_71_);
return v___x_72_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_newlineFn___boxed(lean_object* v_c_73_, lean_object* v_s_74_){
_start:
{
lean_object* v_res_75_; 
v_res_75_ = l_Lake_Toml_newlineFn(v_c_73_, v_s_74_);
lean_dec_ref(v_c_73_);
return v_res_75_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(lean_object* v_a_77_, lean_object* v_a_78_){
_start:
{
lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_79_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___closed__0));
v___x_80_ = l_Lean_Parser_takeUntilFn(v___x_79_, v_a_77_, v_a_78_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___boxed(lean_object* v_a_81_, lean_object* v_a_82_){
_start:
{
lean_object* v_res_83_; 
v_res_83_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(v_a_81_, v_a_82_);
lean_dec_ref(v_a_81_);
return v_res_83_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(lean_object* v_x_84_, lean_object* v_x_85_){
_start:
{
if (lean_obj_tag(v_x_84_) == 0)
{
if (lean_obj_tag(v_x_85_) == 0)
{
uint8_t v___x_86_; 
v___x_86_ = 1;
return v___x_86_;
}
else
{
uint8_t v___x_87_; 
lean_dec_ref_known(v_x_85_, 1);
v___x_87_ = 0;
return v___x_87_;
}
}
else
{
if (lean_obj_tag(v_x_85_) == 0)
{
uint8_t v___x_88_; 
lean_dec_ref_known(v_x_84_, 1);
v___x_88_ = 0;
return v___x_88_;
}
else
{
lean_object* v_val_89_; lean_object* v_val_90_; uint8_t v___x_91_; 
v_val_89_ = lean_ctor_get(v_x_84_, 0);
lean_inc(v_val_89_);
lean_dec_ref_known(v_x_84_, 1);
v_val_90_ = lean_ctor_get(v_x_85_, 0);
lean_inc(v_val_90_);
lean_dec_ref_known(v_x_85_, 1);
v___x_91_ = l_Lean_Parser_instBEqError_beq(v_val_89_, v_val_90_);
return v___x_91_;
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0___boxed(lean_object* v_x_92_, lean_object* v_x_93_){
_start:
{
uint8_t v_res_94_; lean_object* v_r_95_; 
v_res_94_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_x_92_, v_x_93_);
v_r_95_ = lean_box(v_res_94_);
return v_r_95_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_commentFn(lean_object* v_a_100_, lean_object* v_a_101_){
_start:
{
uint32_t v___x_102_; lean_object* v___x_103_; lean_object* v_s_104_; lean_object* v_errorMsg_105_; lean_object* v___x_106_; uint8_t v___x_107_; uint8_t v___x_108_; 
v___x_102_ = 35;
v___x_103_ = ((lean_object*)(l_Lake_Toml_commentFn___closed__1));
v_s_104_ = l_Lake_Toml_chFn(v___x_102_, v___x_103_, v_a_100_, v_a_101_);
v_errorMsg_105_ = lean_ctor_get(v_s_104_, 4);
lean_inc(v_errorMsg_105_);
v___x_106_ = lean_box(0);
v___x_107_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_105_, v___x_106_);
v___x_108_ = lean_bool_not(v___x_107_);
if (v___x_108_ == 0)
{
lean_object* v___x_109_; 
v___x_109_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(v_a_100_, v_s_104_);
return v___x_109_;
}
else
{
return v_s_104_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_commentFn___boxed(lean_object* v_a_110_, lean_object* v_a_111_){
_start:
{
lean_object* v_res_112_; 
v_res_112_ = l_Lake_Toml_commentFn(v_a_110_, v_a_111_);
lean_dec_ref(v_a_110_);
return v_res_112_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_wsNewlineFn(lean_object* v_c_113_, lean_object* v_s_114_){
_start:
{
lean_object* v_toInputContext_115_; lean_object* v_pos_116_; uint8_t v___x_120_; 
v_toInputContext_115_ = lean_ctor_get(v_c_113_, 0);
v_pos_116_ = lean_ctor_get(v_s_114_, 2);
v___x_120_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_115_, v_pos_116_);
if (v___x_120_ == 0)
{
lean_object* v_inputString_121_; uint32_t v_curr_122_; uint8_t v___y_124_; uint32_t v___x_136_; uint8_t v___x_137_; 
v_inputString_121_ = lean_ctor_get(v_toInputContext_115_, 0);
v_curr_122_ = lean_string_utf8_get_fast(v_inputString_121_, v_pos_116_);
v___x_136_ = 32;
v___x_137_ = lean_uint32_dec_eq(v_curr_122_, v___x_136_);
if (v___x_137_ == 0)
{
uint32_t v___x_138_; uint8_t v___x_139_; 
v___x_138_ = 9;
v___x_139_ = lean_uint32_dec_eq(v_curr_122_, v___x_138_);
v___y_124_ = v___x_139_;
goto v___jp_123_;
}
else
{
v___y_124_ = v___x_137_;
goto v___jp_123_;
}
v___jp_123_:
{
if (v___y_124_ == 0)
{
uint32_t v___x_125_; uint8_t v___x_126_; 
v___x_125_ = 10;
v___x_126_ = lean_uint32_dec_eq(v_curr_122_, v___x_125_);
if (v___x_126_ == 0)
{
uint32_t v___x_127_; uint8_t v___x_128_; 
v___x_127_ = 13;
v___x_128_ = lean_uint32_dec_eq(v_curr_122_, v___x_127_);
if (v___x_128_ == 0)
{
return v_s_114_;
}
else
{
lean_object* v___x_129_; lean_object* v_s_130_; lean_object* v_errorMsg_131_; lean_object* v___x_132_; uint8_t v___x_133_; uint8_t v___x_134_; 
lean_inc(v_pos_116_);
v___x_129_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_114_, v_c_113_, v_pos_116_);
lean_dec(v_pos_116_);
v_s_130_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_113_, v___x_129_);
v_errorMsg_131_ = lean_ctor_get(v_s_130_, 4);
lean_inc(v_errorMsg_131_);
v___x_132_ = lean_box(0);
v___x_133_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_131_, v___x_132_);
v___x_134_ = lean_bool_not(v___x_133_);
if (v___x_134_ == 0)
{
v_s_114_ = v_s_130_;
goto _start;
}
else
{
return v_s_130_;
}
}
}
else
{
lean_inc(v_pos_116_);
goto v___jp_117_;
}
}
else
{
lean_inc(v_pos_116_);
goto v___jp_117_;
}
}
}
else
{
return v_s_114_;
}
v___jp_117_:
{
lean_object* v___x_118_; 
v___x_118_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_114_, v_c_113_, v_pos_116_);
lean_dec(v_pos_116_);
v_s_114_ = v___x_118_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_wsNewlineFn___boxed(lean_object* v_c_140_, lean_object* v_s_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Lake_Toml_wsNewlineFn(v_c_140_, v_s_141_);
lean_dec_ref(v_c_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingFn(lean_object* v_c_143_, lean_object* v_s_144_){
_start:
{
lean_object* v_toInputContext_145_; lean_object* v_pos_146_; uint8_t v___x_150_; 
v_toInputContext_145_ = lean_ctor_get(v_c_143_, 0);
v_pos_146_ = lean_ctor_get(v_s_144_, 2);
v___x_150_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_145_, v_pos_146_);
if (v___x_150_ == 0)
{
lean_object* v_inputString_151_; uint32_t v_curr_152_; uint8_t v___y_154_; uint32_t v___x_175_; uint8_t v___x_176_; 
v_inputString_151_ = lean_ctor_get(v_toInputContext_145_, 0);
v_curr_152_ = lean_string_utf8_get_fast(v_inputString_151_, v_pos_146_);
v___x_175_ = 32;
v___x_176_ = lean_uint32_dec_eq(v_curr_152_, v___x_175_);
if (v___x_176_ == 0)
{
uint32_t v___x_177_; uint8_t v___x_178_; 
v___x_177_ = 9;
v___x_178_ = lean_uint32_dec_eq(v_curr_152_, v___x_177_);
v___y_154_ = v___x_178_;
goto v___jp_153_;
}
else
{
v___y_154_ = v___x_176_;
goto v___jp_153_;
}
v___jp_153_:
{
if (v___y_154_ == 0)
{
uint32_t v___x_155_; uint8_t v___x_156_; 
v___x_155_ = 10;
v___x_156_ = lean_uint32_dec_eq(v_curr_152_, v___x_155_);
if (v___x_156_ == 0)
{
uint32_t v___x_157_; uint8_t v___x_158_; 
v___x_157_ = 13;
v___x_158_ = lean_uint32_dec_eq(v_curr_152_, v___x_157_);
if (v___x_158_ == 0)
{
uint32_t v___x_159_; uint8_t v___x_160_; 
v___x_159_ = 35;
v___x_160_ = lean_uint32_dec_eq(v_curr_152_, v___x_159_);
if (v___x_160_ == 0)
{
return v_s_144_;
}
else
{
lean_object* v___x_161_; lean_object* v_s_162_; lean_object* v_errorMsg_163_; lean_object* v___x_164_; uint8_t v___x_165_; uint8_t v___x_166_; 
lean_inc(v_pos_146_);
v___x_161_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_144_, v_c_143_, v_pos_146_);
lean_dec(v_pos_146_);
v_s_162_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(v_c_143_, v___x_161_);
v_errorMsg_163_ = lean_ctor_get(v_s_162_, 4);
lean_inc(v_errorMsg_163_);
v___x_164_ = lean_box(0);
v___x_165_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_163_, v___x_164_);
v___x_166_ = lean_bool_not(v___x_165_);
if (v___x_166_ == 0)
{
v_s_144_ = v_s_162_;
goto _start;
}
else
{
return v_s_162_;
}
}
}
else
{
lean_object* v___x_168_; lean_object* v_s_169_; lean_object* v_errorMsg_170_; lean_object* v___x_171_; uint8_t v___x_172_; uint8_t v___x_173_; 
lean_inc(v_pos_146_);
v___x_168_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_144_, v_c_143_, v_pos_146_);
lean_dec(v_pos_146_);
v_s_169_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_143_, v___x_168_);
v_errorMsg_170_ = lean_ctor_get(v_s_169_, 4);
lean_inc(v_errorMsg_170_);
v___x_171_ = lean_box(0);
v___x_172_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_170_, v___x_171_);
v___x_173_ = lean_bool_not(v___x_172_);
if (v___x_173_ == 0)
{
v_s_144_ = v_s_169_;
goto _start;
}
else
{
return v_s_169_;
}
}
}
else
{
lean_inc(v_pos_146_);
goto v___jp_147_;
}
}
else
{
lean_inc(v_pos_146_);
goto v___jp_147_;
}
}
}
else
{
return v_s_144_;
}
v___jp_147_:
{
lean_object* v___x_148_; 
v___x_148_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_144_, v_c_143_, v_pos_146_);
lean_dec(v_pos_146_);
v_s_144_ = v___x_148_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingFn___boxed(lean_object* v_c_179_, lean_object* v_s_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lake_Toml_trailingFn(v_c_179_, v_s_180_);
lean_dec_ref(v_c_179_);
return v_res_181_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_isEscapeChar(uint32_t v_c_182_){
_start:
{
uint8_t v___y_184_; uint32_t v___x_195_; uint8_t v___x_196_; 
v___x_195_ = 98;
v___x_196_ = lean_uint32_dec_eq(v_c_182_, v___x_195_);
if (v___x_196_ == 0)
{
uint32_t v___x_197_; uint8_t v___x_198_; 
v___x_197_ = 116;
v___x_198_ = lean_uint32_dec_eq(v_c_182_, v___x_197_);
v___y_184_ = v___x_198_;
goto v___jp_183_;
}
else
{
v___y_184_ = v___x_196_;
goto v___jp_183_;
}
v___jp_183_:
{
if (v___y_184_ == 0)
{
uint32_t v___x_185_; uint8_t v___x_186_; 
v___x_185_ = 110;
v___x_186_ = lean_uint32_dec_eq(v_c_182_, v___x_185_);
if (v___x_186_ == 0)
{
uint32_t v___x_187_; uint8_t v___x_188_; 
v___x_187_ = 102;
v___x_188_ = lean_uint32_dec_eq(v_c_182_, v___x_187_);
if (v___x_188_ == 0)
{
uint32_t v___x_189_; uint8_t v___x_190_; 
v___x_189_ = 114;
v___x_190_ = lean_uint32_dec_eq(v_c_182_, v___x_189_);
if (v___x_190_ == 0)
{
uint32_t v___x_191_; uint8_t v___x_192_; 
v___x_191_ = 34;
v___x_192_ = lean_uint32_dec_eq(v_c_182_, v___x_191_);
if (v___x_192_ == 0)
{
uint32_t v___x_193_; uint8_t v___x_194_; 
v___x_193_ = 92;
v___x_194_ = lean_uint32_dec_eq(v_c_182_, v___x_193_);
return v___x_194_;
}
else
{
return v___x_192_;
}
}
else
{
return v___x_190_;
}
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
return v___y_184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_isEscapeChar___boxed(lean_object* v_c_199_){
_start:
{
uint32_t v_c_boxed_200_; uint8_t v_res_201_; lean_object* v_r_202_; 
v_c_boxed_200_ = lean_unbox_uint32(v_c_199_);
lean_dec(v_c_199_);
v_res_201_ = l_Lake_Toml_isEscapeChar(v_c_boxed_200_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0(lean_object* v___y_203_, lean_object* v___y_204_){
_start:
{
lean_object* v_s_205_; lean_object* v_errorMsg_206_; lean_object* v___x_207_; uint8_t v___x_208_; uint8_t v___x_209_; 
v_s_205_ = l_Lake_Toml_wsFn(v___y_203_, v___y_204_);
v_errorMsg_206_ = lean_ctor_get(v_s_205_, 4);
lean_inc(v_errorMsg_206_);
v___x_207_ = lean_box(0);
v___x_208_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_206_, v___x_207_);
v___x_209_ = lean_bool_not(v___x_208_);
if (v___x_209_ == 0)
{
lean_object* v_s_210_; lean_object* v_errorMsg_211_; uint8_t v___x_212_; uint8_t v___x_213_; 
v_s_210_ = l_Lake_Toml_newlineFn(v___y_203_, v_s_205_);
v_errorMsg_211_ = lean_ctor_get(v_s_210_, 4);
lean_inc(v_errorMsg_211_);
v___x_212_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_211_, v___x_207_);
v___x_213_ = lean_bool_not(v___x_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; 
v___x_214_ = l_Lake_Toml_wsNewlineFn(v___y_203_, v_s_210_);
return v___x_214_;
}
else
{
return v_s_210_;
}
}
else
{
return v_s_205_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0___boxed(lean_object* v___y_215_, lean_object* v___y_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0(v___y_215_, v___y_216_);
lean_dec_ref(v___y_215_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1(lean_object* v___y_218_, lean_object* v___y_219_){
_start:
{
lean_object* v_s_220_; lean_object* v_errorMsg_221_; lean_object* v___x_222_; uint8_t v___x_223_; uint8_t v___x_224_; 
v_s_220_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v___y_218_, v___y_219_);
v_errorMsg_221_ = lean_ctor_get(v_s_220_, 4);
lean_inc(v_errorMsg_221_);
v___x_222_ = lean_box(0);
v___x_223_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_221_, v___x_222_);
v___x_224_ = lean_bool_not(v___x_223_);
if (v___x_224_ == 0)
{
lean_object* v___x_225_; 
v___x_225_ = l_Lake_Toml_wsNewlineFn(v___y_218_, v_s_220_);
return v___x_225_;
}
else
{
return v_s_220_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1___boxed(lean_object* v___y_226_, lean_object* v___y_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1(v___y_226_, v___y_227_);
lean_dec_ref(v___y_226_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(lean_object* v_c_229_, lean_object* v_x_230_, lean_object* v_x_231_){
_start:
{
lean_object* v_zero_232_; uint8_t v_isZero_233_; 
v_zero_232_ = lean_unsigned_to_nat(0u);
v_isZero_233_ = lean_nat_dec_eq(v_x_230_, v_zero_232_);
if (v_isZero_233_ == 1)
{
lean_dec(v_x_230_);
return v_x_231_;
}
else
{
lean_object* v_s_234_; lean_object* v_errorMsg_235_; lean_object* v___x_236_; uint8_t v___x_237_; uint8_t v___x_238_; 
v_s_234_ = l_Lean_Parser_hexDigitFn(v_c_229_, v_x_231_);
v_errorMsg_235_ = lean_ctor_get(v_s_234_, 4);
lean_inc(v_errorMsg_235_);
v___x_236_ = lean_box(0);
v___x_237_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_235_, v___x_236_);
v___x_238_ = lean_bool_not(v___x_237_);
if (v___x_238_ == 0)
{
lean_object* v_one_239_; lean_object* v_n_240_; 
v_one_239_ = lean_unsigned_to_nat(1u);
v_n_240_ = lean_nat_sub(v_x_230_, v_one_239_);
lean_dec(v_x_230_);
v_x_230_ = v_n_240_;
v_x_231_ = v_s_234_;
goto _start;
}
else
{
lean_dec(v_x_230_);
return v_s_234_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0___boxed(lean_object* v_c_242_, lean_object* v_x_243_, lean_object* v_x_244_){
_start:
{
lean_object* v_res_245_; 
v_res_245_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(v_c_242_, v_x_243_, v_x_244_);
lean_dec_ref(v_c_242_);
return v_res_245_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(uint8_t v_stringGap_255_, lean_object* v_c_256_, lean_object* v_s_257_){
_start:
{
lean_object* v_toInputContext_258_; lean_object* v_pos_259_; lean_object* v___x_260_; lean_object* v_expected_261_; uint8_t v___x_262_; 
v_toInputContext_258_ = lean_ctor_get(v_c_256_, 0);
v_pos_259_ = lean_ctor_get(v_s_257_, 2);
v___x_260_ = lean_box(0);
v_expected_261_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__1));
v___x_262_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_258_, v_pos_259_);
if (v___x_262_ == 0)
{
lean_object* v_inputString_263_; uint32_t v_curr_264_; uint8_t v___x_265_; 
v_inputString_263_ = lean_ctor_get(v_toInputContext_258_, 0);
v_curr_264_ = lean_string_utf8_get_fast(v_inputString_263_, v_pos_259_);
v___x_265_ = l_Lake_Toml_isEscapeChar(v_curr_264_);
if (v___x_265_ == 0)
{
uint32_t v___x_266_; uint8_t v___x_267_; 
v___x_266_ = 117;
v___x_267_ = lean_uint32_dec_eq(v_curr_264_, v___x_266_);
if (v___x_267_ == 0)
{
uint32_t v___x_268_; uint8_t v___x_269_; 
v___x_268_ = 85;
v___x_269_ = lean_uint32_dec_eq(v_curr_264_, v___x_268_);
if (v___x_269_ == 0)
{
lean_object* v___f_270_; uint8_t v___x_271_; lean_object* v_p_273_; uint32_t v___x_278_; uint8_t v___x_279_; 
v___f_270_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__2));
v___x_271_ = 1;
v___x_278_ = 32;
v___x_279_ = lean_uint32_dec_eq(v_curr_264_, v___x_278_);
if (v___x_279_ == 0)
{
uint32_t v___x_280_; uint8_t v___x_281_; 
v___x_280_ = 9;
v___x_281_ = lean_uint32_dec_eq(v_curr_264_, v___x_280_);
if (v___x_281_ == 0)
{
uint32_t v___x_282_; uint8_t v___x_283_; 
v___x_282_ = 10;
v___x_283_ = lean_uint32_dec_eq(v_curr_264_, v___x_282_);
if (v___x_283_ == 0)
{
uint32_t v___x_284_; uint8_t v___x_285_; 
v___x_284_ = 13;
v___x_285_ = lean_uint32_dec_eq(v_curr_264_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec_ref(v_c_256_);
v___x_286_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__4));
v___x_287_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_257_, v___x_286_, v___x_260_, v___x_271_);
return v___x_287_;
}
else
{
lean_object* v___f_288_; 
v___f_288_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__5));
v_p_273_ = v___f_288_;
goto v___jp_272_;
}
}
else
{
lean_object* v___x_289_; 
v___x_289_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__6));
v_p_273_ = v___x_289_;
goto v___jp_272_;
}
}
else
{
v_p_273_ = v___f_270_;
goto v___jp_272_;
}
}
else
{
v_p_273_ = v___f_270_;
goto v___jp_272_;
}
v___jp_272_:
{
if (v_stringGap_255_ == 0)
{
lean_object* v___x_274_; lean_object* v___x_275_; 
lean_dec_ref(v_c_256_);
v___x_274_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__3));
v___x_275_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_257_, v___x_274_, v_expected_261_, v___x_271_);
return v___x_275_;
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; 
lean_inc(v_pos_259_);
v___x_276_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_257_, v_c_256_, v_pos_259_);
lean_dec(v_pos_259_);
lean_inc_ref(v_p_273_);
v___x_277_ = lean_apply_2(v_p_273_, v_c_256_, v___x_276_);
return v___x_277_;
}
}
}
else
{
lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
lean_inc(v_pos_259_);
v___x_290_ = lean_unsigned_to_nat(8u);
v___x_291_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_257_, v_c_256_, v_pos_259_);
lean_dec(v_pos_259_);
v___x_292_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(v_c_256_, v___x_290_, v___x_291_);
lean_dec_ref(v_c_256_);
return v___x_292_;
}
}
else
{
lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; 
lean_inc(v_pos_259_);
v___x_293_ = lean_unsigned_to_nat(4u);
v___x_294_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_257_, v_c_256_, v_pos_259_);
lean_dec(v_pos_259_);
v___x_295_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00__private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(v_c_256_, v___x_293_, v___x_294_);
lean_dec_ref(v_c_256_);
return v___x_295_;
}
}
else
{
lean_object* v___x_296_; 
lean_inc(v_pos_259_);
v___x_296_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_257_, v_c_256_, v_pos_259_);
lean_dec(v_pos_259_);
lean_dec_ref(v_c_256_);
return v___x_296_;
}
}
else
{
lean_object* v___x_297_; 
lean_dec_ref(v_c_256_);
v___x_297_ = l_Lean_Parser_ParserState_mkEOIError(v_s_257_, v_expected_261_);
return v___x_297_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___boxed(lean_object* v_stringGap_298_, lean_object* v_c_299_, lean_object* v_s_300_){
_start:
{
uint8_t v_stringGap_boxed_301_; lean_object* v_res_302_; 
v_stringGap_boxed_301_ = lean_unbox(v_stringGap_298_);
v_res_302_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(v_stringGap_boxed_301_, v_c_299_, v_s_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn(lean_object* v_startPos_304_, lean_object* v_c_305_, lean_object* v_s_306_){
_start:
{
lean_object* v_toInputContext_307_; lean_object* v_pos_308_; uint8_t v___x_309_; 
v_toInputContext_307_ = lean_ctor_get(v_c_305_, 0);
v_pos_308_ = lean_ctor_get(v_s_306_, 2);
v___x_309_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_307_, v_pos_308_);
if (v___x_309_ == 0)
{
lean_object* v_inputString_310_; uint32_t v_curr_311_; uint32_t v___x_312_; uint8_t v___x_313_; 
v_inputString_310_ = lean_ctor_get(v_toInputContext_307_, 0);
v_curr_311_ = lean_string_utf8_get_fast(v_inputString_310_, v_pos_308_);
v___x_312_ = 34;
v___x_313_ = lean_uint32_dec_eq(v_curr_311_, v___x_312_);
if (v___x_313_ == 0)
{
uint32_t v___x_314_; uint8_t v___x_315_; 
v___x_314_ = 92;
v___x_315_ = lean_uint32_dec_eq(v_curr_311_, v___x_314_);
if (v___x_315_ == 0)
{
uint8_t v___x_316_; 
v___x_316_ = l_Lake_Toml_isControlChar(v_curr_311_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; 
lean_inc(v_pos_308_);
v___x_317_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_306_, v_c_305_, v_pos_308_);
lean_dec(v_pos_308_);
v_s_306_ = v___x_317_;
goto _start;
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec_ref(v_c_305_);
lean_dec(v_startPos_304_);
v___x_319_ = lean_box(0);
v___x_320_ = l_Lake_Toml_mkUnexpectedCharError(v_s_306_, v_curr_311_, v___x_319_, v___x_316_);
return v___x_320_;
}
}
else
{
lean_object* v___x_321_; lean_object* v_s_322_; lean_object* v_errorMsg_323_; lean_object* v___x_324_; uint8_t v___x_325_; uint8_t v___x_326_; 
lean_inc(v_pos_308_);
v___x_321_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_306_, v_c_305_, v_pos_308_);
lean_dec(v_pos_308_);
lean_inc_ref(v_c_305_);
v_s_322_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(v___x_313_, v_c_305_, v___x_321_);
v_errorMsg_323_ = lean_ctor_get(v_s_322_, 4);
lean_inc(v_errorMsg_323_);
v___x_324_ = lean_box(0);
v___x_325_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_323_, v___x_324_);
v___x_326_ = lean_bool_not(v___x_325_);
if (v___x_326_ == 0)
{
v_s_306_ = v_s_322_;
goto _start;
}
else
{
lean_dec_ref(v_c_305_);
lean_dec(v_startPos_304_);
return v_s_322_;
}
}
}
else
{
lean_object* v___x_328_; 
lean_inc(v_pos_308_);
lean_dec(v_startPos_304_);
v___x_328_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_306_, v_c_305_, v_pos_308_);
lean_dec(v_pos_308_);
lean_dec_ref(v_c_305_);
return v___x_328_;
}
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; 
lean_dec_ref(v_c_305_);
v___x_329_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn___closed__0));
v___x_330_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_306_, v___x_329_, v_startPos_304_);
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicStringFn(lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_pos_337_; uint32_t v___x_338_; lean_object* v___x_339_; lean_object* v_s_340_; lean_object* v_errorMsg_341_; lean_object* v___x_342_; uint8_t v___x_343_; uint8_t v___x_344_; 
v_pos_337_ = lean_ctor_get(v_a_336_, 2);
lean_inc(v_pos_337_);
v___x_338_ = 34;
v___x_339_ = ((lean_object*)(l_Lake_Toml_basicStringFn___closed__1));
v_s_340_ = l_Lake_Toml_chFn(v___x_338_, v___x_339_, v_a_335_, v_a_336_);
v_errorMsg_341_ = lean_ctor_get(v_s_340_, 4);
lean_inc(v_errorMsg_341_);
v___x_342_ = lean_box(0);
v___x_343_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_341_, v___x_342_);
v___x_344_ = lean_bool_not(v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; 
v___x_345_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn(v_pos_337_, v_a_335_, v_s_340_);
return v___x_345_;
}
else
{
lean_dec(v_pos_337_);
lean_dec_ref(v_a_335_);
return v_s_340_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(lean_object* v_startPos_347_, lean_object* v_c_348_, lean_object* v_s_349_){
_start:
{
lean_object* v_toInputContext_350_; lean_object* v_pos_351_; uint8_t v___x_352_; 
v_toInputContext_350_ = lean_ctor_get(v_c_348_, 0);
v_pos_351_ = lean_ctor_get(v_s_349_, 2);
v___x_352_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_350_, v_pos_351_);
if (v___x_352_ == 0)
{
lean_object* v_inputString_353_; uint32_t v_curr_354_; uint32_t v___x_355_; uint8_t v___x_356_; 
v_inputString_353_ = lean_ctor_get(v_toInputContext_350_, 0);
v_curr_354_ = lean_string_utf8_get_fast(v_inputString_353_, v_pos_351_);
v___x_355_ = 39;
v___x_356_ = lean_uint32_dec_eq(v_curr_354_, v___x_355_);
if (v___x_356_ == 0)
{
uint8_t v___x_357_; 
v___x_357_ = l_Lake_Toml_isControlChar(v_curr_354_);
if (v___x_357_ == 0)
{
lean_object* v___x_358_; 
lean_inc(v_pos_351_);
v___x_358_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_349_, v_c_348_, v_pos_351_);
lean_dec(v_pos_351_);
v_s_349_ = v___x_358_;
goto _start;
}
else
{
lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec(v_startPos_347_);
v___x_360_ = lean_box(0);
v___x_361_ = l_Lake_Toml_mkUnexpectedCharError(v_s_349_, v_curr_354_, v___x_360_, v___x_357_);
return v___x_361_;
}
}
else
{
lean_object* v___x_362_; 
lean_inc(v_pos_351_);
lean_dec(v_startPos_347_);
v___x_362_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_349_, v_c_348_, v_pos_351_);
lean_dec(v_pos_351_);
return v___x_362_;
}
}
else
{
lean_object* v___x_363_; lean_object* v___x_364_; 
v___x_363_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___closed__0));
v___x_364_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_349_, v___x_363_, v_startPos_347_);
return v___x_364_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___boxed(lean_object* v_startPos_365_, lean_object* v_c_366_, lean_object* v_s_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(v_startPos_365_, v_c_366_, v_s_367_);
lean_dec_ref(v_c_366_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalStringFn(lean_object* v_a_373_, lean_object* v_a_374_){
_start:
{
lean_object* v_pos_375_; uint32_t v___x_376_; lean_object* v___x_377_; lean_object* v_s_378_; lean_object* v_errorMsg_379_; lean_object* v___x_380_; uint8_t v___x_381_; uint8_t v___x_382_; 
v_pos_375_ = lean_ctor_get(v_a_374_, 2);
lean_inc(v_pos_375_);
v___x_376_ = 39;
v___x_377_ = ((lean_object*)(l_Lake_Toml_literalStringFn___closed__1));
v_s_378_ = l_Lake_Toml_chFn(v___x_376_, v___x_377_, v_a_373_, v_a_374_);
v_errorMsg_379_ = lean_ctor_get(v_s_378_, 4);
lean_inc(v_errorMsg_379_);
v___x_380_ = lean_box(0);
v___x_381_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_379_, v___x_380_);
v___x_382_ = lean_bool_not(v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
v___x_383_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(v_pos_375_, v_a_373_, v_s_378_);
return v___x_383_;
}
else
{
lean_dec(v_pos_375_);
return v_s_378_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalStringFn___boxed(lean_object* v_a_384_, lean_object* v_a_385_){
_start:
{
lean_object* v_res_386_; 
v_res_386_ = l_Lake_Toml_literalStringFn(v_a_384_, v_a_385_);
lean_dec_ref(v_a_384_);
return v_res_386_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(lean_object* v_startPos_389_, lean_object* v_quoteDepth_390_, lean_object* v_c_391_, lean_object* v_s_392_){
_start:
{
lean_object* v_toInputContext_393_; lean_object* v_pos_394_; uint8_t v___x_395_; 
v_toInputContext_393_ = lean_ctor_get(v_c_391_, 0);
v_pos_394_ = lean_ctor_get(v_s_392_, 2);
v___x_395_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_393_, v_pos_394_);
if (v___x_395_ == 0)
{
lean_object* v_inputString_396_; uint8_t v___x_397_; uint32_t v_curr_398_; uint32_t v___x_399_; uint8_t v___x_400_; 
v_inputString_396_ = lean_ctor_get(v_toInputContext_393_, 0);
v___x_397_ = 1;
v_curr_398_ = lean_string_utf8_get_fast(v_inputString_396_, v_pos_394_);
v___x_399_ = 39;
v___x_400_ = lean_uint32_dec_eq(v_curr_398_, v___x_399_);
if (v___x_400_ == 0)
{
lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_401_ = lean_unsigned_to_nat(3u);
v___x_402_ = lean_nat_dec_le(v___x_401_, v_quoteDepth_390_);
lean_dec(v_quoteDepth_390_);
if (v___x_402_ == 0)
{
uint32_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = 10;
v___x_404_ = lean_uint32_dec_eq(v_curr_398_, v___x_403_);
if (v___x_404_ == 0)
{
uint32_t v___x_405_; uint8_t v___x_406_; 
v___x_405_ = 13;
v___x_406_ = lean_uint32_dec_eq(v_curr_398_, v___x_405_);
if (v___x_406_ == 0)
{
uint8_t v___x_407_; 
v___x_407_ = l_Lake_Toml_isControlChar(v_curr_398_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; 
lean_inc(v_pos_394_);
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_392_, v_c_391_, v_pos_394_);
lean_dec(v_pos_394_);
v_quoteDepth_390_ = v___x_408_;
v_s_392_ = v___x_409_;
goto _start;
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; 
lean_dec(v_startPos_389_);
v___x_411_ = lean_box(0);
v___x_412_ = l_Lake_Toml_mkUnexpectedCharError(v_s_392_, v_curr_398_, v___x_411_, v___x_397_);
return v___x_412_;
}
}
else
{
lean_object* v___x_413_; lean_object* v_s_414_; lean_object* v_errorMsg_415_; lean_object* v___x_416_; uint8_t v___x_417_; uint8_t v___x_418_; 
lean_inc(v_pos_394_);
v___x_413_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_392_, v_c_391_, v_pos_394_);
lean_dec(v_pos_394_);
v_s_414_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_391_, v___x_413_);
v_errorMsg_415_ = lean_ctor_get(v_s_414_, 4);
lean_inc(v_errorMsg_415_);
v___x_416_ = lean_box(0);
v___x_417_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_415_, v___x_416_);
v___x_418_ = lean_bool_not(v___x_417_);
if (v___x_418_ == 0)
{
lean_object* v___x_419_; 
v___x_419_ = lean_unsigned_to_nat(0u);
v_quoteDepth_390_ = v___x_419_;
v_s_392_ = v_s_414_;
goto _start;
}
else
{
lean_dec(v_startPos_389_);
return v_s_414_;
}
}
}
else
{
lean_object* v___x_421_; lean_object* v___x_422_; 
lean_inc(v_pos_394_);
v___x_421_ = lean_unsigned_to_nat(0u);
v___x_422_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_392_, v_c_391_, v_pos_394_);
lean_dec(v_pos_394_);
v_quoteDepth_390_ = v___x_421_;
v_s_392_ = v___x_422_;
goto _start;
}
}
else
{
lean_dec(v_startPos_389_);
return v_s_392_;
}
}
else
{
lean_object* v_s_424_; lean_object* v___x_425_; uint8_t v___x_426_; 
lean_inc(v_pos_394_);
v_s_424_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_392_, v_c_391_, v_pos_394_);
lean_dec(v_pos_394_);
v___x_425_ = lean_unsigned_to_nat(5u);
v___x_426_ = lean_nat_dec_le(v___x_425_, v_quoteDepth_390_);
if (v___x_426_ == 0)
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = lean_unsigned_to_nat(1u);
v___x_428_ = lean_nat_add(v_quoteDepth_390_, v___x_427_);
lean_dec(v_quoteDepth_390_);
v_quoteDepth_390_ = v___x_428_;
v_s_392_ = v_s_424_;
goto _start;
}
else
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
lean_dec(v_quoteDepth_390_);
lean_dec(v_startPos_389_);
v___x_430_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0));
v___x_431_ = lean_box(0);
v___x_432_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_424_, v___x_430_, v___x_431_, v___x_397_);
return v___x_432_;
}
}
}
else
{
lean_object* v___x_433_; uint8_t v___x_434_; 
v___x_433_ = lean_unsigned_to_nat(3u);
v___x_434_ = lean_nat_dec_le(v___x_433_, v_quoteDepth_390_);
lean_dec(v_quoteDepth_390_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__1));
v___x_436_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_392_, v___x_435_, v_startPos_389_);
return v___x_436_;
}
else
{
lean_dec(v_startPos_389_);
return v_s_392_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___boxed(lean_object* v_startPos_437_, lean_object* v_quoteDepth_438_, lean_object* v_c_439_, lean_object* v_s_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(v_startPos_437_, v_quoteDepth_438_, v_c_439_, v_s_440_);
lean_dec_ref(v_c_439_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0(lean_object* v_c_446_, lean_object* v_x_447_, lean_object* v_x_448_){
_start:
{
lean_object* v_zero_449_; uint8_t v_isZero_450_; 
v_zero_449_ = lean_unsigned_to_nat(0u);
v_isZero_450_ = lean_nat_dec_eq(v_x_447_, v_zero_449_);
if (v_isZero_450_ == 1)
{
lean_dec(v_x_447_);
return v_x_448_;
}
else
{
uint32_t v___x_451_; lean_object* v___x_452_; lean_object* v_s_453_; lean_object* v_errorMsg_454_; lean_object* v___x_455_; uint8_t v___x_456_; uint8_t v___x_457_; 
v___x_451_ = 39;
v___x_452_ = ((lean_object*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___closed__1));
v_s_453_ = l_Lake_Toml_chFn(v___x_451_, v___x_452_, v_c_446_, v_x_448_);
v_errorMsg_454_ = lean_ctor_get(v_s_453_, 4);
lean_inc(v_errorMsg_454_);
v___x_455_ = lean_box(0);
v___x_456_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_454_, v___x_455_);
v___x_457_ = lean_bool_not(v___x_456_);
if (v___x_457_ == 0)
{
lean_object* v_one_458_; lean_object* v_n_459_; 
v_one_458_ = lean_unsigned_to_nat(1u);
v_n_459_ = lean_nat_sub(v_x_447_, v_one_458_);
lean_dec(v_x_447_);
v_x_447_ = v_n_459_;
v_x_448_ = v_s_453_;
goto _start;
}
else
{
lean_dec(v_x_447_);
return v_s_453_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0___boxed(lean_object* v_c_461_, lean_object* v_x_462_, lean_object* v_x_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0(v_c_461_, v_x_462_, v_x_463_);
lean_dec_ref(v_c_461_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralStringFn___lam__0(lean_object* v___x_465_, lean_object* v___y_466_, lean_object* v___y_467_){
_start:
{
lean_object* v___x_468_; 
v___x_468_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlLiteralStringFn_spec__0(v___y_466_, v___x_465_, v___y_467_);
return v___x_468_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralStringFn___lam__0___boxed(lean_object* v___x_469_, lean_object* v___y_470_, lean_object* v___y_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l_Lake_Toml_mlLiteralStringFn___lam__0(v___x_469_, v___y_470_, v___y_471_);
lean_dec_ref(v___y_470_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralStringFn(lean_object* v_a_475_, lean_object* v_a_476_){
_start:
{
lean_object* v_pos_477_; lean_object* v___f_478_; lean_object* v_s_479_; lean_object* v_errorMsg_480_; lean_object* v___x_481_; uint8_t v___x_482_; uint8_t v___x_483_; 
v_pos_477_ = lean_ctor_get(v_a_476_, 2);
lean_inc(v_pos_477_);
v___f_478_ = ((lean_object*)(l_Lake_Toml_mlLiteralStringFn___closed__0));
lean_inc_ref(v_a_475_);
v_s_479_ = l_Lean_Parser_atomicFn(v___f_478_, v_a_475_, v_a_476_);
v_errorMsg_480_ = lean_ctor_get(v_s_479_, 4);
lean_inc(v_errorMsg_480_);
v___x_481_ = lean_box(0);
v___x_482_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_480_, v___x_481_);
v___x_483_ = lean_bool_not(v___x_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_unsigned_to_nat(0u);
v___x_485_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(v_pos_477_, v___x_484_, v_a_475_, v_s_479_);
lean_dec_ref(v_a_475_);
return v___x_485_;
}
else
{
lean_dec(v_pos_477_);
lean_dec_ref(v_a_475_);
return v_s_479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn(lean_object* v_startPos_487_, lean_object* v_quoteDepth_488_, lean_object* v_c_489_, lean_object* v_s_490_){
_start:
{
lean_object* v_toInputContext_491_; lean_object* v_pos_492_; uint8_t v___x_493_; 
v_toInputContext_491_ = lean_ctor_get(v_c_489_, 0);
v_pos_492_ = lean_ctor_get(v_s_490_, 2);
v___x_493_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_491_, v_pos_492_);
if (v___x_493_ == 0)
{
lean_object* v_inputString_494_; uint8_t v___x_495_; uint32_t v_curr_496_; uint32_t v___x_497_; uint8_t v___x_498_; 
v_inputString_494_ = lean_ctor_get(v_toInputContext_491_, 0);
v___x_495_ = 1;
v_curr_496_ = lean_string_utf8_get_fast(v_inputString_494_, v_pos_492_);
v___x_497_ = 34;
v___x_498_ = lean_uint32_dec_eq(v_curr_496_, v___x_497_);
if (v___x_498_ == 0)
{
lean_object* v___x_499_; uint8_t v___x_500_; 
v___x_499_ = lean_unsigned_to_nat(3u);
v___x_500_ = lean_nat_dec_le(v___x_499_, v_quoteDepth_488_);
lean_dec(v_quoteDepth_488_);
if (v___x_500_ == 0)
{
uint32_t v___x_501_; uint8_t v___x_502_; 
v___x_501_ = 10;
v___x_502_ = lean_uint32_dec_eq(v_curr_496_, v___x_501_);
if (v___x_502_ == 0)
{
uint32_t v___x_503_; uint8_t v___x_504_; 
v___x_503_ = 13;
v___x_504_ = lean_uint32_dec_eq(v_curr_496_, v___x_503_);
if (v___x_504_ == 0)
{
uint32_t v___x_505_; uint8_t v___x_506_; 
v___x_505_ = 92;
v___x_506_ = lean_uint32_dec_eq(v_curr_496_, v___x_505_);
if (v___x_506_ == 0)
{
uint8_t v___x_507_; 
v___x_507_ = l_Lake_Toml_isControlChar(v_curr_496_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; lean_object* v___x_509_; 
lean_inc(v_pos_492_);
v___x_508_ = lean_unsigned_to_nat(0u);
v___x_509_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_490_, v_c_489_, v_pos_492_);
lean_dec(v_pos_492_);
v_quoteDepth_488_ = v___x_508_;
v_s_490_ = v___x_509_;
goto _start;
}
else
{
lean_object* v___x_511_; lean_object* v___x_512_; 
lean_dec_ref(v_c_489_);
lean_dec(v_startPos_487_);
v___x_511_ = lean_box(0);
v___x_512_ = l_Lake_Toml_mkUnexpectedCharError(v_s_490_, v_curr_496_, v___x_511_, v___x_495_);
return v___x_512_;
}
}
else
{
lean_object* v___x_513_; lean_object* v_s_514_; lean_object* v_errorMsg_515_; lean_object* v___x_516_; uint8_t v___x_517_; uint8_t v___x_518_; 
lean_inc(v_pos_492_);
v___x_513_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_490_, v_c_489_, v_pos_492_);
lean_dec(v_pos_492_);
lean_inc_ref(v_c_489_);
v_s_514_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(v___x_495_, v_c_489_, v___x_513_);
v_errorMsg_515_ = lean_ctor_get(v_s_514_, 4);
lean_inc(v_errorMsg_515_);
v___x_516_ = lean_box(0);
v___x_517_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_515_, v___x_516_);
v___x_518_ = lean_bool_not(v___x_517_);
if (v___x_518_ == 0)
{
lean_object* v___x_519_; 
v___x_519_ = lean_unsigned_to_nat(0u);
v_quoteDepth_488_ = v___x_519_;
v_s_490_ = v_s_514_;
goto _start;
}
else
{
lean_dec_ref(v_c_489_);
lean_dec(v_startPos_487_);
return v_s_514_;
}
}
}
else
{
lean_object* v___x_521_; lean_object* v_s_522_; lean_object* v_errorMsg_523_; lean_object* v___x_524_; uint8_t v___x_525_; uint8_t v___x_526_; 
lean_inc(v_pos_492_);
v___x_521_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_490_, v_c_489_, v_pos_492_);
lean_dec(v_pos_492_);
v_s_522_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(v_c_489_, v___x_521_);
v_errorMsg_523_ = lean_ctor_get(v_s_522_, 4);
lean_inc(v_errorMsg_523_);
v___x_524_ = lean_box(0);
v___x_525_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_523_, v___x_524_);
v___x_526_ = lean_bool_not(v___x_525_);
if (v___x_526_ == 0)
{
lean_object* v___x_527_; 
v___x_527_ = lean_unsigned_to_nat(0u);
v_quoteDepth_488_ = v___x_527_;
v_s_490_ = v_s_522_;
goto _start;
}
else
{
lean_dec_ref(v_c_489_);
lean_dec(v_startPos_487_);
return v_s_522_;
}
}
}
else
{
lean_object* v___x_529_; lean_object* v___x_530_; 
lean_inc(v_pos_492_);
v___x_529_ = lean_unsigned_to_nat(0u);
v___x_530_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_490_, v_c_489_, v_pos_492_);
lean_dec(v_pos_492_);
v_quoteDepth_488_ = v___x_529_;
v_s_490_ = v___x_530_;
goto _start;
}
}
else
{
lean_dec_ref(v_c_489_);
lean_dec(v_startPos_487_);
return v_s_490_;
}
}
else
{
lean_object* v_s_532_; lean_object* v___x_533_; uint8_t v___x_534_; 
lean_inc(v_pos_492_);
v_s_532_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_490_, v_c_489_, v_pos_492_);
lean_dec(v_pos_492_);
v___x_533_ = lean_unsigned_to_nat(5u);
v___x_534_ = lean_nat_dec_le(v___x_533_, v_quoteDepth_488_);
if (v___x_534_ == 0)
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = lean_unsigned_to_nat(1u);
v___x_536_ = lean_nat_add(v_quoteDepth_488_, v___x_535_);
lean_dec(v_quoteDepth_488_);
v_quoteDepth_488_ = v___x_536_;
v_s_490_ = v_s_532_;
goto _start;
}
else
{
lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; 
lean_dec_ref(v_c_489_);
lean_dec(v_quoteDepth_488_);
lean_dec(v_startPos_487_);
v___x_538_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0));
v___x_539_ = lean_box(0);
v___x_540_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_532_, v___x_538_, v___x_539_, v___x_495_);
return v___x_540_;
}
}
}
else
{
lean_object* v___x_541_; uint8_t v___x_542_; 
lean_dec_ref(v_c_489_);
v___x_541_ = lean_unsigned_to_nat(3u);
v___x_542_ = lean_nat_dec_le(v___x_541_, v_quoteDepth_488_);
lean_dec(v_quoteDepth_488_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn___closed__0));
v___x_544_ = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(v_s_490_, v___x_543_, v_startPos_487_);
return v___x_544_;
}
else
{
lean_dec(v_startPos_487_);
return v_s_490_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0(lean_object* v_c_549_, lean_object* v_x_550_, lean_object* v_x_551_){
_start:
{
lean_object* v_zero_552_; uint8_t v_isZero_553_; 
v_zero_552_ = lean_unsigned_to_nat(0u);
v_isZero_553_ = lean_nat_dec_eq(v_x_550_, v_zero_552_);
if (v_isZero_553_ == 1)
{
lean_dec(v_x_550_);
return v_x_551_;
}
else
{
uint32_t v___x_554_; lean_object* v___x_555_; lean_object* v_s_556_; lean_object* v_errorMsg_557_; lean_object* v___x_558_; uint8_t v___x_559_; uint8_t v___x_560_; 
v___x_554_ = 34;
v___x_555_ = ((lean_object*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___closed__1));
v_s_556_ = l_Lake_Toml_chFn(v___x_554_, v___x_555_, v_c_549_, v_x_551_);
v_errorMsg_557_ = lean_ctor_get(v_s_556_, 4);
lean_inc(v_errorMsg_557_);
v___x_558_ = lean_box(0);
v___x_559_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_557_, v___x_558_);
v___x_560_ = lean_bool_not(v___x_559_);
if (v___x_560_ == 0)
{
lean_object* v_one_561_; lean_object* v_n_562_; 
v_one_561_ = lean_unsigned_to_nat(1u);
v_n_562_ = lean_nat_sub(v_x_550_, v_one_561_);
lean_dec(v_x_550_);
v_x_550_ = v_n_562_;
v_x_551_ = v_s_556_;
goto _start;
}
else
{
lean_dec(v_x_550_);
return v_s_556_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0___boxed(lean_object* v_c_564_, lean_object* v_x_565_, lean_object* v_x_566_){
_start:
{
lean_object* v_res_567_; 
v_res_567_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0(v_c_564_, v_x_565_, v_x_566_);
lean_dec_ref(v_c_564_);
return v_res_567_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicStringFn___lam__0(lean_object* v___x_568_, lean_object* v___y_569_, lean_object* v___y_570_){
_start:
{
lean_object* v___x_571_; 
v___x_571_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_mlBasicStringFn_spec__0(v___y_569_, v___x_568_, v___y_570_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicStringFn___lam__0___boxed(lean_object* v___x_572_, lean_object* v___y_573_, lean_object* v___y_574_){
_start:
{
lean_object* v_res_575_; 
v_res_575_ = l_Lake_Toml_mlBasicStringFn___lam__0(v___x_572_, v___y_573_, v___y_574_);
lean_dec_ref(v___y_573_);
return v_res_575_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicStringFn(lean_object* v_a_578_, lean_object* v_a_579_){
_start:
{
lean_object* v_pos_580_; lean_object* v___f_581_; lean_object* v_s_582_; lean_object* v_errorMsg_583_; lean_object* v___x_584_; uint8_t v___x_585_; uint8_t v___x_586_; 
v_pos_580_ = lean_ctor_get(v_a_579_, 2);
lean_inc(v_pos_580_);
v___f_581_ = ((lean_object*)(l_Lake_Toml_mlBasicStringFn___closed__0));
lean_inc_ref(v_a_578_);
v_s_582_ = l_Lean_Parser_atomicFn(v___f_581_, v_a_578_, v_a_579_);
v_errorMsg_583_ = lean_ctor_get(v_s_582_, 4);
lean_inc(v_errorMsg_583_);
v___x_584_ = lean_box(0);
v___x_585_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_583_, v___x_584_);
v___x_586_ = lean_bool_not(v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_588_; 
v___x_587_ = lean_unsigned_to_nat(0u);
v___x_588_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn(v_pos_580_, v___x_587_, v_a_578_, v_s_582_);
return v___x_588_;
}
else
{
lean_dec(v_pos_580_);
lean_dec_ref(v_a_578_);
return v_s_582_;
}
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4(void){
_start:
{
uint32_t v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; 
v___x_595_ = 58;
v___x_596_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_597_ = lean_string_push(v___x_596_, v___x_595_);
return v___x_597_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5(void){
_start:
{
lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_598_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4, &l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4);
v___x_599_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_600_ = lean_string_append(v___x_599_, v___x_598_);
return v___x_600_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6(void){
_start:
{
lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; 
v___x_601_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_602_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5);
v___x_603_ = lean_string_append(v___x_602_, v___x_601_);
return v___x_603_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7(void){
_start:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; 
v___x_604_ = lean_box(0);
v___x_605_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6, &l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6);
v___x_606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_606_, 0, v___x_605_);
lean_ctor_set(v___x_606_, 1, v___x_604_);
return v___x_606_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(lean_object* v_a_611_, lean_object* v_a_612_){
_start:
{
lean_object* v___x_613_; lean_object* v_s_614_; lean_object* v_errorMsg_615_; lean_object* v___x_616_; uint8_t v___x_617_; uint8_t v___x_618_; 
v___x_613_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__1));
v_s_614_ = l_Lake_Toml_digitPairFn(v___x_613_, v_a_611_, v_a_612_);
v_errorMsg_615_ = lean_ctor_get(v_s_614_, 4);
lean_inc(v_errorMsg_615_);
v___x_616_ = lean_box(0);
v___x_617_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_615_, v___x_616_);
v___x_618_ = lean_bool_not(v___x_617_);
if (v___x_618_ == 0)
{
uint32_t v___x_619_; lean_object* v___x_620_; lean_object* v_s_621_; lean_object* v_errorMsg_622_; uint8_t v___x_623_; uint8_t v___x_624_; 
v___x_619_ = 58;
v___x_620_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7, &l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7);
v_s_621_ = l_Lake_Toml_chFn(v___x_619_, v___x_620_, v_a_611_, v_s_614_);
v_errorMsg_622_ = lean_ctor_get(v_s_621_, 4);
lean_inc(v_errorMsg_622_);
v___x_623_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_622_, v___x_616_);
v___x_624_ = lean_bool_not(v___x_623_);
if (v___x_624_ == 0)
{
lean_object* v___x_625_; lean_object* v___x_626_; 
v___x_625_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9));
v___x_626_ = l_Lake_Toml_digitPairFn(v___x_625_, v_a_611_, v_s_621_);
return v___x_626_;
}
else
{
return v_s_621_;
}
}
else
{
return v_s_614_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___boxed(lean_object* v_a_627_, lean_object* v_a_628_){
_start:
{
lean_object* v_res_629_; 
v_res_629_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(v_a_627_, v_a_628_);
lean_dec_ref(v_a_627_);
return v_res_629_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn(uint8_t v_allowOffset_631_, uint32_t v_curr_632_, lean_object* v_nextPos_633_, lean_object* v_c_634_, lean_object* v_s_635_){
_start:
{
uint8_t v___y_637_; uint8_t v___y_638_; uint8_t v___y_645_; uint32_t v___x_655_; uint8_t v___x_656_; 
v___x_655_ = 90;
v___x_656_ = lean_uint32_dec_eq(v_curr_632_, v___x_655_);
if (v___x_656_ == 0)
{
uint32_t v___x_657_; uint8_t v___x_658_; 
v___x_657_ = 122;
v___x_658_ = lean_uint32_dec_eq(v_curr_632_, v___x_657_);
v___y_645_ = v___x_658_;
goto v___jp_644_;
}
else
{
v___y_645_ = v___x_656_;
goto v___jp_644_;
}
v___jp_636_:
{
if (v___y_638_ == 0)
{
lean_dec(v_nextPos_633_);
return v_s_635_;
}
else
{
if (v_allowOffset_631_ == 0)
{
lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
lean_dec(v_nextPos_633_);
v___x_639_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_640_ = lean_box(0);
v___x_641_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_635_, v___x_639_, v___x_640_, v___y_637_);
return v___x_641_;
}
else
{
lean_object* v___x_642_; lean_object* v___x_643_; 
v___x_642_ = l_Lean_Parser_ParserState_setPos(v_s_635_, v_nextPos_633_);
v___x_643_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(v_c_634_, v___x_642_);
return v___x_643_;
}
}
}
v___jp_644_:
{
uint8_t v___x_646_; 
v___x_646_ = 1;
if (v___y_645_ == 0)
{
uint32_t v___x_647_; uint8_t v___x_648_; 
v___x_647_ = 43;
v___x_648_ = lean_uint32_dec_eq(v_curr_632_, v___x_647_);
if (v___x_648_ == 0)
{
uint32_t v___x_649_; uint8_t v___x_650_; 
v___x_649_ = 45;
v___x_650_ = lean_uint32_dec_eq(v_curr_632_, v___x_649_);
v___y_637_ = v___x_646_;
v___y_638_ = v___x_650_;
goto v___jp_636_;
}
else
{
v___y_637_ = v___x_646_;
v___y_638_ = v___x_648_;
goto v___jp_636_;
}
}
else
{
if (v_allowOffset_631_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
lean_dec(v_nextPos_633_);
v___x_651_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_652_ = lean_box(0);
v___x_653_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_635_, v___x_651_, v___x_652_, v___x_646_);
return v___x_653_;
}
else
{
lean_object* v___x_654_; 
v___x_654_ = l_Lean_Parser_ParserState_setPos(v_s_635_, v_nextPos_633_);
return v___x_654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___boxed(lean_object* v_allowOffset_659_, lean_object* v_curr_660_, lean_object* v_nextPos_661_, lean_object* v_c_662_, lean_object* v_s_663_){
_start:
{
uint8_t v_allowOffset_boxed_664_; uint32_t v_curr_boxed_665_; lean_object* v_res_666_; 
v_allowOffset_boxed_664_ = lean_unbox(v_allowOffset_659_);
v_curr_boxed_665_ = lean_unbox_uint32(v_curr_660_);
lean_dec(v_curr_660_);
v_res_666_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn(v_allowOffset_boxed_664_, v_curr_boxed_665_, v_nextPos_661_, v_c_662_, v_s_663_);
lean_dec_ref(v_c_662_);
return v_res_666_;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0(uint32_t v_x_667_){
_start:
{
uint32_t v___x_668_; uint8_t v___x_669_; 
v___x_668_ = 48;
v___x_669_ = lean_uint32_dec_le(v___x_668_, v_x_667_);
if (v___x_669_ == 0)
{
return v___x_669_;
}
else
{
uint32_t v___x_670_; uint8_t v___x_671_; 
v___x_670_ = 57;
v___x_671_ = lean_uint32_dec_le(v_x_667_, v___x_670_);
return v___x_671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0___boxed(lean_object* v_x_672_){
_start:
{
uint32_t v_x_470__boxed_673_; uint8_t v_res_674_; lean_object* v_r_675_; 
v_x_470__boxed_673_ = lean_unbox_uint32(v_x_672_);
lean_dec(v_x_672_);
v_res_674_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0(v_x_470__boxed_673_);
v_r_675_ = lean_box(v_res_674_);
return v_r_675_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(uint8_t v_allowOffset_681_, lean_object* v_c_682_, lean_object* v_s_683_){
_start:
{
lean_object* v_toInputContext_684_; lean_object* v_pos_685_; uint8_t v___x_686_; 
v_toInputContext_684_ = lean_ctor_get(v_c_682_, 0);
v_pos_685_ = lean_ctor_get(v_s_683_, 2);
v___x_686_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_684_, v_pos_685_);
if (v___x_686_ == 0)
{
lean_object* v_inputString_687_; uint32_t v_curr_688_; uint32_t v___x_689_; uint8_t v___x_690_; 
v_inputString_687_ = lean_ctor_get(v_toInputContext_684_, 0);
v_curr_688_ = lean_string_utf8_get_fast(v_inputString_687_, v_pos_685_);
v___x_689_ = 46;
v___x_690_ = lean_uint32_dec_eq(v_curr_688_, v___x_689_);
if (v___x_690_ == 0)
{
lean_object* v___x_691_; uint8_t v___y_693_; uint8_t v___y_694_; uint8_t v___y_701_; uint32_t v___x_711_; uint8_t v___x_712_; 
v___x_691_ = lean_string_utf8_next_fast(v_inputString_687_, v_pos_685_);
v___x_711_ = 90;
v___x_712_ = lean_uint32_dec_eq(v_curr_688_, v___x_711_);
if (v___x_712_ == 0)
{
uint32_t v___x_713_; uint8_t v___x_714_; 
v___x_713_ = 122;
v___x_714_ = lean_uint32_dec_eq(v_curr_688_, v___x_713_);
v___y_701_ = v___x_714_;
goto v___jp_700_;
}
else
{
v___y_701_ = v___x_712_;
goto v___jp_700_;
}
v___jp_692_:
{
if (v___y_694_ == 0)
{
return v_s_683_;
}
else
{
if (v_allowOffset_681_ == 0)
{
lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_695_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_696_ = lean_box(0);
v___x_697_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_683_, v___x_695_, v___x_696_, v___y_693_);
return v___x_697_;
}
else
{
lean_object* v___x_698_; lean_object* v___x_699_; 
v___x_698_ = l_Lean_Parser_ParserState_setPos(v_s_683_, v___x_691_);
v___x_699_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(v_c_682_, v___x_698_);
return v___x_699_;
}
}
}
v___jp_700_:
{
uint8_t v___x_702_; 
v___x_702_ = 1;
if (v___y_701_ == 0)
{
uint32_t v___x_703_; uint8_t v___x_704_; 
v___x_703_ = 43;
v___x_704_ = lean_uint32_dec_eq(v_curr_688_, v___x_703_);
if (v___x_704_ == 0)
{
uint32_t v___x_705_; uint8_t v___x_706_; 
v___x_705_ = 45;
v___x_706_ = lean_uint32_dec_eq(v_curr_688_, v___x_705_);
v___y_693_ = v___x_702_;
v___y_694_ = v___x_706_;
goto v___jp_692_;
}
else
{
v___y_693_ = v___x_702_;
v___y_694_ = v___x_704_;
goto v___jp_692_;
}
}
else
{
if (v_allowOffset_681_ == 0)
{
lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; 
v___x_707_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_708_ = lean_box(0);
v___x_709_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_683_, v___x_707_, v___x_708_, v___x_702_);
return v___x_709_;
}
else
{
lean_object* v___x_710_; 
v___x_710_ = l_Lean_Parser_ParserState_setPos(v_s_683_, v___x_691_);
return v___x_710_;
}
}
}
}
else
{
lean_object* v___f_715_; lean_object* v_s_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v_s_719_; lean_object* v_pos_720_; lean_object* v_errorMsg_721_; lean_object* v___x_722_; uint8_t v___x_723_; uint8_t v___x_724_; 
lean_inc(v_pos_685_);
v___f_715_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0));
v_s_716_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_683_, v_c_682_, v_pos_685_);
lean_dec(v_pos_685_);
v___x_717_ = lean_box(0);
v___x_718_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__2));
v_s_719_ = l_Lake_Toml_takeWhile1Fn(v___f_715_, v___x_718_, v_c_682_, v_s_716_);
v_pos_720_ = lean_ctor_get(v_s_719_, 2);
lean_inc(v_pos_720_);
v_errorMsg_721_ = lean_ctor_get(v_s_719_, 4);
lean_inc(v_errorMsg_721_);
v___x_722_ = lean_box(0);
v___x_723_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_721_, v___x_722_);
v___x_724_ = lean_bool_not(v___x_723_);
if (v___x_724_ == 0)
{
uint8_t v___x_725_; 
v___x_725_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_684_, v_pos_720_);
if (v___x_725_ == 0)
{
uint32_t v___x_726_; lean_object* v___x_727_; uint8_t v___y_729_; uint8_t v___y_735_; uint32_t v___x_743_; uint8_t v___x_744_; 
v___x_726_ = lean_string_utf8_get_fast(v_inputString_687_, v_pos_720_);
v___x_727_ = lean_string_utf8_next_fast(v_inputString_687_, v_pos_720_);
lean_dec(v_pos_720_);
v___x_743_ = 90;
v___x_744_ = lean_uint32_dec_eq(v___x_726_, v___x_743_);
if (v___x_744_ == 0)
{
uint32_t v___x_745_; uint8_t v___x_746_; 
v___x_745_ = 122;
v___x_746_ = lean_uint32_dec_eq(v___x_726_, v___x_745_);
v___y_735_ = v___x_746_;
goto v___jp_734_;
}
else
{
v___y_735_ = v___x_744_;
goto v___jp_734_;
}
v___jp_728_:
{
if (v___y_729_ == 0)
{
return v_s_719_;
}
else
{
if (v_allowOffset_681_ == 0)
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_731_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_719_, v___x_730_, v___x_717_, v___x_690_);
return v___x_731_;
}
else
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = l_Lean_Parser_ParserState_setPos(v_s_719_, v___x_727_);
v___x_733_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(v_c_682_, v___x_732_);
return v___x_733_;
}
}
}
v___jp_734_:
{
if (v___y_735_ == 0)
{
uint32_t v___x_736_; uint8_t v___x_737_; 
v___x_736_ = 43;
v___x_737_ = lean_uint32_dec_eq(v___x_726_, v___x_736_);
if (v___x_737_ == 0)
{
uint32_t v___x_738_; uint8_t v___x_739_; 
v___x_738_ = 45;
v___x_739_ = lean_uint32_dec_eq(v___x_726_, v___x_738_);
v___y_729_ = v___x_739_;
goto v___jp_728_;
}
else
{
v___y_729_ = v___x_737_;
goto v___jp_728_;
}
}
else
{
if (v_allowOffset_681_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0));
v___x_741_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_719_, v___x_740_, v___x_717_, v___x_690_);
return v___x_741_;
}
else
{
lean_object* v___x_742_; 
v___x_742_ = l_Lean_Parser_ParserState_setPos(v_s_719_, v___x_727_);
return v___x_742_;
}
}
}
}
else
{
lean_dec(v_pos_720_);
return v_s_719_;
}
}
else
{
lean_dec(v_pos_720_);
return v_s_719_;
}
}
}
else
{
return v_s_683_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___boxed(lean_object* v_allowOffset_747_, lean_object* v_c_748_, lean_object* v_s_749_){
_start:
{
uint8_t v_allowOffset_boxed_750_; lean_object* v_res_751_; 
v_allowOffset_boxed_750_ = lean_unbox(v_allowOffset_747_);
v_res_751_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(v_allowOffset_boxed_750_, v_c_748_, v_s_749_);
lean_dec_ref(v_c_748_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(uint8_t v_allowOffset_756_, lean_object* v_a_757_, lean_object* v_a_758_){
_start:
{
lean_object* v___x_759_; lean_object* v_s_760_; lean_object* v_errorMsg_761_; lean_object* v___x_762_; uint8_t v___x_763_; uint8_t v___x_764_; 
v___x_759_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9));
v_s_760_ = l_Lake_Toml_digitPairFn(v___x_759_, v_a_757_, v_a_758_);
v_errorMsg_761_ = lean_ctor_get(v_s_760_, 4);
lean_inc(v_errorMsg_761_);
v___x_762_ = lean_box(0);
v___x_763_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_761_, v___x_762_);
v___x_764_ = lean_bool_not(v___x_763_);
if (v___x_764_ == 0)
{
uint32_t v___x_765_; lean_object* v___x_766_; lean_object* v_s_767_; lean_object* v_errorMsg_768_; uint8_t v___x_769_; uint8_t v___x_770_; 
v___x_765_ = 58;
v___x_766_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7, &l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7);
v_s_767_ = l_Lake_Toml_chFn(v___x_765_, v___x_766_, v_a_757_, v_s_760_);
v_errorMsg_768_ = lean_ctor_get(v_s_767_, 4);
lean_inc(v_errorMsg_768_);
v___x_769_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_768_, v___x_762_);
v___x_770_ = lean_bool_not(v___x_769_);
if (v___x_770_ == 0)
{
lean_object* v___x_771_; lean_object* v_s_772_; lean_object* v_errorMsg_773_; uint8_t v___x_774_; uint8_t v___x_775_; 
v___x_771_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__1));
v_s_772_ = l_Lake_Toml_digitPairFn(v___x_771_, v_a_757_, v_s_767_);
v_errorMsg_773_ = lean_ctor_get(v_s_772_, 4);
lean_inc(v_errorMsg_773_);
v___x_774_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_773_, v___x_762_);
v___x_775_ = lean_bool_not(v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
v___x_776_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(v_allowOffset_756_, v_a_757_, v_s_772_);
return v___x_776_;
}
else
{
return v_s_772_;
}
}
else
{
return v_s_767_;
}
}
else
{
return v_s_760_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___boxed(lean_object* v_allowOffset_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
uint8_t v_allowOffset_boxed_780_; lean_object* v_res_781_; 
v_allowOffset_boxed_780_ = lean_unbox(v_allowOffset_777_);
v_res_781_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(v_allowOffset_boxed_780_, v_a_778_, v_a_779_);
lean_dec_ref(v_a_778_);
return v_res_781_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_timeFn(uint8_t v_allowOffset_786_, lean_object* v_a_787_, lean_object* v_a_788_){
_start:
{
lean_object* v___x_789_; lean_object* v_s_790_; lean_object* v_errorMsg_791_; lean_object* v___x_792_; uint8_t v___x_793_; uint8_t v___x_794_; 
v___x_789_ = ((lean_object*)(l_Lake_Toml_timeFn___closed__1));
v_s_790_ = l_Lake_Toml_digitPairFn(v___x_789_, v_a_787_, v_a_788_);
v_errorMsg_791_ = lean_ctor_get(v_s_790_, 4);
lean_inc(v_errorMsg_791_);
v___x_792_ = lean_box(0);
v___x_793_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_791_, v___x_792_);
v___x_794_ = lean_bool_not(v___x_793_);
if (v___x_794_ == 0)
{
uint32_t v___x_795_; lean_object* v___x_796_; lean_object* v_s_797_; lean_object* v_errorMsg_798_; uint8_t v___x_799_; uint8_t v___x_800_; 
v___x_795_ = 58;
v___x_796_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7, &l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7);
v_s_797_ = l_Lake_Toml_chFn(v___x_795_, v___x_796_, v_a_787_, v_s_790_);
v_errorMsg_798_ = lean_ctor_get(v_s_797_, 4);
lean_inc(v_errorMsg_798_);
v___x_799_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_798_, v___x_792_);
v___x_800_ = lean_bool_not(v___x_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; 
v___x_801_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(v_allowOffset_786_, v_a_787_, v_s_797_);
return v___x_801_;
}
else
{
return v_s_797_;
}
}
else
{
return v_s_790_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_timeFn___boxed(lean_object* v_allowOffset_802_, lean_object* v_a_803_, lean_object* v_a_804_){
_start:
{
uint8_t v_allowOffset_boxed_805_; lean_object* v_res_806_; 
v_allowOffset_boxed_805_ = lean_unbox(v_allowOffset_802_);
v_res_806_ = l_Lake_Toml_timeFn(v_allowOffset_boxed_805_, v_a_803_, v_a_804_);
lean_dec_ref(v_a_803_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(lean_object* v_c_807_, lean_object* v_s_808_){
_start:
{
lean_object* v_pos_809_; lean_object* v_toInputContext_810_; uint8_t v___x_811_; 
v_pos_809_ = lean_ctor_get(v_s_808_, 2);
v_toInputContext_810_ = lean_ctor_get(v_c_807_, 0);
v___x_811_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_810_, v_pos_809_);
if (v___x_811_ == 0)
{
lean_object* v_inputString_812_; uint8_t v___x_813_; uint32_t v_curr_817_; uint32_t v___x_818_; uint8_t v___x_819_; 
v_inputString_812_ = lean_ctor_get(v_toInputContext_810_, 0);
v___x_813_ = 1;
v_curr_817_ = lean_string_utf8_get_fast(v_inputString_812_, v_pos_809_);
v___x_818_ = 84;
v___x_819_ = lean_uint32_dec_eq(v_curr_817_, v___x_818_);
if (v___x_819_ == 0)
{
uint32_t v___x_820_; uint8_t v___x_821_; 
v___x_820_ = 116;
v___x_821_ = lean_uint32_dec_eq(v_curr_817_, v___x_820_);
if (v___x_821_ == 0)
{
uint32_t v___x_822_; uint8_t v___x_823_; 
v___x_822_ = 32;
v___x_823_ = lean_uint32_dec_eq(v_curr_817_, v___x_822_);
if (v___x_823_ == 0)
{
return v_s_808_;
}
else
{
lean_object* v_tPos_824_; lean_object* v___x_825_; lean_object* v_s_826_; uint8_t v___y_828_; lean_object* v_pos_833_; lean_object* v_errorMsg_834_; lean_object* v___x_835_; uint8_t v___x_836_; uint8_t v___x_837_; 
lean_inc(v_pos_809_);
v_tPos_824_ = lean_string_utf8_next_fast(v_inputString_812_, v_pos_809_);
v___x_825_ = l_Lean_Parser_ParserState_setPos(v_s_808_, v_tPos_824_);
v_s_826_ = l_Lake_Toml_timeFn(v___x_813_, v_c_807_, v___x_825_);
v_pos_833_ = lean_ctor_get(v_s_826_, 2);
lean_inc(v_pos_833_);
v_errorMsg_834_ = lean_ctor_get(v_s_826_, 4);
lean_inc(v_errorMsg_834_);
v___x_835_ = lean_box(0);
v___x_836_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_834_, v___x_835_);
v___x_837_ = lean_bool_not(v___x_836_);
if (v___x_837_ == 0)
{
lean_dec(v_pos_833_);
v___y_828_ = v___x_837_;
goto v___jp_827_;
}
else
{
uint8_t v___x_838_; 
v___x_838_ = lean_nat_dec_eq(v_pos_833_, v_tPos_824_);
lean_dec(v_pos_833_);
v___y_828_ = v___x_838_;
goto v___jp_827_;
}
v___jp_827_:
{
if (v___y_828_ == 0)
{
lean_dec(v_pos_809_);
return v_s_826_;
}
else
{
lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_829_ = l_Lean_Parser_ParserState_stackSize(v_s_826_);
v___x_830_ = lean_unsigned_to_nat(1u);
v___x_831_ = lean_nat_sub(v___x_829_, v___x_830_);
lean_dec(v___x_829_);
v___x_832_ = l_Lean_Parser_ParserState_restore(v_s_826_, v___x_831_, v_pos_809_);
lean_dec(v___x_831_);
return v___x_832_;
}
}
}
}
else
{
lean_inc(v_pos_809_);
goto v___jp_814_;
}
}
else
{
lean_inc(v_pos_809_);
goto v___jp_814_;
}
v___jp_814_:
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_808_, v_c_807_, v_pos_809_);
lean_dec(v_pos_809_);
v___x_816_ = l_Lake_Toml_timeFn(v___x_813_, v_c_807_, v___x_815_);
return v___x_816_;
}
}
else
{
return v_s_808_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn___boxed(lean_object* v_c_839_, lean_object* v_s_840_){
_start:
{
lean_object* v_res_841_; 
v_res_841_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(v_c_839_, v_s_840_);
lean_dec_ref(v_c_839_);
return v_res_841_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2(void){
_start:
{
uint32_t v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_846_ = 45;
v___x_847_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_848_ = lean_string_push(v___x_847_, v___x_846_);
return v___x_848_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3(void){
_start:
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; 
v___x_849_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2, &l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2);
v___x_850_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_851_ = lean_string_append(v___x_850_, v___x_849_);
return v___x_851_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4(void){
_start:
{
lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; 
v___x_852_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_853_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3, &l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3);
v___x_854_ = lean_string_append(v___x_853_, v___x_852_);
return v___x_854_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5(void){
_start:
{
lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; 
v___x_855_ = lean_box(0);
v___x_856_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4, &l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4);
v___x_857_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_857_, 0, v___x_856_);
lean_ctor_set(v___x_857_, 1, v___x_855_);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(lean_object* v_a_862_, lean_object* v_a_863_){
_start:
{
lean_object* v___x_864_; lean_object* v_s_865_; lean_object* v_errorMsg_866_; lean_object* v___x_867_; uint8_t v___x_868_; uint8_t v___x_869_; 
v___x_864_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__1));
v_s_865_ = l_Lake_Toml_digitPairFn(v___x_864_, v_a_862_, v_a_863_);
v_errorMsg_866_ = lean_ctor_get(v_s_865_, 4);
lean_inc(v_errorMsg_866_);
v___x_867_ = lean_box(0);
v___x_868_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_866_, v___x_867_);
v___x_869_ = lean_bool_not(v___x_868_);
if (v___x_869_ == 0)
{
uint32_t v___x_870_; lean_object* v___x_871_; lean_object* v_s_872_; lean_object* v_errorMsg_873_; uint8_t v___x_874_; uint8_t v___x_875_; 
v___x_870_ = 45;
v___x_871_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5);
v_s_872_ = l_Lake_Toml_chFn(v___x_870_, v___x_871_, v_a_862_, v_s_865_);
v_errorMsg_873_ = lean_ctor_get(v_s_872_, 4);
lean_inc(v_errorMsg_873_);
v___x_874_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_873_, v___x_867_);
v___x_875_ = lean_bool_not(v___x_874_);
if (v___x_875_ == 0)
{
lean_object* v___x_876_; lean_object* v_s_877_; lean_object* v_errorMsg_878_; uint8_t v___x_879_; uint8_t v___x_880_; 
v___x_876_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__7));
v_s_877_ = l_Lake_Toml_digitPairFn(v___x_876_, v_a_862_, v_s_872_);
v_errorMsg_878_ = lean_ctor_get(v_s_877_, 4);
lean_inc(v_errorMsg_878_);
v___x_879_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_878_, v___x_867_);
v___x_880_ = lean_bool_not(v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; 
v___x_881_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(v_a_862_, v_s_877_);
return v___x_881_;
}
else
{
return v_s_877_;
}
}
else
{
return v_s_872_;
}
}
else
{
return v_s_865_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___boxed(lean_object* v_a_882_, lean_object* v_a_883_){
_start:
{
lean_object* v_res_884_; 
v_res_884_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(v_a_882_, v_a_883_);
lean_dec_ref(v_a_882_);
return v_res_884_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0(lean_object* v_c_889_, lean_object* v_x_890_, lean_object* v_x_891_){
_start:
{
lean_object* v_zero_892_; uint8_t v_isZero_893_; 
v_zero_892_ = lean_unsigned_to_nat(0u);
v_isZero_893_ = lean_nat_dec_eq(v_x_890_, v_zero_892_);
if (v_isZero_893_ == 1)
{
lean_dec(v_x_890_);
return v_x_891_;
}
else
{
lean_object* v___x_894_; lean_object* v_s_895_; lean_object* v_errorMsg_896_; lean_object* v___x_897_; uint8_t v___x_898_; uint8_t v___x_899_; 
v___x_894_ = ((lean_object*)(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___closed__1));
v_s_895_ = l_Lake_Toml_digitFn(v___x_894_, v_c_889_, v_x_891_);
v_errorMsg_896_ = lean_ctor_get(v_s_895_, 4);
lean_inc(v_errorMsg_896_);
v___x_897_ = lean_box(0);
v___x_898_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_896_, v___x_897_);
v___x_899_ = lean_bool_not(v___x_898_);
if (v___x_899_ == 0)
{
lean_object* v_one_900_; lean_object* v_n_901_; 
v_one_900_ = lean_unsigned_to_nat(1u);
v_n_901_ = lean_nat_sub(v_x_890_, v_one_900_);
lean_dec(v_x_890_);
v_x_890_ = v_n_901_;
v_x_891_ = v_s_895_;
goto _start;
}
else
{
lean_dec(v_x_890_);
return v_s_895_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0___boxed(lean_object* v_c_903_, lean_object* v_x_904_, lean_object* v_x_905_){
_start:
{
lean_object* v_res_906_; 
v_res_906_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0(v_c_903_, v_x_904_, v_x_905_);
lean_dec_ref(v_c_903_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dateTimeFn(lean_object* v_a_907_, lean_object* v_a_908_){
_start:
{
lean_object* v___x_909_; lean_object* v_s_910_; lean_object* v_errorMsg_911_; lean_object* v___x_912_; uint8_t v___x_913_; uint8_t v___x_914_; 
v___x_909_ = lean_unsigned_to_nat(4u);
v_s_910_ = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___00Lake_Toml_dateTimeFn_spec__0(v_a_907_, v___x_909_, v_a_908_);
v_errorMsg_911_ = lean_ctor_get(v_s_910_, 4);
lean_inc(v_errorMsg_911_);
v___x_912_ = lean_box(0);
v___x_913_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_911_, v___x_912_);
v___x_914_ = lean_bool_not(v___x_913_);
if (v___x_914_ == 0)
{
uint32_t v___x_915_; lean_object* v___x_916_; lean_object* v_s_917_; lean_object* v_errorMsg_918_; uint8_t v___x_919_; uint8_t v___x_920_; 
v___x_915_ = 45;
v___x_916_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5);
v_s_917_ = l_Lake_Toml_chFn(v___x_915_, v___x_916_, v_a_907_, v_s_910_);
v_errorMsg_918_ = lean_ctor_get(v_s_917_, 4);
lean_inc(v_errorMsg_918_);
v___x_919_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_918_, v___x_912_);
v___x_920_ = lean_bool_not(v___x_919_);
if (v___x_920_ == 0)
{
lean_object* v___x_921_; 
v___x_921_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(v_a_907_, v_s_917_);
return v___x_921_;
}
else
{
return v_s_917_;
}
}
else
{
return v_s_910_;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dateTimeFn___boxed(lean_object* v_a_922_, lean_object* v_a_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l_Lake_Toml_dateTimeFn(v_a_922_, v_a_923_);
lean_dec_ref(v_a_922_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(lean_object* v_c_929_, lean_object* v_s_930_){
_start:
{
lean_object* v_toInputContext_931_; lean_object* v_pos_932_; lean_object* v_expected_933_; uint8_t v___x_934_; 
v_toInputContext_931_ = lean_ctor_get(v_c_929_, 0);
v_pos_932_ = lean_ctor_get(v_s_930_, 2);
v_expected_933_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__1));
v___x_934_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_931_, v_pos_932_);
if (v___x_934_ == 0)
{
lean_object* v_inputString_935_; lean_object* v___f_936_; uint32_t v_curr_941_; uint32_t v___x_942_; uint8_t v___x_943_; 
v_inputString_935_ = lean_ctor_get(v_toInputContext_931_, 0);
v___f_936_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0));
v_curr_941_ = lean_string_utf8_get_fast(v_inputString_935_, v_pos_932_);
v___x_942_ = 45;
v___x_943_ = lean_uint32_dec_eq(v_curr_941_, v___x_942_);
if (v___x_943_ == 0)
{
uint32_t v___x_944_; uint8_t v___x_945_; 
v___x_944_ = 43;
v___x_945_ = lean_uint32_dec_eq(v_curr_941_, v___x_944_);
if (v___x_945_ == 0)
{
uint8_t v___x_946_; uint8_t v___y_948_; uint32_t v___x_953_; uint8_t v___x_954_; 
v___x_946_ = 1;
v___x_953_ = 48;
v___x_954_ = lean_uint32_dec_le(v___x_953_, v_curr_941_);
if (v___x_954_ == 0)
{
v___y_948_ = v___x_954_;
goto v___jp_947_;
}
else
{
uint32_t v___x_955_; uint8_t v___x_956_; 
v___x_955_ = 57;
v___x_956_ = lean_uint32_dec_le(v_curr_941_, v___x_955_);
v___y_948_ = v___x_956_;
goto v___jp_947_;
}
v___jp_947_:
{
if (v___y_948_ == 0)
{
lean_object* v___x_949_; 
v___x_949_ = l_Lake_Toml_mkUnexpectedCharError(v_s_930_, v_curr_941_, v_expected_933_, v___x_946_);
return v___x_949_;
}
else
{
lean_object* v_s_950_; uint32_t v___x_951_; lean_object* v___x_952_; 
lean_inc(v_pos_932_);
v_s_950_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_930_, v_c_929_, v_pos_932_);
lean_dec(v_pos_932_);
v___x_951_ = 95;
v___x_952_ = l_Lake_Toml_sepByChar1AuxFn(v___f_936_, v___x_951_, v_expected_933_, v_c_929_, v_s_950_);
return v___x_952_;
}
}
}
else
{
lean_inc(v_pos_932_);
goto v___jp_937_;
}
}
else
{
lean_inc(v_pos_932_);
goto v___jp_937_;
}
v___jp_937_:
{
lean_object* v_s_938_; uint32_t v___x_939_; lean_object* v___x_940_; 
v_s_938_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_930_, v_c_929_, v_pos_932_);
lean_dec(v_pos_932_);
v___x_939_ = 95;
v___x_940_ = l_Lake_Toml_sepByChar1Fn(v___f_936_, v___x_939_, v_expected_933_, v_c_929_, v_s_938_);
return v___x_940_;
}
}
else
{
lean_object* v___x_957_; 
v___x_957_ = l_Lean_Parser_ParserState_mkEOIError(v_s_930_, v_expected_933_);
return v___x_957_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___boxed(lean_object* v_c_958_, lean_object* v_s_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(v_c_958_, v_s_959_);
lean_dec_ref(v_c_958_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(lean_object* v_c_961_, lean_object* v_s_962_){
_start:
{
lean_object* v_toInputContext_963_; lean_object* v_pos_964_; uint8_t v___x_968_; 
v_toInputContext_963_ = lean_ctor_get(v_c_961_, 0);
v_pos_964_ = lean_ctor_get(v_s_962_, 2);
v___x_968_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_963_, v_pos_964_);
if (v___x_968_ == 0)
{
lean_object* v_inputString_969_; uint32_t v_curr_970_; uint32_t v___x_971_; uint8_t v___x_972_; 
v_inputString_969_ = lean_ctor_get(v_toInputContext_963_, 0);
v_curr_970_ = lean_string_utf8_get_fast(v_inputString_969_, v_pos_964_);
v___x_971_ = 101;
v___x_972_ = lean_uint32_dec_eq(v_curr_970_, v___x_971_);
if (v___x_972_ == 0)
{
uint32_t v___x_973_; uint8_t v___x_974_; 
v___x_973_ = 69;
v___x_974_ = lean_uint32_dec_eq(v_curr_970_, v___x_973_);
if (v___x_974_ == 0)
{
return v_s_962_;
}
else
{
lean_inc(v_pos_964_);
goto v___jp_965_;
}
}
else
{
lean_inc(v_pos_964_);
goto v___jp_965_;
}
}
else
{
return v_s_962_;
}
v___jp_965_:
{
lean_object* v___x_966_; lean_object* v___x_967_; 
v___x_966_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_962_, v_c_961_, v_pos_964_);
lean_dec(v_pos_964_);
v___x_967_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(v_c_961_, v___x_966_);
return v___x_967_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn___boxed(lean_object* v_c_975_, lean_object* v_s_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(v_c_975_, v_s_976_);
lean_dec_ref(v_c_975_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(lean_object* v_startPos_995_, uint32_t v_curr_996_, lean_object* v_nextPos_997_, lean_object* v_c_998_, lean_object* v_s_999_){
_start:
{
uint32_t v___x_1010_; uint8_t v___x_1011_; 
v___x_1010_ = 46;
v___x_1011_ = lean_uint32_dec_eq(v_curr_996_, v___x_1010_);
if (v___x_1011_ == 0)
{
uint32_t v___x_1012_; uint8_t v___x_1013_; 
v___x_1012_ = 101;
v___x_1013_ = lean_uint32_dec_eq(v_curr_996_, v___x_1012_);
if (v___x_1013_ == 0)
{
uint32_t v___x_1014_; uint8_t v___x_1015_; 
v___x_1014_ = 69;
v___x_1015_ = lean_uint32_dec_eq(v_curr_996_, v___x_1014_);
if (v___x_1015_ == 0)
{
lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
lean_dec(v_nextPos_997_);
v___x_1016_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1017_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1018_ = l_Lake_Toml_pushLit(v___x_1016_, v_startPos_995_, v___x_1017_, v_c_998_, v_s_999_);
return v___x_1018_;
}
else
{
goto v___jp_1000_;
}
}
else
{
goto v___jp_1000_;
}
}
else
{
lean_object* v___f_1019_; lean_object* v_s_1020_; uint32_t v___x_1021_; lean_object* v___x_1022_; lean_object* v_s_1023_; lean_object* v_errorMsg_1024_; lean_object* v___x_1025_; uint8_t v___x_1026_; uint8_t v___x_1027_; 
v___f_1019_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0));
v_s_1020_ = l_Lean_Parser_ParserState_setPos(v_s_999_, v_nextPos_997_);
v___x_1021_ = 95;
v___x_1022_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__8));
v_s_1023_ = l_Lake_Toml_sepByChar1Fn(v___f_1019_, v___x_1021_, v___x_1022_, v_c_998_, v_s_1020_);
v_errorMsg_1024_ = lean_ctor_get(v_s_1023_, 4);
lean_inc(v_errorMsg_1024_);
v___x_1025_ = lean_box(0);
v___x_1026_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1024_, v___x_1025_);
v___x_1027_ = lean_bool_not(v___x_1026_);
if (v___x_1027_ == 0)
{
lean_object* v_s_1028_; lean_object* v_errorMsg_1029_; uint8_t v___x_1030_; uint8_t v___x_1031_; 
v_s_1028_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(v_c_998_, v_s_1023_);
v_errorMsg_1029_ = lean_ctor_get(v_s_1028_, 4);
lean_inc(v_errorMsg_1029_);
v___x_1030_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1029_, v___x_1025_);
v___x_1031_ = lean_bool_not(v___x_1030_);
if (v___x_1031_ == 0)
{
lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; 
v___x_1032_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_1033_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1034_ = l_Lake_Toml_pushLit(v___x_1032_, v_startPos_995_, v___x_1033_, v_c_998_, v_s_1028_);
return v___x_1034_;
}
else
{
lean_dec_ref(v_c_998_);
lean_dec(v_startPos_995_);
return v_s_1028_;
}
}
else
{
lean_dec_ref(v_c_998_);
lean_dec(v_startPos_995_);
return v_s_1023_;
}
}
v___jp_1000_:
{
lean_object* v_s_1001_; lean_object* v_s_1002_; lean_object* v_errorMsg_1003_; lean_object* v___x_1004_; uint8_t v___x_1005_; uint8_t v___x_1006_; 
v_s_1001_ = l_Lean_Parser_ParserState_setPos(v_s_999_, v_nextPos_997_);
v_s_1002_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(v_c_998_, v_s_1001_);
v_errorMsg_1003_ = lean_ctor_get(v_s_1002_, 4);
lean_inc(v_errorMsg_1003_);
v___x_1004_ = lean_box(0);
v___x_1005_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1003_, v___x_1004_);
v___x_1006_ = lean_bool_not(v___x_1005_);
if (v___x_1006_ == 0)
{
lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; 
v___x_1007_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_1008_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1009_ = l_Lake_Toml_pushLit(v___x_1007_, v_startPos_995_, v___x_1008_, v_c_998_, v_s_1002_);
return v___x_1009_;
}
else
{
lean_dec_ref(v_c_998_);
lean_dec(v_startPos_995_);
return v_s_1002_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___boxed(lean_object* v_startPos_1035_, lean_object* v_curr_1036_, lean_object* v_nextPos_1037_, lean_object* v_c_1038_, lean_object* v_s_1039_){
_start:
{
uint32_t v_curr_boxed_1040_; lean_object* v_res_1041_; 
v_curr_boxed_1040_ = lean_unbox_uint32(v_curr_1036_);
lean_dec(v_curr_1036_);
v_res_1041_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(v_startPos_1035_, v_curr_boxed_1040_, v_nextPos_1037_, v_c_1038_, v_s_1039_);
return v_res_1041_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailFn(lean_object* v_startPos_1042_, lean_object* v_c_1043_, lean_object* v_s_1044_){
_start:
{
lean_object* v_toInputContext_1045_; lean_object* v_pos_1046_; uint8_t v___x_1047_; 
v_toInputContext_1045_ = lean_ctor_get(v_c_1043_, 0);
v_pos_1046_ = lean_ctor_get(v_s_1044_, 2);
v___x_1047_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1045_, v_pos_1046_);
if (v___x_1047_ == 0)
{
lean_object* v_inputString_1048_; uint32_t v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; 
v_inputString_1048_ = lean_ctor_get(v_toInputContext_1045_, 0);
v___x_1049_ = lean_string_utf8_get_fast(v_inputString_1048_, v_pos_1046_);
v___x_1050_ = lean_string_utf8_next_fast(v_inputString_1048_, v_pos_1046_);
v___x_1051_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(v_startPos_1042_, v___x_1049_, v___x_1050_, v_c_1043_, v_s_1044_);
return v___x_1051_;
}
else
{
lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v___x_1052_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1053_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1054_ = l_Lake_Toml_pushLit(v___x_1052_, v_startPos_1042_, v___x_1053_, v_c_1043_, v_s_1044_);
return v___x_1054_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(lean_object* v_startPos_1062_, lean_object* v_c_1063_, lean_object* v_s_1064_){
_start:
{
lean_object* v_toInputContext_1065_; lean_object* v_pos_1066_; uint8_t v___x_1067_; 
v_toInputContext_1065_ = lean_ctor_get(v_c_1063_, 0);
v_pos_1066_ = lean_ctor_get(v_s_1064_, 2);
v___x_1067_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1065_, v_pos_1066_);
if (v___x_1067_ == 0)
{
lean_object* v_inputString_1068_; uint32_t v_curr_1069_; uint8_t v___y_1071_; uint32_t v___x_1076_; uint8_t v___x_1077_; 
v_inputString_1068_ = lean_ctor_get(v_toInputContext_1065_, 0);
v_curr_1069_ = lean_string_utf8_get_fast(v_inputString_1068_, v_pos_1066_);
v___x_1076_ = 48;
v___x_1077_ = lean_uint32_dec_le(v___x_1076_, v_curr_1069_);
if (v___x_1077_ == 0)
{
v___y_1071_ = v___x_1077_;
goto v___jp_1070_;
}
else
{
uint32_t v___x_1078_; uint8_t v___x_1079_; 
v___x_1078_ = 57;
v___x_1079_ = lean_uint32_dec_le(v_curr_1069_, v___x_1078_);
v___y_1071_ = v___x_1079_;
goto v___jp_1070_;
}
v___jp_1070_:
{
if (v___y_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
v___x_1072_ = lean_string_utf8_next_fast(v_inputString_1068_, v_pos_1066_);
v___x_1073_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1062_, v_curr_1069_, v___x_1072_, v_c_1063_, v_s_1064_);
return v___x_1073_;
}
else
{
lean_object* v_s_1074_; 
lean_inc(v_pos_1066_);
v_s_1074_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1064_, v_c_1063_, v_pos_1066_);
lean_dec(v_pos_1066_);
v_s_1064_ = v_s_1074_;
goto _start;
}
}
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1080_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1081_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1082_ = l_Lake_Toml_pushLit(v___x_1080_, v_startPos_1062_, v___x_1081_, v_c_1063_, v_s_1064_);
return v___x_1082_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn(lean_object* v_startPos_1083_, lean_object* v_c_1084_, lean_object* v_s_1085_){
_start:
{
lean_object* v_pos_1086_; lean_object* v_toInputContext_1087_; lean_object* v_expected_1088_; uint8_t v___x_1089_; 
v_pos_1086_ = lean_ctor_get(v_s_1085_, 2);
v_toInputContext_1087_ = lean_ctor_get(v_c_1084_, 0);
v_expected_1088_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2));
v___x_1089_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1087_, v_pos_1086_);
if (v___x_1089_ == 0)
{
lean_object* v_inputString_1090_; uint8_t v___x_1091_; uint32_t v_curr_1092_; uint8_t v___y_1094_; uint32_t v___x_1098_; uint8_t v___x_1099_; 
v_inputString_1090_ = lean_ctor_get(v_toInputContext_1087_, 0);
v___x_1091_ = 1;
v_curr_1092_ = lean_string_utf8_get_fast(v_inputString_1090_, v_pos_1086_);
v___x_1098_ = 48;
v___x_1099_ = lean_uint32_dec_le(v___x_1098_, v_curr_1092_);
if (v___x_1099_ == 0)
{
v___y_1094_ = v___x_1099_;
goto v___jp_1093_;
}
else
{
uint32_t v___x_1100_; uint8_t v___x_1101_; 
v___x_1100_ = 57;
v___x_1101_ = lean_uint32_dec_le(v_curr_1092_, v___x_1100_);
v___y_1094_ = v___x_1101_;
goto v___jp_1093_;
}
v___jp_1093_:
{
if (v___y_1094_ == 0)
{
lean_object* v___x_1095_; 
lean_dec_ref(v_c_1084_);
lean_dec(v_startPos_1083_);
v___x_1095_ = l_Lake_Toml_mkUnexpectedCharError(v_s_1085_, v_curr_1092_, v_expected_1088_, v___x_1091_);
return v___x_1095_;
}
else
{
lean_object* v_s_1096_; lean_object* v___x_1097_; 
lean_inc(v_pos_1086_);
v_s_1096_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1085_, v_c_1084_, v_pos_1086_);
lean_dec(v_pos_1086_);
v___x_1097_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(v_startPos_1083_, v_c_1084_, v_s_1096_);
return v___x_1097_;
}
}
}
else
{
lean_object* v___x_1102_; 
lean_dec_ref(v_c_1084_);
lean_dec(v_startPos_1083_);
v___x_1102_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1085_, v_expected_1088_);
return v___x_1102_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(lean_object* v_startPos_1103_, uint32_t v_curr_1104_, lean_object* v_nextPos_1105_, lean_object* v_c_1106_, lean_object* v_s_1107_){
_start:
{
uint32_t v___x_1108_; uint8_t v___x_1109_; 
v___x_1108_ = 95;
v___x_1109_ = lean_uint32_dec_eq(v_curr_1104_, v___x_1108_);
if (v___x_1109_ == 0)
{
lean_object* v___x_1110_; 
v___x_1110_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(v_startPos_1103_, v_curr_1104_, v_nextPos_1105_, v_c_1106_, v_s_1107_);
return v___x_1110_;
}
else
{
lean_object* v_s_1111_; lean_object* v___x_1112_; 
v_s_1111_ = l_Lean_Parser_ParserState_setPos(v_s_1107_, v_nextPos_1105_);
v___x_1112_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn(v_startPos_1103_, v_c_1106_, v_s_1111_);
return v___x_1112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn___boxed(lean_object* v_startPos_1113_, lean_object* v_curr_1114_, lean_object* v_nextPos_1115_, lean_object* v_c_1116_, lean_object* v_s_1117_){
_start:
{
uint32_t v_curr_boxed_1118_; lean_object* v_res_1119_; 
v_curr_boxed_1118_ = lean_unbox_uint32(v_curr_1114_);
lean_dec(v_curr_1114_);
v_res_1119_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1113_, v_curr_boxed_1118_, v_nextPos_1115_, v_c_1116_, v_s_1117_);
return v_res_1119_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(lean_object* v_startPos_1125_, lean_object* v_a_1126_, lean_object* v_a_1127_){
_start:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v_s_1130_; lean_object* v_errorMsg_1131_; lean_object* v___x_1132_; uint8_t v___x_1133_; uint8_t v___x_1134_; 
v___x_1128_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__0));
v___x_1129_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__2));
lean_inc_ref(v_a_1126_);
v_s_1130_ = l_Lake_Toml_strFn(v___x_1128_, v___x_1129_, v_a_1126_, v_a_1127_);
v_errorMsg_1131_ = lean_ctor_get(v_s_1130_, 4);
lean_inc(v_errorMsg_1131_);
v___x_1132_ = lean_box(0);
v___x_1133_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1131_, v___x_1132_);
v___x_1134_ = lean_bool_not(v___x_1133_);
if (v___x_1134_ == 0)
{
lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
v___x_1135_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_1136_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1137_ = l_Lake_Toml_pushLit(v___x_1135_, v_startPos_1125_, v___x_1136_, v_a_1126_, v_s_1130_);
return v___x_1137_;
}
else
{
lean_dec_ref(v_a_1126_);
lean_dec(v_startPos_1125_);
return v_s_1130_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(lean_object* v_startPos_1143_, lean_object* v_a_1144_, lean_object* v_a_1145_){
_start:
{
lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v_s_1148_; lean_object* v_errorMsg_1149_; lean_object* v___x_1150_; uint8_t v___x_1151_; uint8_t v___x_1152_; 
v___x_1146_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__0));
v___x_1147_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__2));
lean_inc_ref(v_a_1144_);
v_s_1148_ = l_Lake_Toml_strFn(v___x_1146_, v___x_1147_, v_a_1144_, v_a_1145_);
v_errorMsg_1149_ = lean_ctor_get(v_s_1148_, 4);
lean_inc(v_errorMsg_1149_);
v___x_1150_ = lean_box(0);
v___x_1151_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1149_, v___x_1150_);
v___x_1152_ = lean_bool_not(v___x_1151_);
if (v___x_1152_ == 0)
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1153_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_1154_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1155_ = l_Lake_Toml_pushLit(v___x_1153_, v_startPos_1143_, v___x_1154_, v_a_1144_, v_s_1148_);
return v___x_1155_;
}
else
{
lean_dec_ref(v_a_1144_);
lean_dec(v_startPos_1143_);
return v_s_1148_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decimalFn(lean_object* v_startPos_1156_, lean_object* v_c_1157_, lean_object* v_s_1158_){
_start:
{
lean_object* v_toInputContext_1159_; lean_object* v_pos_1160_; lean_object* v_expected_1161_; uint8_t v___x_1162_; 
v_toInputContext_1159_ = lean_ctor_get(v_c_1157_, 0);
v_pos_1160_ = lean_ctor_get(v_s_1158_, 2);
v_expected_1161_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2));
v___x_1162_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1159_, v_pos_1160_);
if (v___x_1162_ == 0)
{
lean_object* v_inputString_1163_; uint32_t v_curr_1164_; uint32_t v___x_1165_; uint8_t v___x_1166_; 
v_inputString_1163_ = lean_ctor_get(v_toInputContext_1159_, 0);
v_curr_1164_ = lean_string_utf8_get_fast(v_inputString_1163_, v_pos_1160_);
v___x_1165_ = 48;
v___x_1166_ = lean_uint32_dec_eq(v_curr_1164_, v___x_1165_);
if (v___x_1166_ == 0)
{
uint8_t v___x_1167_; uint8_t v___y_1169_; uint8_t v___x_1181_; 
v___x_1167_ = 1;
v___x_1181_ = lean_uint32_dec_le(v___x_1165_, v_curr_1164_);
if (v___x_1181_ == 0)
{
v___y_1169_ = v___x_1181_;
goto v___jp_1168_;
}
else
{
uint32_t v___x_1182_; uint8_t v___x_1183_; 
v___x_1182_ = 57;
v___x_1183_ = lean_uint32_dec_le(v_curr_1164_, v___x_1182_);
v___y_1169_ = v___x_1183_;
goto v___jp_1168_;
}
v___jp_1168_:
{
if (v___y_1169_ == 0)
{
uint32_t v___x_1170_; uint8_t v___x_1171_; 
v___x_1170_ = 105;
v___x_1171_ = lean_uint32_dec_eq(v_curr_1164_, v___x_1170_);
if (v___x_1171_ == 0)
{
uint32_t v___x_1172_; uint8_t v___x_1173_; 
v___x_1172_ = 110;
v___x_1173_ = lean_uint32_dec_eq(v_curr_1164_, v___x_1172_);
if (v___x_1173_ == 0)
{
lean_object* v___x_1174_; 
lean_dec_ref(v_c_1157_);
lean_dec(v_startPos_1156_);
v___x_1174_ = l_Lake_Toml_mkUnexpectedCharError(v_s_1158_, v_curr_1164_, v_expected_1161_, v___x_1167_);
return v___x_1174_;
}
else
{
lean_object* v___x_1175_; lean_object* v___x_1176_; 
lean_inc(v_pos_1160_);
v___x_1175_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1158_, v_c_1157_, v_pos_1160_);
lean_dec(v_pos_1160_);
v___x_1176_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(v_startPos_1156_, v_c_1157_, v___x_1175_);
return v___x_1176_;
}
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_inc(v_pos_1160_);
v___x_1177_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1158_, v_c_1157_, v_pos_1160_);
lean_dec(v_pos_1160_);
v___x_1178_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(v_startPos_1156_, v_c_1157_, v___x_1177_);
return v___x_1178_;
}
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_inc(v_pos_1160_);
v___x_1179_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1158_, v_c_1157_, v_pos_1160_);
lean_dec(v_pos_1160_);
v___x_1180_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(v_startPos_1156_, v_c_1157_, v___x_1179_);
return v___x_1180_;
}
}
}
else
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
lean_inc(v_pos_1160_);
v___x_1184_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1158_, v_c_1157_, v_pos_1160_);
lean_dec(v_pos_1160_);
v___x_1185_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailFn(v_startPos_1156_, v_c_1157_, v___x_1184_);
return v___x_1185_;
}
}
else
{
lean_object* v___x_1186_; 
lean_dec_ref(v_c_1157_);
lean_dec(v_startPos_1156_);
v___x_1186_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1158_, v_expected_1161_);
return v___x_1186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn(lean_object* v_startPos_1202_, lean_object* v_c_1203_, lean_object* v_s_1204_){
_start:
{
lean_object* v___y_1206_; lean_object* v___y_1207_; uint32_t v___y_1208_; uint8_t v___y_1209_; lean_object* v_toInputContext_1213_; lean_object* v_pos_1214_; uint8_t v___x_1215_; 
v_toInputContext_1213_ = lean_ctor_get(v_c_1203_, 0);
v_pos_1214_ = lean_ctor_get(v_s_1204_, 2);
v___x_1215_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1213_, v_pos_1214_);
if (v___x_1215_ == 0)
{
lean_object* v_inputString_1216_; uint32_t v___y_1218_; lean_object* v___y_1219_; lean_object* v___y_1220_; uint8_t v___y_1221_; lean_object* v___y_1247_; uint32_t v___y_1248_; lean_object* v___y_1249_; uint8_t v___y_1250_; uint32_t v_curr_1264_; lean_object* v_nextPos_1265_; uint8_t v___y_1267_; uint32_t v___x_1292_; uint8_t v___x_1293_; 
v_inputString_1216_ = lean_ctor_get(v_toInputContext_1213_, 0);
v_curr_1264_ = lean_string_utf8_get_fast(v_inputString_1216_, v_pos_1214_);
v_nextPos_1265_ = lean_string_utf8_next_fast(v_inputString_1216_, v_pos_1214_);
v___x_1292_ = 48;
v___x_1293_ = lean_uint32_dec_le(v___x_1292_, v_curr_1264_);
if (v___x_1293_ == 0)
{
v___y_1267_ = v___x_1293_;
goto v___jp_1266_;
}
else
{
uint32_t v___x_1294_; uint8_t v___x_1295_; 
v___x_1294_ = 57;
v___x_1295_ = lean_uint32_dec_le(v_curr_1264_, v___x_1294_);
v___y_1267_ = v___x_1295_;
goto v___jp_1266_;
}
v___jp_1217_:
{
if (v___y_1221_ == 0)
{
lean_object* v___x_1222_; 
v___x_1222_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1202_, v___y_1218_, v___y_1219_, v_c_1203_, v___y_1220_);
return v___x_1222_;
}
else
{
lean_object* v_s_1223_; uint8_t v___x_1224_; 
lean_inc(v___y_1219_);
v_s_1223_ = l_Lean_Parser_ParserState_setPos(v___y_1220_, v___y_1219_);
v___x_1224_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1213_, v___y_1219_);
lean_dec(v___y_1219_);
if (v___x_1224_ == 0)
{
lean_object* v_pos_1225_; uint32_t v_curr_1226_; lean_object* v_nextPos_1227_; uint32_t v___x_1228_; uint8_t v___x_1229_; 
v_pos_1225_ = lean_ctor_get(v_s_1223_, 2);
lean_inc(v_pos_1225_);
v_curr_1226_ = lean_string_utf8_get_fast(v_inputString_1216_, v_pos_1225_);
v_nextPos_1227_ = lean_string_utf8_next_fast(v_inputString_1216_, v_pos_1225_);
lean_dec(v_pos_1225_);
v___x_1228_ = 45;
v___x_1229_ = lean_uint32_dec_eq(v_curr_1226_, v___x_1228_);
if (v___x_1229_ == 0)
{
uint32_t v___x_1230_; uint8_t v___x_1231_; 
v___x_1230_ = 48;
v___x_1231_ = lean_uint32_dec_le(v___x_1230_, v_curr_1226_);
if (v___x_1231_ == 0)
{
v___y_1206_ = v_nextPos_1227_;
v___y_1207_ = v_s_1223_;
v___y_1208_ = v_curr_1226_;
v___y_1209_ = v___x_1231_;
goto v___jp_1205_;
}
else
{
uint32_t v___x_1232_; uint8_t v___x_1233_; 
v___x_1232_ = 57;
v___x_1233_ = lean_uint32_dec_le(v_curr_1226_, v___x_1232_);
v___y_1206_ = v_nextPos_1227_;
v___y_1207_ = v_s_1223_;
v___y_1208_ = v_curr_1226_;
v___y_1209_ = v___x_1233_;
goto v___jp_1205_;
}
}
else
{
lean_object* v_s_1234_; lean_object* v_s_1235_; lean_object* v_errorMsg_1236_; lean_object* v___x_1237_; uint8_t v___x_1238_; uint8_t v___x_1239_; 
v_s_1234_ = l_Lean_Parser_ParserState_setPos(v_s_1223_, v_nextPos_1227_);
v_s_1235_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(v_c_1203_, v_s_1234_);
v_errorMsg_1236_ = lean_ctor_get(v_s_1235_, 4);
lean_inc(v_errorMsg_1236_);
v___x_1237_ = lean_box(0);
v___x_1238_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1236_, v___x_1237_);
v___x_1239_ = lean_bool_not(v___x_1238_);
if (v___x_1239_ == 0)
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; 
v___x_1240_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_1241_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1242_ = l_Lake_Toml_pushLit(v___x_1240_, v_startPos_1202_, v___x_1241_, v_c_1203_, v_s_1235_);
return v___x_1242_;
}
else
{
lean_dec_ref(v_c_1203_);
lean_dec(v_startPos_1202_);
return v_s_1235_;
}
}
}
else
{
lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; 
v___x_1243_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1244_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1245_ = l_Lake_Toml_pushLit(v___x_1243_, v_startPos_1202_, v___x_1244_, v_c_1203_, v_s_1223_);
return v___x_1245_;
}
}
}
v___jp_1246_:
{
if (v___y_1250_ == 0)
{
lean_object* v___x_1251_; 
v___x_1251_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1202_, v___y_1248_, v___y_1249_, v_c_1203_, v___y_1247_);
return v___x_1251_;
}
else
{
lean_object* v_s_1252_; lean_object* v_pos_1253_; uint8_t v___x_1254_; 
v_s_1252_ = l_Lean_Parser_ParserState_setPos(v___y_1247_, v___y_1249_);
v_pos_1253_ = lean_ctor_get(v_s_1252_, 2);
lean_inc(v_pos_1253_);
v___x_1254_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1213_, v_pos_1253_);
if (v___x_1254_ == 0)
{
uint32_t v_curr_1255_; lean_object* v_nextPos_1256_; uint32_t v___x_1257_; uint8_t v___x_1258_; 
v_curr_1255_ = lean_string_utf8_get_fast(v_inputString_1216_, v_pos_1253_);
v_nextPos_1256_ = lean_string_utf8_next_fast(v_inputString_1216_, v_pos_1253_);
lean_dec(v_pos_1253_);
v___x_1257_ = 48;
v___x_1258_ = lean_uint32_dec_le(v___x_1257_, v_curr_1255_);
if (v___x_1258_ == 0)
{
v___y_1218_ = v_curr_1255_;
v___y_1219_ = v_nextPos_1256_;
v___y_1220_ = v_s_1252_;
v___y_1221_ = v___x_1258_;
goto v___jp_1217_;
}
else
{
uint32_t v___x_1259_; uint8_t v___x_1260_; 
v___x_1259_ = 57;
v___x_1260_ = lean_uint32_dec_le(v_curr_1255_, v___x_1259_);
v___y_1218_ = v_curr_1255_;
v___y_1219_ = v_nextPos_1256_;
v___y_1220_ = v_s_1252_;
v___y_1221_ = v___x_1260_;
goto v___jp_1217_;
}
}
else
{
lean_object* v___x_1261_; lean_object* v___x_1262_; lean_object* v___x_1263_; 
lean_dec(v_pos_1253_);
v___x_1261_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1262_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1263_ = l_Lake_Toml_pushLit(v___x_1261_, v_startPos_1202_, v___x_1262_, v_c_1203_, v_s_1252_);
return v___x_1263_;
}
}
}
v___jp_1266_:
{
if (v___y_1267_ == 0)
{
lean_object* v___x_1268_; 
v___x_1268_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1202_, v_curr_1264_, v_nextPos_1265_, v_c_1203_, v_s_1204_);
return v___x_1268_;
}
else
{
lean_object* v_s_1269_; lean_object* v_pos_1270_; uint8_t v___x_1271_; 
v_s_1269_ = l_Lean_Parser_ParserState_setPos(v_s_1204_, v_nextPos_1265_);
v_pos_1270_ = lean_ctor_get(v_s_1269_, 2);
lean_inc(v_pos_1270_);
v___x_1271_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1213_, v_pos_1270_);
if (v___x_1271_ == 0)
{
uint32_t v_curr_1272_; lean_object* v_nextPos_1273_; uint32_t v___x_1274_; uint8_t v___x_1275_; 
v_curr_1272_ = lean_string_utf8_get_fast(v_inputString_1216_, v_pos_1270_);
v_nextPos_1273_ = lean_string_utf8_next_fast(v_inputString_1216_, v_pos_1270_);
lean_dec(v_pos_1270_);
v___x_1274_ = 58;
v___x_1275_ = lean_uint32_dec_eq(v_curr_1272_, v___x_1274_);
if (v___x_1275_ == 0)
{
uint32_t v___x_1276_; uint8_t v___x_1277_; 
v___x_1276_ = 48;
v___x_1277_ = lean_uint32_dec_le(v___x_1276_, v_curr_1272_);
if (v___x_1277_ == 0)
{
v___y_1247_ = v_s_1269_;
v___y_1248_ = v_curr_1272_;
v___y_1249_ = v_nextPos_1273_;
v___y_1250_ = v___x_1277_;
goto v___jp_1246_;
}
else
{
uint32_t v___x_1278_; uint8_t v___x_1279_; 
v___x_1278_ = 57;
v___x_1279_ = lean_uint32_dec_le(v_curr_1272_, v___x_1278_);
v___y_1247_ = v_s_1269_;
v___y_1248_ = v_curr_1272_;
v___y_1249_ = v_nextPos_1273_;
v___y_1250_ = v___x_1279_;
goto v___jp_1246_;
}
}
else
{
lean_object* v_s_1280_; lean_object* v_s_1281_; lean_object* v_errorMsg_1282_; lean_object* v___x_1283_; uint8_t v___x_1284_; uint8_t v___x_1285_; 
v_s_1280_ = l_Lean_Parser_ParserState_setPos(v_s_1269_, v_nextPos_1273_);
v_s_1281_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(v___x_1271_, v_c_1203_, v_s_1280_);
v_errorMsg_1282_ = lean_ctor_get(v_s_1281_, 4);
lean_inc(v_errorMsg_1282_);
v___x_1283_ = lean_box(0);
v___x_1284_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1282_, v___x_1283_);
v___x_1285_ = lean_bool_not(v___x_1284_);
if (v___x_1285_ == 0)
{
lean_object* v___x_1286_; lean_object* v___x_1287_; lean_object* v___x_1288_; 
v___x_1286_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_1287_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1288_ = l_Lake_Toml_pushLit(v___x_1286_, v_startPos_1202_, v___x_1287_, v_c_1203_, v_s_1281_);
return v___x_1288_;
}
else
{
lean_dec_ref(v_c_1203_);
lean_dec(v_startPos_1202_);
return v_s_1281_;
}
}
}
else
{
lean_object* v___x_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; 
lean_dec(v_pos_1270_);
v___x_1289_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1290_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1291_ = l_Lake_Toml_pushLit(v___x_1289_, v_startPos_1202_, v___x_1290_, v_c_1203_, v_s_1269_);
return v___x_1291_;
}
}
}
}
else
{
lean_object* v___x_1296_; lean_object* v___x_1297_; 
lean_dec_ref(v_c_1203_);
lean_dec(v_startPos_1202_);
v___x_1296_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__5));
v___x_1297_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1204_, v___x_1296_);
return v___x_1297_;
}
v___jp_1205_:
{
if (v___y_1209_ == 0)
{
lean_object* v___x_1210_; 
v___x_1210_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(v_startPos_1202_, v___y_1208_, v___y_1206_, v_c_1203_, v___y_1207_);
return v___x_1210_;
}
else
{
lean_object* v_s_1211_; lean_object* v___x_1212_; 
v_s_1211_ = l_Lean_Parser_ParserState_setPos(v___y_1207_, v___y_1206_);
v___x_1212_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(v_startPos_1202_, v_c_1203_, v_s_1211_);
return v___x_1212_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralFn___lam__0(lean_object* v_c_1333_, lean_object* v_s_1334_){
_start:
{
lean_object* v_pos_1335_; lean_object* v___y_1340_; lean_object* v_toInputContext_1348_; lean_object* v_expected_1349_; uint8_t v___x_1350_; 
v_pos_1335_ = lean_ctor_get(v_s_1334_, 2);
v_toInputContext_1348_ = lean_ctor_get(v_c_1333_, 0);
v_expected_1349_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__1));
v___x_1350_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1348_, v_pos_1335_);
if (v___x_1350_ == 0)
{
lean_object* v_inputString_1351_; uint32_t v_curr_1352_; uint32_t v___x_1353_; uint8_t v___x_1354_; 
v_inputString_1351_ = lean_ctor_get(v_toInputContext_1348_, 0);
v_curr_1352_ = lean_string_utf8_get_fast(v_inputString_1351_, v_pos_1335_);
v___x_1353_ = 48;
v___x_1354_ = lean_uint32_dec_eq(v_curr_1352_, v___x_1353_);
if (v___x_1354_ == 0)
{
uint8_t v___x_1355_; uint8_t v___y_1357_; uint8_t v___x_1379_; 
v___x_1355_ = 1;
v___x_1379_ = lean_uint32_dec_le(v___x_1353_, v_curr_1352_);
if (v___x_1379_ == 0)
{
v___y_1357_ = v___x_1379_;
goto v___jp_1356_;
}
else
{
uint32_t v___x_1380_; uint8_t v___x_1381_; 
v___x_1380_ = 57;
v___x_1381_ = lean_uint32_dec_le(v_curr_1352_, v___x_1380_);
v___y_1357_ = v___x_1381_;
goto v___jp_1356_;
}
v___jp_1356_:
{
if (v___y_1357_ == 0)
{
uint32_t v___x_1358_; uint8_t v___x_1359_; 
v___x_1358_ = 43;
v___x_1359_ = lean_uint32_dec_eq(v_curr_1352_, v___x_1358_);
if (v___x_1359_ == 0)
{
uint32_t v___x_1360_; uint8_t v___x_1361_; 
v___x_1360_ = 45;
v___x_1361_ = lean_uint32_dec_eq(v_curr_1352_, v___x_1360_);
if (v___x_1361_ == 0)
{
uint32_t v___x_1362_; uint8_t v___x_1363_; 
v___x_1362_ = 105;
v___x_1363_ = lean_uint32_dec_eq(v_curr_1352_, v___x_1362_);
if (v___x_1363_ == 0)
{
uint32_t v___x_1364_; uint8_t v___x_1365_; 
v___x_1364_ = 110;
v___x_1365_ = lean_uint32_dec_eq(v_curr_1352_, v___x_1364_);
if (v___x_1365_ == 0)
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v___x_1368_; lean_object* v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; 
lean_dec_ref(v_c_1333_);
v___x_1366_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__2));
v___x_1367_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_1368_ = lean_string_push(v___x_1367_, v_curr_1352_);
v___x_1369_ = lean_string_append(v___x_1366_, v___x_1368_);
lean_dec_ref(v___x_1368_);
v___x_1370_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1371_ = lean_string_append(v___x_1369_, v___x_1370_);
v___x_1372_ = l_Lean_Parser_ParserState_mkUnexpectedError(v_s_1334_, v___x_1371_, v_expected_1349_, v___x_1355_);
return v___x_1372_;
}
else
{
lean_object* v___x_1373_; lean_object* v___x_1374_; 
lean_inc(v_pos_1335_);
v___x_1373_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1334_, v_c_1333_, v_pos_1335_);
v___x_1374_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(v_pos_1335_, v_c_1333_, v___x_1373_);
return v___x_1374_;
}
}
else
{
lean_object* v___x_1375_; lean_object* v___x_1376_; 
lean_inc(v_pos_1335_);
v___x_1375_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1334_, v_c_1333_, v_pos_1335_);
v___x_1376_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(v_pos_1335_, v_c_1333_, v___x_1375_);
return v___x_1376_;
}
}
else
{
lean_inc(v_pos_1335_);
goto v___jp_1336_;
}
}
else
{
lean_inc(v_pos_1335_);
goto v___jp_1336_;
}
}
else
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
lean_inc(v_pos_1335_);
v___x_1377_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1334_, v_c_1333_, v_pos_1335_);
v___x_1378_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn(v_pos_1335_, v_c_1333_, v___x_1377_);
return v___x_1378_;
}
}
}
else
{
lean_object* v_s_1382_; lean_object* v_pos_1383_; uint8_t v___x_1384_; 
lean_inc(v_pos_1335_);
v_s_1382_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1334_, v_c_1333_, v_pos_1335_);
v_pos_1383_ = lean_ctor_get(v_s_1382_, 2);
lean_inc(v_pos_1383_);
v___x_1384_ = l_Lean_Parser_InputContext_atEnd(v_toInputContext_1348_, v_pos_1383_);
if (v___x_1384_ == 0)
{
uint32_t v_curr_1385_; uint8_t v___y_1387_; uint32_t v___x_1399_; uint8_t v___x_1400_; 
v_curr_1385_ = lean_string_utf8_get_fast(v_inputString_1351_, v_pos_1383_);
v___x_1399_ = 98;
v___x_1400_ = lean_uint32_dec_eq(v_curr_1385_, v___x_1399_);
if (v___x_1400_ == 0)
{
uint32_t v___x_1401_; uint8_t v___x_1402_; 
v___x_1401_ = 111;
v___x_1402_ = lean_uint32_dec_eq(v_curr_1385_, v___x_1401_);
if (v___x_1402_ == 0)
{
uint32_t v___x_1403_; uint8_t v___x_1404_; 
v___x_1403_ = 120;
v___x_1404_ = lean_uint32_dec_eq(v_curr_1385_, v___x_1403_);
if (v___x_1404_ == 0)
{
uint8_t v___x_1405_; 
v___x_1405_ = lean_uint32_dec_le(v___x_1353_, v_curr_1385_);
if (v___x_1405_ == 0)
{
v___y_1387_ = v___x_1405_;
goto v___jp_1386_;
}
else
{
uint32_t v___x_1406_; uint8_t v___x_1407_; 
v___x_1406_ = 57;
v___x_1407_ = lean_uint32_dec_le(v_curr_1385_, v___x_1406_);
v___y_1387_ = v___x_1407_;
goto v___jp_1386_;
}
}
else
{
lean_object* v_s_1408_; lean_object* v___x_1409_; uint32_t v___x_1410_; lean_object* v___x_1411_; lean_object* v_s_1412_; lean_object* v_errorMsg_1413_; lean_object* v___x_1414_; uint8_t v___x_1415_; uint8_t v___x_1416_; 
v_s_1408_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1382_, v_c_1333_, v_pos_1383_);
lean_dec(v_pos_1383_);
v___x_1409_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__3));
v___x_1410_ = 95;
v___x_1411_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__5));
v_s_1412_ = l_Lake_Toml_sepByChar1Fn(v___x_1409_, v___x_1410_, v___x_1411_, v_c_1333_, v_s_1408_);
v_errorMsg_1413_ = lean_ctor_get(v_s_1412_, 4);
lean_inc(v_errorMsg_1413_);
v___x_1414_ = lean_box(0);
v___x_1415_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1413_, v___x_1414_);
v___x_1416_ = lean_bool_not(v___x_1415_);
if (v___x_1416_ == 0)
{
lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v___x_1417_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__7));
v___x_1418_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1419_ = l_Lake_Toml_pushLit(v___x_1417_, v_pos_1335_, v___x_1418_, v_c_1333_, v_s_1412_);
return v___x_1419_;
}
else
{
lean_dec(v_pos_1335_);
lean_dec_ref(v_c_1333_);
return v_s_1412_;
}
}
}
else
{
lean_object* v_s_1420_; lean_object* v___x_1421_; uint32_t v___x_1422_; lean_object* v___x_1423_; lean_object* v_s_1424_; lean_object* v_errorMsg_1425_; lean_object* v___x_1426_; uint8_t v___x_1427_; uint8_t v___x_1428_; 
v_s_1420_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1382_, v_c_1333_, v_pos_1383_);
lean_dec(v_pos_1383_);
v___x_1421_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__8));
v___x_1422_ = 95;
v___x_1423_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__10));
v_s_1424_ = l_Lake_Toml_sepByChar1Fn(v___x_1421_, v___x_1422_, v___x_1423_, v_c_1333_, v_s_1420_);
v_errorMsg_1425_ = lean_ctor_get(v_s_1424_, 4);
lean_inc(v_errorMsg_1425_);
v___x_1426_ = lean_box(0);
v___x_1427_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1425_, v___x_1426_);
v___x_1428_ = lean_bool_not(v___x_1427_);
if (v___x_1428_ == 0)
{
lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1431_; 
v___x_1429_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__12));
v___x_1430_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1431_ = l_Lake_Toml_pushLit(v___x_1429_, v_pos_1335_, v___x_1430_, v_c_1333_, v_s_1424_);
return v___x_1431_;
}
else
{
lean_dec(v_pos_1335_);
lean_dec_ref(v_c_1333_);
return v_s_1424_;
}
}
}
else
{
lean_object* v_s_1432_; lean_object* v___x_1433_; uint32_t v___x_1434_; lean_object* v___x_1435_; lean_object* v_s_1436_; lean_object* v_errorMsg_1437_; lean_object* v___x_1438_; uint8_t v___x_1439_; uint8_t v___x_1440_; 
v_s_1432_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1382_, v_c_1333_, v_pos_1383_);
lean_dec(v_pos_1383_);
v___x_1433_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__13));
v___x_1434_ = 95;
v___x_1435_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__15));
v_s_1436_ = l_Lake_Toml_sepByChar1Fn(v___x_1433_, v___x_1434_, v___x_1435_, v_c_1333_, v_s_1432_);
v_errorMsg_1437_ = lean_ctor_get(v_s_1436_, 4);
lean_inc(v_errorMsg_1437_);
v___x_1438_ = lean_box(0);
v___x_1439_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1437_, v___x_1438_);
v___x_1440_ = lean_bool_not(v___x_1439_);
if (v___x_1440_ == 0)
{
lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
v___x_1441_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__17));
v___x_1442_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1443_ = l_Lake_Toml_pushLit(v___x_1441_, v_pos_1335_, v___x_1442_, v_c_1333_, v_s_1436_);
return v___x_1443_;
}
else
{
lean_dec(v_pos_1335_);
lean_dec_ref(v_c_1333_);
return v_s_1436_;
}
}
v___jp_1386_:
{
if (v___y_1387_ == 0)
{
lean_object* v___x_1388_; lean_object* v___x_1389_; 
v___x_1388_ = lean_string_utf8_next_fast(v_inputString_1351_, v_pos_1383_);
lean_dec(v_pos_1383_);
v___x_1389_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(v_pos_1335_, v_curr_1385_, v___x_1388_, v_c_1333_, v_s_1382_);
return v___x_1389_;
}
else
{
lean_object* v_s_1390_; uint32_t v___x_1391_; lean_object* v___x_1392_; lean_object* v_s_1393_; lean_object* v_errorMsg_1394_; lean_object* v___x_1395_; uint8_t v___x_1396_; uint8_t v___x_1397_; 
v_s_1390_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1382_, v_c_1333_, v_pos_1383_);
lean_dec(v_pos_1383_);
v___x_1391_ = 58;
v___x_1392_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7, &l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7);
v_s_1393_ = l_Lake_Toml_chFn(v___x_1391_, v___x_1392_, v_c_1333_, v_s_1390_);
v_errorMsg_1394_ = lean_ctor_get(v_s_1393_, 4);
lean_inc(v_errorMsg_1394_);
v___x_1395_ = lean_box(0);
v___x_1396_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1394_, v___x_1395_);
v___x_1397_ = lean_bool_not(v___x_1396_);
if (v___x_1397_ == 0)
{
lean_object* v___x_1398_; 
v___x_1398_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(v___x_1397_, v_c_1333_, v_s_1393_);
v___y_1340_ = v___x_1398_;
goto v___jp_1339_;
}
else
{
v___y_1340_ = v_s_1393_;
goto v___jp_1339_;
}
}
}
}
else
{
lean_object* v___x_1444_; lean_object* v___x_1445_; lean_object* v___x_1446_; 
lean_dec(v_pos_1383_);
v___x_1444_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1445_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1446_ = l_Lake_Toml_pushLit(v___x_1444_, v_pos_1335_, v___x_1445_, v_c_1333_, v_s_1382_);
return v___x_1446_;
}
}
}
else
{
lean_object* v___x_1447_; 
lean_dec_ref(v_c_1333_);
v___x_1447_ = l_Lean_Parser_ParserState_mkEOIError(v_s_1334_, v_expected_1349_);
return v___x_1447_;
}
v___jp_1336_:
{
lean_object* v___x_1337_; lean_object* v___x_1338_; 
v___x_1337_ = l_Lean_Parser_ParserState_next_x27___redArg(v_s_1334_, v_c_1333_, v_pos_1335_);
v___x_1338_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_decimalFn(v_pos_1335_, v_c_1333_, v___x_1337_);
return v___x_1338_;
}
v___jp_1339_:
{
lean_object* v_errorMsg_1341_; lean_object* v___x_1342_; uint8_t v___x_1343_; uint8_t v___x_1344_; 
v_errorMsg_1341_ = lean_ctor_get(v___y_1340_, 4);
v___x_1342_ = lean_box(0);
lean_inc(v_errorMsg_1341_);
v___x_1343_ = l_Option_instBEq_beq___at___00Lake_Toml_commentFn_spec__0(v_errorMsg_1341_, v___x_1342_);
v___x_1344_ = lean_bool_not(v___x_1343_);
if (v___x_1344_ == 0)
{
lean_object* v___x_1345_; lean_object* v___x_1346_; lean_object* v___x_1347_; 
v___x_1345_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_1346_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1347_ = l_Lake_Toml_pushLit(v___x_1345_, v_pos_1335_, v___x_1346_, v_c_1333_, v___y_1340_);
return v___x_1347_;
}
else
{
lean_dec(v_pos_1335_);
lean_dec_ref(v_c_1333_);
return v___y_1340_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralFn(lean_object* v_a_1449_, lean_object* v_a_1450_){
_start:
{
lean_object* v___f_1451_; lean_object* v___x_1452_; 
v___f_1451_ = ((lean_object*)(l_Lake_Toml_numeralFn___closed__0));
v___x_1452_ = l_Lean_Parser_atomicFn(v___f_1451_, v_a_1449_, v_a_1450_);
return v___x_1452_;
}
}
static lean_object* _init_l_Lake_Toml_trailingWs___closed__0(void){
_start:
{
lean_object* v___x_1453_; lean_object* v___x_1454_; 
v___x_1453_ = lean_alloc_closure((void*)(l_Lake_Toml_wsFn___boxed), 2, 0);
v___x_1454_ = l_Lake_Toml_trailing(v___x_1453_);
return v___x_1454_;
}
}
static lean_object* _init_l_Lake_Toml_trailingWs(void){
_start:
{
lean_object* v___x_1455_; 
v___x_1455_ = lean_obj_once(&l_Lake_Toml_trailingWs___closed__0, &l_Lake_Toml_trailingWs___closed__0_once, _init_l_Lake_Toml_trailingWs___closed__0);
return v___x_1455_;
}
}
static lean_object* _init_l_Lake_Toml_trailingSep___closed__1(void){
_start:
{
lean_object* v___x_1457_; lean_object* v___x_1458_; 
v___x_1457_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1458_ = l_Lake_Toml_trailing(v___x_1457_);
return v___x_1458_;
}
}
static lean_object* _init_l_Lake_Toml_trailingSep(void){
_start:
{
lean_object* v___x_1459_; 
v___x_1459_ = lean_obj_once(&l_Lake_Toml_trailingSep___closed__1, &l_Lake_Toml_trailingSep___closed__1_once, _init_l_Lake_Toml_trailingSep___closed__1);
return v___x_1459_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_unquotedKeyFn___lam__0(uint32_t v_c_1460_){
_start:
{
uint8_t v___y_1462_; uint8_t v___y_1468_; uint32_t v___x_1478_; uint8_t v___x_1479_; 
v___x_1478_ = 65;
v___x_1479_ = lean_uint32_dec_le(v___x_1478_, v_c_1460_);
if (v___x_1479_ == 0)
{
goto v___jp_1473_;
}
else
{
uint32_t v___x_1480_; uint8_t v___x_1481_; 
v___x_1480_ = 90;
v___x_1481_ = lean_uint32_dec_le(v_c_1460_, v___x_1480_);
if (v___x_1481_ == 0)
{
goto v___jp_1473_;
}
else
{
return v___x_1481_;
}
}
v___jp_1461_:
{
if (v___y_1462_ == 0)
{
uint32_t v___x_1463_; uint8_t v___x_1464_; 
v___x_1463_ = 95;
v___x_1464_ = lean_uint32_dec_eq(v_c_1460_, v___x_1463_);
if (v___x_1464_ == 0)
{
uint32_t v___x_1465_; uint8_t v___x_1466_; 
v___x_1465_ = 45;
v___x_1466_ = lean_uint32_dec_eq(v_c_1460_, v___x_1465_);
return v___x_1466_;
}
else
{
return v___x_1464_;
}
}
else
{
return v___y_1462_;
}
}
v___jp_1467_:
{
if (v___y_1468_ == 0)
{
uint32_t v___x_1469_; uint8_t v___x_1470_; 
v___x_1469_ = 48;
v___x_1470_ = lean_uint32_dec_le(v___x_1469_, v_c_1460_);
if (v___x_1470_ == 0)
{
v___y_1462_ = v___x_1470_;
goto v___jp_1461_;
}
else
{
uint32_t v___x_1471_; uint8_t v___x_1472_; 
v___x_1471_ = 57;
v___x_1472_ = lean_uint32_dec_le(v_c_1460_, v___x_1471_);
v___y_1462_ = v___x_1472_;
goto v___jp_1461_;
}
}
else
{
return v___y_1468_;
}
}
v___jp_1473_:
{
uint32_t v___x_1474_; uint8_t v___x_1475_; 
v___x_1474_ = 97;
v___x_1475_ = lean_uint32_dec_le(v___x_1474_, v_c_1460_);
if (v___x_1475_ == 0)
{
v___y_1468_ = v___x_1475_;
goto v___jp_1467_;
}
else
{
uint32_t v___x_1476_; uint8_t v___x_1477_; 
v___x_1476_ = 122;
v___x_1477_ = lean_uint32_dec_le(v_c_1460_, v___x_1476_);
v___y_1468_ = v___x_1477_;
goto v___jp_1467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn___lam__0___boxed(lean_object* v_c_1482_){
_start:
{
uint32_t v_c_boxed_1483_; uint8_t v_res_1484_; lean_object* v_r_1485_; 
v_c_boxed_1483_ = lean_unbox_uint32(v_c_1482_);
lean_dec(v_c_1482_);
v_res_1484_ = l_Lake_Toml_unquotedKeyFn___lam__0(v_c_boxed_1483_);
v_r_1485_ = lean_box(v_res_1484_);
return v_r_1485_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn(lean_object* v_a_1491_, lean_object* v_a_1492_){
_start:
{
lean_object* v___f_1493_; lean_object* v___x_1494_; lean_object* v___x_1495_; 
v___f_1493_ = ((lean_object*)(l_Lake_Toml_unquotedKeyFn___closed__0));
v___x_1494_ = ((lean_object*)(l_Lake_Toml_unquotedKeyFn___closed__2));
v___x_1495_ = l_Lake_Toml_takeWhile1Fn(v___f_1493_, v___x_1494_, v_a_1491_, v_a_1492_);
return v___x_1495_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn___boxed(lean_object* v_a_1496_, lean_object* v_a_1497_){
_start:
{
lean_object* v_res_1498_; 
v_res_1498_ = l_Lake_Toml_unquotedKeyFn(v_a_1496_, v_a_1497_);
lean_dec_ref(v_a_1496_);
return v_res_1498_;
}
}
static lean_object* _init_l_Lake_Toml_unquotedKey___closed__2(void){
_start:
{
uint8_t v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v___x_1504_ = 0;
v___x_1505_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1506_ = lean_alloc_closure((void*)(l_Lake_Toml_unquotedKeyFn___boxed), 2, 0);
v___x_1507_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__1));
v___x_1508_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__0));
v___x_1509_ = l_Lake_Toml_litWithAntiquot(v___x_1508_, v___x_1507_, v___x_1506_, v___x_1505_, v___x_1504_);
return v___x_1509_;
}
}
static lean_object* _init_l_Lake_Toml_unquotedKey(void){
_start:
{
lean_object* v___x_1510_; 
v___x_1510_ = lean_obj_once(&l_Lake_Toml_unquotedKey___closed__2, &l_Lake_Toml_unquotedKey___closed__2_once, _init_l_Lake_Toml_unquotedKey___closed__2);
return v___x_1510_;
}
}
static lean_object* _init_l_Lake_Toml_basicString___closed__2(void){
_start:
{
uint8_t v___x_1516_; lean_object* v___x_1517_; lean_object* v___x_1518_; lean_object* v___x_1519_; lean_object* v___x_1520_; lean_object* v___x_1521_; 
v___x_1516_ = 0;
v___x_1517_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1518_ = lean_alloc_closure((void*)(l_Lake_Toml_basicStringFn), 2, 0);
v___x_1519_ = ((lean_object*)(l_Lake_Toml_basicString___closed__1));
v___x_1520_ = ((lean_object*)(l_Lake_Toml_basicString___closed__0));
v___x_1521_ = l_Lake_Toml_litWithAntiquot(v___x_1520_, v___x_1519_, v___x_1518_, v___x_1517_, v___x_1516_);
return v___x_1521_;
}
}
static lean_object* _init_l_Lake_Toml_basicString(void){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = lean_obj_once(&l_Lake_Toml_basicString___closed__2, &l_Lake_Toml_basicString___closed__2_once, _init_l_Lake_Toml_basicString___closed__2);
return v___x_1522_;
}
}
static lean_object* _init_l_Lake_Toml_literalString___closed__2(void){
_start:
{
uint8_t v___x_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1528_ = 0;
v___x_1529_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1530_ = lean_alloc_closure((void*)(l_Lake_Toml_literalStringFn___boxed), 2, 0);
v___x_1531_ = ((lean_object*)(l_Lake_Toml_literalString___closed__1));
v___x_1532_ = ((lean_object*)(l_Lake_Toml_literalString___closed__0));
v___x_1533_ = l_Lake_Toml_litWithAntiquot(v___x_1532_, v___x_1531_, v___x_1530_, v___x_1529_, v___x_1528_);
return v___x_1533_;
}
}
static lean_object* _init_l_Lake_Toml_literalString(void){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = lean_obj_once(&l_Lake_Toml_literalString___closed__2, &l_Lake_Toml_literalString___closed__2_once, _init_l_Lake_Toml_literalString___closed__2);
return v___x_1534_;
}
}
static lean_object* _init_l_Lake_Toml_mlBasicString___closed__2(void){
_start:
{
uint8_t v___x_1540_; lean_object* v___x_1541_; lean_object* v___x_1542_; lean_object* v___x_1543_; lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1540_ = 0;
v___x_1541_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1542_ = lean_alloc_closure((void*)(l_Lake_Toml_mlBasicStringFn), 2, 0);
v___x_1543_ = ((lean_object*)(l_Lake_Toml_mlBasicString___closed__1));
v___x_1544_ = ((lean_object*)(l_Lake_Toml_mlBasicString___closed__0));
v___x_1545_ = l_Lake_Toml_litWithAntiquot(v___x_1544_, v___x_1543_, v___x_1542_, v___x_1541_, v___x_1540_);
return v___x_1545_;
}
}
static lean_object* _init_l_Lake_Toml_mlBasicString(void){
_start:
{
lean_object* v___x_1546_; 
v___x_1546_ = lean_obj_once(&l_Lake_Toml_mlBasicString___closed__2, &l_Lake_Toml_mlBasicString___closed__2_once, _init_l_Lake_Toml_mlBasicString___closed__2);
return v___x_1546_;
}
}
static lean_object* _init_l_Lake_Toml_mlLiteralString___closed__2(void){
_start:
{
uint8_t v___x_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1555_; lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1552_ = 0;
v___x_1553_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1554_ = lean_alloc_closure((void*)(l_Lake_Toml_mlLiteralStringFn), 2, 0);
v___x_1555_ = ((lean_object*)(l_Lake_Toml_mlLiteralString___closed__1));
v___x_1556_ = ((lean_object*)(l_Lake_Toml_mlLiteralString___closed__0));
v___x_1557_ = l_Lake_Toml_litWithAntiquot(v___x_1556_, v___x_1555_, v___x_1554_, v___x_1553_, v___x_1552_);
return v___x_1557_;
}
}
static lean_object* _init_l_Lake_Toml_mlLiteralString(void){
_start:
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_obj_once(&l_Lake_Toml_mlLiteralString___closed__2, &l_Lake_Toml_mlLiteralString___closed__2_once, _init_l_Lake_Toml_mlLiteralString___closed__2);
return v___x_1558_;
}
}
static lean_object* _init_l_Lake_Toml_quotedKey___closed__0(void){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; lean_object* v___x_1561_; 
v___x_1559_ = l_Lake_Toml_literalString;
v___x_1560_ = l_Lake_Toml_basicString;
v___x_1561_ = l_Lean_Parser_orelse(v___x_1560_, v___x_1559_);
return v___x_1561_;
}
}
static lean_object* _init_l_Lake_Toml_quotedKey(void){
_start:
{
lean_object* v___x_1562_; 
v___x_1562_ = lean_obj_once(&l_Lake_Toml_quotedKey___closed__0, &l_Lake_Toml_quotedKey___closed__0_once, _init_l_Lake_Toml_quotedKey___closed__0);
return v___x_1562_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey___closed__2(void){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1570_; 
v___x_1568_ = l_Lake_Toml_quotedKey;
v___x_1569_ = l_Lake_Toml_unquotedKey;
v___x_1570_ = l_Lean_Parser_orelse(v___x_1569_, v___x_1568_);
return v___x_1570_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey___closed__3(void){
_start:
{
uint8_t v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1575_; 
v___x_1571_ = 1;
v___x_1572_ = lean_obj_once(&l_Lake_Toml_simpleKey___closed__2, &l_Lake_Toml_simpleKey___closed__2_once, _init_l_Lake_Toml_simpleKey___closed__2);
v___x_1573_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__1));
v___x_1574_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__0));
v___x_1575_ = l_Lean_Parser_nodeWithAntiquot(v___x_1574_, v___x_1573_, v___x_1572_, v___x_1571_);
return v___x_1575_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey(void){
_start:
{
lean_object* v___x_1576_; 
v___x_1576_ = lean_obj_once(&l_Lake_Toml_simpleKey___closed__3, &l_Lake_Toml_simpleKey___closed__3_once, _init_l_Lake_Toml_simpleKey___closed__3);
return v___x_1576_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__4(void){
_start:
{
uint32_t v___x_1586_; lean_object* v___x_1587_; lean_object* v___x_1588_; 
v___x_1586_ = 46;
v___x_1587_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_1588_ = lean_string_push(v___x_1587_, v___x_1586_);
return v___x_1588_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__5(void){
_start:
{
lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1589_ = lean_obj_once(&l_Lake_Toml_key___closed__4, &l_Lake_Toml_key___closed__4_once, _init_l_Lake_Toml_key___closed__4);
v___x_1590_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1591_ = lean_string_append(v___x_1590_, v___x_1589_);
return v___x_1591_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__6(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; lean_object* v___x_1594_; 
v___x_1592_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1593_ = lean_obj_once(&l_Lake_Toml_key___closed__5, &l_Lake_Toml_key___closed__5_once, _init_l_Lake_Toml_key___closed__5);
v___x_1594_ = lean_string_append(v___x_1593_, v___x_1592_);
return v___x_1594_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__7(void){
_start:
{
lean_object* v___x_1595_; lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1595_ = lean_box(0);
v___x_1596_ = lean_obj_once(&l_Lake_Toml_key___closed__6, &l_Lake_Toml_key___closed__6_once, _init_l_Lake_Toml_key___closed__6);
v___x_1597_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1597_, 0, v___x_1596_);
lean_ctor_set(v___x_1597_, 1, v___x_1595_);
return v___x_1597_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__8(void){
_start:
{
lean_object* v___x_1598_; lean_object* v___x_1599_; uint32_t v___x_1600_; lean_object* v___x_1601_; 
v___x_1598_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1599_ = lean_obj_once(&l_Lake_Toml_key___closed__7, &l_Lake_Toml_key___closed__7_once, _init_l_Lake_Toml_key___closed__7);
v___x_1600_ = 46;
v___x_1601_ = l_Lake_Toml_chAtom(v___x_1600_, v___x_1599_, v___x_1598_);
return v___x_1601_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__9(void){
_start:
{
lean_object* v___x_1602_; lean_object* v___x_1603_; lean_object* v___x_1604_; 
v___x_1602_ = l_Lake_Toml_trailingWs;
v___x_1603_ = lean_obj_once(&l_Lake_Toml_key___closed__8, &l_Lake_Toml_key___closed__8_once, _init_l_Lake_Toml_key___closed__8);
v___x_1604_ = l_Lean_Parser_andthen(v___x_1603_, v___x_1602_);
return v___x_1604_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__10(void){
_start:
{
lean_object* v___x_1605_; lean_object* v___x_1606_; lean_object* v___x_1607_; 
v___x_1605_ = lean_obj_once(&l_Lake_Toml_key___closed__9, &l_Lake_Toml_key___closed__9_once, _init_l_Lake_Toml_key___closed__9);
v___x_1606_ = l_Lake_Toml_trailingWs;
v___x_1607_ = l_Lean_Parser_andthen(v___x_1606_, v___x_1605_);
return v___x_1607_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__11(void){
_start:
{
uint8_t v___x_1608_; lean_object* v___x_1609_; lean_object* v___x_1610_; lean_object* v___x_1611_; lean_object* v___x_1612_; 
v___x_1608_ = 0;
v___x_1609_ = lean_obj_once(&l_Lake_Toml_key___closed__10, &l_Lake_Toml_key___closed__10_once, _init_l_Lake_Toml_key___closed__10);
v___x_1610_ = ((lean_object*)(l_Lake_Toml_key___closed__3));
v___x_1611_ = l_Lake_Toml_simpleKey;
v___x_1612_ = l_Lean_Parser_sepBy1(v___x_1611_, v___x_1610_, v___x_1609_, v___x_1608_);
return v___x_1612_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__12(void){
_start:
{
lean_object* v___x_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; 
v___x_1613_ = lean_obj_once(&l_Lake_Toml_key___closed__11, &l_Lake_Toml_key___closed__11_once, _init_l_Lake_Toml_key___closed__11);
v___x_1614_ = ((lean_object*)(l_Lake_Toml_key___closed__2));
v___x_1615_ = l_Lean_Parser_setExpected(v___x_1614_, v___x_1613_);
return v___x_1615_;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__13(void){
_start:
{
uint8_t v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1618_; lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1616_ = 1;
v___x_1617_ = lean_obj_once(&l_Lake_Toml_key___closed__12, &l_Lake_Toml_key___closed__12_once, _init_l_Lake_Toml_key___closed__12);
v___x_1618_ = ((lean_object*)(l_Lake_Toml_key___closed__1));
v___x_1619_ = ((lean_object*)(l_Lake_Toml_key___closed__0));
v___x_1620_ = l_Lean_Parser_nodeWithAntiquot(v___x_1619_, v___x_1618_, v___x_1617_, v___x_1616_);
return v___x_1620_;
}
}
static lean_object* _init_l_Lake_Toml_key(void){
_start:
{
lean_object* v___x_1621_; 
v___x_1621_ = lean_obj_once(&l_Lake_Toml_key___closed__13, &l_Lake_Toml_key___closed__13_once, _init_l_Lake_Toml_key___closed__13);
return v___x_1621_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__4(void){
_start:
{
lean_object* v___x_1631_; lean_object* v___x_1632_; uint32_t v___x_1633_; lean_object* v___x_1634_; 
v___x_1631_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1632_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__3));
v___x_1633_ = 91;
v___x_1634_ = l_Lake_Toml_chAtom(v___x_1633_, v___x_1632_, v___x_1631_);
return v___x_1634_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__5(void){
_start:
{
uint32_t v___x_1635_; lean_object* v___x_1636_; lean_object* v___x_1637_; 
v___x_1635_ = 91;
v___x_1636_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_1637_ = lean_string_push(v___x_1636_, v___x_1635_);
return v___x_1637_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__6(void){
_start:
{
lean_object* v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1640_; 
v___x_1638_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__5, &l_Lake_Toml_stdTable___closed__5_once, _init_l_Lake_Toml_stdTable___closed__5);
v___x_1639_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1640_ = lean_string_append(v___x_1639_, v___x_1638_);
return v___x_1640_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__7(void){
_start:
{
lean_object* v___x_1641_; lean_object* v___x_1642_; lean_object* v___x_1643_; 
v___x_1641_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1642_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__6, &l_Lake_Toml_stdTable___closed__6_once, _init_l_Lake_Toml_stdTable___closed__6);
v___x_1643_ = lean_string_append(v___x_1642_, v___x_1641_);
return v___x_1643_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__8(void){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v___x_1646_; 
v___x_1644_ = lean_box(0);
v___x_1645_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__7, &l_Lake_Toml_stdTable___closed__7_once, _init_l_Lake_Toml_stdTable___closed__7);
v___x_1646_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1646_, 0, v___x_1645_);
lean_ctor_set(v___x_1646_, 1, v___x_1644_);
return v___x_1646_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__9(void){
_start:
{
lean_object* v___x_1647_; lean_object* v___x_1648_; uint32_t v___x_1649_; lean_object* v___x_1650_; 
v___x_1647_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1648_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__8, &l_Lake_Toml_stdTable___closed__8_once, _init_l_Lake_Toml_stdTable___closed__8);
v___x_1649_ = 91;
v___x_1650_ = l_Lake_Toml_chAtom(v___x_1649_, v___x_1648_, v___x_1647_);
return v___x_1650_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__11(void){
_start:
{
lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1654_; 
v___x_1652_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__10));
v___x_1653_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__9, &l_Lake_Toml_stdTable___closed__9_once, _init_l_Lake_Toml_stdTable___closed__9);
v___x_1654_ = l_Lean_Parser_notFollowedBy(v___x_1653_, v___x_1652_);
return v___x_1654_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__12(void){
_start:
{
lean_object* v___x_1655_; lean_object* v___x_1656_; lean_object* v___x_1657_; 
v___x_1655_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__11, &l_Lake_Toml_stdTable___closed__11_once, _init_l_Lake_Toml_stdTable___closed__11);
v___x_1656_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__4, &l_Lake_Toml_stdTable___closed__4_once, _init_l_Lake_Toml_stdTable___closed__4);
v___x_1657_ = l_Lean_Parser_andthen(v___x_1656_, v___x_1655_);
return v___x_1657_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__13(void){
_start:
{
lean_object* v___x_1658_; lean_object* v___x_1659_; 
v___x_1658_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__12, &l_Lake_Toml_stdTable___closed__12_once, _init_l_Lake_Toml_stdTable___closed__12);
v___x_1659_ = l_Lean_Parser_atomic(v___x_1658_);
return v___x_1659_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__14(void){
_start:
{
uint32_t v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; 
v___x_1660_ = 93;
v___x_1661_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_1662_ = lean_string_push(v___x_1661_, v___x_1660_);
return v___x_1662_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__15(void){
_start:
{
lean_object* v___x_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1663_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__14, &l_Lake_Toml_stdTable___closed__14_once, _init_l_Lake_Toml_stdTable___closed__14);
v___x_1664_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1665_ = lean_string_append(v___x_1664_, v___x_1663_);
return v___x_1665_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__16(void){
_start:
{
lean_object* v___x_1666_; lean_object* v___x_1667_; lean_object* v___x_1668_; 
v___x_1666_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1667_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__15, &l_Lake_Toml_stdTable___closed__15_once, _init_l_Lake_Toml_stdTable___closed__15);
v___x_1668_ = lean_string_append(v___x_1667_, v___x_1666_);
return v___x_1668_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__17(void){
_start:
{
lean_object* v___x_1669_; lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1669_ = lean_box(0);
v___x_1670_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__16, &l_Lake_Toml_stdTable___closed__16_once, _init_l_Lake_Toml_stdTable___closed__16);
v___x_1671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
lean_ctor_set(v___x_1671_, 1, v___x_1669_);
return v___x_1671_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__18(void){
_start:
{
lean_object* v___x_1672_; lean_object* v___x_1673_; uint32_t v___x_1674_; lean_object* v___x_1675_; 
v___x_1672_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1673_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__17, &l_Lake_Toml_stdTable___closed__17_once, _init_l_Lake_Toml_stdTable___closed__17);
v___x_1674_ = 93;
v___x_1675_ = l_Lake_Toml_chAtom(v___x_1674_, v___x_1673_, v___x_1672_);
return v___x_1675_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__19(void){
_start:
{
lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1678_; 
v___x_1676_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__18, &l_Lake_Toml_stdTable___closed__18_once, _init_l_Lake_Toml_stdTable___closed__18);
v___x_1677_ = l_Lake_Toml_trailingWs;
v___x_1678_ = l_Lean_Parser_andthen(v___x_1677_, v___x_1676_);
return v___x_1678_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__20(void){
_start:
{
lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v___x_1679_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__19, &l_Lake_Toml_stdTable___closed__19_once, _init_l_Lake_Toml_stdTable___closed__19);
v___x_1680_ = l_Lake_Toml_key;
v___x_1681_ = l_Lean_Parser_andthen(v___x_1680_, v___x_1679_);
return v___x_1681_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__21(void){
_start:
{
lean_object* v___x_1682_; lean_object* v___x_1683_; lean_object* v___x_1684_; 
v___x_1682_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__20, &l_Lake_Toml_stdTable___closed__20_once, _init_l_Lake_Toml_stdTable___closed__20);
v___x_1683_ = l_Lake_Toml_trailingWs;
v___x_1684_ = l_Lean_Parser_andthen(v___x_1683_, v___x_1682_);
return v___x_1684_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__22(void){
_start:
{
lean_object* v___x_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v___x_1685_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__21, &l_Lake_Toml_stdTable___closed__21_once, _init_l_Lake_Toml_stdTable___closed__21);
v___x_1686_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__13, &l_Lake_Toml_stdTable___closed__13_once, _init_l_Lake_Toml_stdTable___closed__13);
v___x_1687_ = l_Lean_Parser_andthen(v___x_1686_, v___x_1685_);
return v___x_1687_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__23(void){
_start:
{
uint8_t v___x_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v___x_1688_ = 0;
v___x_1689_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__22, &l_Lake_Toml_stdTable___closed__22_once, _init_l_Lake_Toml_stdTable___closed__22);
v___x_1690_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__1));
v___x_1691_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__0));
v___x_1692_ = l_Lean_Parser_nodeWithAntiquot(v___x_1691_, v___x_1690_, v___x_1689_, v___x_1688_);
return v___x_1692_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable(void){
_start:
{
lean_object* v___x_1693_; 
v___x_1693_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__23, &l_Lake_Toml_stdTable___closed__23_once, _init_l_Lake_Toml_stdTable___closed__23);
return v___x_1693_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__2(void){
_start:
{
lean_object* v___x_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
v___x_1699_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__9, &l_Lake_Toml_stdTable___closed__9_once, _init_l_Lake_Toml_stdTable___closed__9);
v___x_1700_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__4, &l_Lake_Toml_stdTable___closed__4_once, _init_l_Lake_Toml_stdTable___closed__4);
v___x_1701_ = l_Lean_Parser_andthen(v___x_1700_, v___x_1699_);
return v___x_1701_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__3(void){
_start:
{
lean_object* v___x_1702_; lean_object* v___x_1703_; 
v___x_1702_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__2, &l_Lake_Toml_arrayTable___closed__2_once, _init_l_Lake_Toml_arrayTable___closed__2);
v___x_1703_ = l_Lean_Parser_atomic(v___x_1702_);
return v___x_1703_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__4(void){
_start:
{
lean_object* v___x_1704_; lean_object* v___x_1705_; 
v___x_1704_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__18, &l_Lake_Toml_stdTable___closed__18_once, _init_l_Lake_Toml_stdTable___closed__18);
v___x_1705_ = l_Lean_Parser_andthen(v___x_1704_, v___x_1704_);
return v___x_1705_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__5(void){
_start:
{
lean_object* v___x_1706_; lean_object* v___x_1707_; lean_object* v___x_1708_; 
v___x_1706_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__4, &l_Lake_Toml_arrayTable___closed__4_once, _init_l_Lake_Toml_arrayTable___closed__4);
v___x_1707_ = l_Lake_Toml_trailingWs;
v___x_1708_ = l_Lean_Parser_andthen(v___x_1707_, v___x_1706_);
return v___x_1708_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__6(void){
_start:
{
lean_object* v___x_1709_; lean_object* v___x_1710_; lean_object* v___x_1711_; 
v___x_1709_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__5, &l_Lake_Toml_arrayTable___closed__5_once, _init_l_Lake_Toml_arrayTable___closed__5);
v___x_1710_ = l_Lake_Toml_key;
v___x_1711_ = l_Lean_Parser_andthen(v___x_1710_, v___x_1709_);
return v___x_1711_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__7(void){
_start:
{
lean_object* v___x_1712_; lean_object* v___x_1713_; lean_object* v___x_1714_; 
v___x_1712_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__6, &l_Lake_Toml_arrayTable___closed__6_once, _init_l_Lake_Toml_arrayTable___closed__6);
v___x_1713_ = l_Lake_Toml_trailingWs;
v___x_1714_ = l_Lean_Parser_andthen(v___x_1713_, v___x_1712_);
return v___x_1714_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__8(void){
_start:
{
lean_object* v___x_1715_; lean_object* v___x_1716_; lean_object* v___x_1717_; 
v___x_1715_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__7, &l_Lake_Toml_arrayTable___closed__7_once, _init_l_Lake_Toml_arrayTable___closed__7);
v___x_1716_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__3, &l_Lake_Toml_arrayTable___closed__3_once, _init_l_Lake_Toml_arrayTable___closed__3);
v___x_1717_ = l_Lean_Parser_andthen(v___x_1716_, v___x_1715_);
return v___x_1717_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__9(void){
_start:
{
uint8_t v___x_1718_; lean_object* v___x_1719_; lean_object* v___x_1720_; lean_object* v___x_1721_; lean_object* v___x_1722_; 
v___x_1718_ = 0;
v___x_1719_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__8, &l_Lake_Toml_arrayTable___closed__8_once, _init_l_Lake_Toml_arrayTable___closed__8);
v___x_1720_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__1));
v___x_1721_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__0));
v___x_1722_ = l_Lean_Parser_nodeWithAntiquot(v___x_1721_, v___x_1720_, v___x_1719_, v___x_1718_);
return v___x_1722_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable(void){
_start:
{
lean_object* v___x_1723_; 
v___x_1723_ = lean_obj_once(&l_Lake_Toml_arrayTable___closed__9, &l_Lake_Toml_arrayTable___closed__9_once, _init_l_Lake_Toml_arrayTable___closed__9);
return v___x_1723_;
}
}
static lean_object* _init_l_Lake_Toml_table___closed__0(void){
_start:
{
lean_object* v___x_1724_; lean_object* v___x_1725_; lean_object* v___x_1726_; 
v___x_1724_ = l_Lake_Toml_arrayTable;
v___x_1725_ = l_Lake_Toml_stdTable;
v___x_1726_ = l_Lean_Parser_orelse(v___x_1725_, v___x_1724_);
return v___x_1726_;
}
}
static lean_object* _init_l_Lake_Toml_table(void){
_start:
{
lean_object* v___x_1727_; 
v___x_1727_ = lean_obj_once(&l_Lake_Toml_table___closed__0, &l_Lake_Toml_table___closed__0_once, _init_l_Lake_Toml_table___closed__0);
return v___x_1727_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2(void){
_start:
{
uint32_t v___x_1733_; lean_object* v___x_1734_; lean_object* v___x_1735_; 
v___x_1733_ = 61;
v___x_1734_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_1735_ = lean_string_push(v___x_1734_, v___x_1733_);
return v___x_1735_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3(void){
_start:
{
lean_object* v___x_1736_; lean_object* v___x_1737_; lean_object* v___x_1738_; 
v___x_1736_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2);
v___x_1737_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1738_ = lean_string_append(v___x_1737_, v___x_1736_);
return v___x_1738_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4(void){
_start:
{
lean_object* v___x_1739_; lean_object* v___x_1740_; lean_object* v___x_1741_; 
v___x_1739_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1740_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3);
v___x_1741_ = lean_string_append(v___x_1740_, v___x_1739_);
return v___x_1741_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5(void){
_start:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1742_ = lean_box(0);
v___x_1743_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4);
v___x_1744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
lean_ctor_set(v___x_1744_, 1, v___x_1742_);
return v___x_1744_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6(void){
_start:
{
lean_object* v___x_1745_; lean_object* v___x_1746_; uint32_t v___x_1747_; lean_object* v___x_1748_; 
v___x_1745_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1746_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5);
v___x_1747_ = 61;
v___x_1748_ = l_Lake_Toml_chAtom(v___x_1747_, v___x_1746_, v___x_1745_);
return v___x_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(lean_object* v_val_1749_){
_start:
{
lean_object* v___x_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; lean_object* v___x_1753_; lean_object* v___x_1754_; lean_object* v___x_1755_; lean_object* v___x_1756_; lean_object* v___x_1757_; lean_object* v___x_1758_; uint8_t v___x_1759_; lean_object* v___x_1760_; 
v___x_1750_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0));
v___x_1751_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1));
v___x_1752_ = l_Lake_Toml_key;
v___x_1753_ = l_Lake_Toml_trailingWs;
v___x_1754_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6);
v___x_1755_ = l_Lean_Parser_andthen(v___x_1753_, v_val_1749_);
v___x_1756_ = l_Lean_Parser_andthen(v___x_1754_, v___x_1755_);
v___x_1757_ = l_Lean_Parser_andthen(v___x_1753_, v___x_1756_);
v___x_1758_ = l_Lean_Parser_andthen(v___x_1752_, v___x_1757_);
v___x_1759_ = 1;
v___x_1760_ = l_Lean_Parser_nodeWithAntiquot(v___x_1750_, v___x_1751_, v___x_1758_, v___x_1759_);
return v___x_1760_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2(void){
_start:
{
uint8_t v___x_1766_; lean_object* v___x_1767_; lean_object* v___x_1768_; lean_object* v___x_1769_; 
v___x_1766_ = 1;
v___x_1767_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1));
v___x_1768_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0));
v___x_1769_ = l_Lean_Parser_mkAntiquot(v___x_1768_, v___x_1767_, v___x_1766_, v___x_1766_);
return v___x_1769_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(lean_object* v_val_1770_){
_start:
{
lean_object* v___x_1771_; lean_object* v___x_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v___x_1771_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2, &l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2);
v___x_1772_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(v_val_1770_);
v___x_1773_ = l_Lake_Toml_table;
v___x_1774_ = l_Lean_Parser_orelse(v___x_1772_, v___x_1773_);
v___x_1775_ = l_Lean_Parser_withAntiquot(v___x_1771_, v___x_1774_);
return v___x_1775_;
}
}
static lean_object* _init_l_Lake_Toml_header___closed__2(void){
_start:
{
uint8_t v___x_1781_; lean_object* v___x_1782_; lean_object* v___x_1783_; lean_object* v___x_1784_; lean_object* v___x_1785_; lean_object* v___x_1786_; 
v___x_1781_ = 0;
v___x_1782_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1783_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1784_ = ((lean_object*)(l_Lake_Toml_header___closed__1));
v___x_1785_ = ((lean_object*)(l_Lake_Toml_header___closed__0));
v___x_1786_ = l_Lake_Toml_litWithAntiquot(v___x_1785_, v___x_1784_, v___x_1783_, v___x_1782_, v___x_1781_);
return v___x_1786_;
}
}
static lean_object* _init_l_Lake_Toml_header(void){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_obj_once(&l_Lake_Toml_header___closed__2, &l_Lake_Toml_header___closed__2_once, _init_l_Lake_Toml_header___closed__2);
return v___x_1787_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5(void){
_start:
{
lean_object* v___x_1797_; lean_object* v___x_1798_; 
v___x_1797_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__4));
v___x_1798_ = l_Lean_Parser_symbol(v___x_1797_);
return v___x_1798_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7(void){
_start:
{
lean_object* v___x_1800_; lean_object* v___x_1801_; 
v___x_1800_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__6));
v___x_1801_ = l_Lean_Parser_checkLinebreakBefore(v___x_1800_);
return v___x_1801_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8(void){
_start:
{
lean_object* v___x_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; 
v___x_1802_ = l_Lean_Parser_pushNone;
v___x_1803_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7, &l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7);
v___x_1804_ = l_Lean_Parser_andthen(v___x_1803_, v___x_1802_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore(lean_object* v_val_1805_){
_start:
{
lean_object* v___x_1806_; lean_object* v___x_1807_; lean_object* v___x_1808_; lean_object* v___x_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; uint8_t v___x_1812_; lean_object* v___x_1813_; lean_object* v___x_1814_; lean_object* v_p_1815_; lean_object* v___x_1816_; lean_object* v___x_1817_; lean_object* v___x_1818_; lean_object* v___x_1819_; 
v___x_1806_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0));
v___x_1807_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1));
v___x_1808_ = l_Lake_Toml_header;
v___x_1809_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(v_val_1805_);
v___x_1810_ = l_Lake_Toml_trailingSep;
v___x_1811_ = l_Lean_Parser_andthen(v___x_1809_, v___x_1810_);
v___x_1812_ = 1;
v___x_1813_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__3));
v___x_1814_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5);
v_p_1815_ = l_Lean_Parser_withAntiquotSpliceAndSuffix(v___x_1813_, v___x_1811_, v___x_1814_);
v___x_1816_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8, &l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8);
v___x_1817_ = l_Lean_Parser_sepByNoAntiquot(v_p_1815_, v___x_1816_, v___x_1812_);
v___x_1818_ = l_Lean_Parser_andthen(v___x_1808_, v___x_1817_);
v___x_1819_ = l_Lean_Parser_nodeWithAntiquot(v___x_1806_, v___x_1807_, v___x_1818_, v___x_1812_);
return v___x_1819_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4(void){
_start:
{
lean_object* v___x_1829_; lean_object* v___x_1830_; uint32_t v___x_1831_; lean_object* v___x_1832_; 
v___x_1829_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1830_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__3));
v___x_1831_ = 123;
v___x_1832_ = l_Lake_Toml_chAtom(v___x_1831_, v___x_1830_, v___x_1829_);
return v___x_1832_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6(void){
_start:
{
uint32_t v___x_1834_; lean_object* v___x_1835_; lean_object* v___x_1836_; 
v___x_1834_ = 44;
v___x_1835_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_1836_ = lean_string_push(v___x_1835_, v___x_1834_);
return v___x_1836_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7(void){
_start:
{
lean_object* v___x_1837_; lean_object* v___x_1838_; lean_object* v___x_1839_; 
v___x_1837_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6);
v___x_1838_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1839_ = lean_string_append(v___x_1838_, v___x_1837_);
return v___x_1839_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8(void){
_start:
{
lean_object* v___x_1840_; lean_object* v___x_1841_; lean_object* v___x_1842_; 
v___x_1840_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1841_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7);
v___x_1842_ = lean_string_append(v___x_1841_, v___x_1840_);
return v___x_1842_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9(void){
_start:
{
lean_object* v___x_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; 
v___x_1843_ = lean_box(0);
v___x_1844_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8);
v___x_1845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1845_, 0, v___x_1844_);
lean_ctor_set(v___x_1845_, 1, v___x_1843_);
return v___x_1845_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10(void){
_start:
{
lean_object* v___x_1846_; lean_object* v___x_1847_; uint32_t v___x_1848_; lean_object* v___x_1849_; 
v___x_1846_ = lean_alloc_closure((void*)(l_Lake_Toml_wsFn___boxed), 2, 0);
v___x_1847_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9);
v___x_1848_ = 44;
v___x_1849_ = l_Lake_Toml_chAtom(v___x_1848_, v___x_1847_, v___x_1846_);
return v___x_1849_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11(void){
_start:
{
uint32_t v___x_1850_; lean_object* v___x_1851_; lean_object* v___x_1852_; 
v___x_1850_ = 125;
v___x_1851_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3));
v___x_1852_ = lean_string_push(v___x_1851_, v___x_1850_);
return v___x_1852_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12(void){
_start:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; lean_object* v___x_1855_; 
v___x_1853_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11);
v___x_1854_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1855_ = lean_string_append(v___x_1854_, v___x_1853_);
return v___x_1855_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13(void){
_start:
{
lean_object* v___x_1856_; lean_object* v___x_1857_; lean_object* v___x_1858_; 
v___x_1856_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2));
v___x_1857_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12);
v___x_1858_ = lean_string_append(v___x_1857_, v___x_1856_);
return v___x_1858_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14(void){
_start:
{
lean_object* v___x_1859_; lean_object* v___x_1860_; lean_object* v___x_1861_; 
v___x_1859_ = lean_box(0);
v___x_1860_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13);
v___x_1861_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1861_, 0, v___x_1860_);
lean_ctor_set(v___x_1861_, 1, v___x_1859_);
return v___x_1861_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15(void){
_start:
{
lean_object* v___x_1862_; lean_object* v___x_1863_; uint32_t v___x_1864_; lean_object* v___x_1865_; 
v___x_1862_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1863_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14);
v___x_1864_ = 125;
v___x_1865_ = l_Lake_Toml_chAtom(v___x_1864_, v___x_1863_, v___x_1862_);
return v___x_1865_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(lean_object* v_val_1866_){
_start:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; uint8_t v___x_1875_; lean_object* v___x_1876_; lean_object* v___x_1877_; lean_object* v___x_1878_; lean_object* v___x_1879_; lean_object* v___x_1880_; 
v___x_1867_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0));
v___x_1868_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1));
v___x_1869_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4);
v___x_1870_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(v_val_1866_);
v___x_1871_ = l_Lake_Toml_trailingWs;
v___x_1872_ = l_Lean_Parser_andthen(v___x_1870_, v___x_1871_);
v___x_1873_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5));
v___x_1874_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10);
v___x_1875_ = 0;
v___x_1876_ = l_Lean_Parser_sepBy(v___x_1872_, v___x_1873_, v___x_1874_, v___x_1875_);
v___x_1877_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15);
v___x_1878_ = l_Lean_Parser_andthen(v___x_1876_, v___x_1877_);
v___x_1879_ = l_Lean_Parser_andthen(v___x_1869_, v___x_1878_);
v___x_1880_ = l_Lean_Parser_nodeWithAntiquot(v___x_1867_, v___x_1868_, v___x_1879_, v___x_1875_);
return v___x_1880_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3(void){
_start:
{
lean_object* v___x_1889_; lean_object* v___x_1890_; uint32_t v___x_1891_; lean_object* v___x_1892_; 
v___x_1889_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1890_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__2));
v___x_1891_ = 91;
v___x_1892_ = l_Lake_Toml_chAtom(v___x_1891_, v___x_1890_, v___x_1889_);
return v___x_1892_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4(void){
_start:
{
lean_object* v___x_1893_; lean_object* v___x_1894_; uint32_t v___x_1895_; lean_object* v___x_1896_; 
v___x_1893_ = ((lean_object*)(l_Lake_Toml_trailingSep___closed__0));
v___x_1894_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9, &l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9);
v___x_1895_ = 44;
v___x_1896_ = l_Lake_Toml_chAtom(v___x_1895_, v___x_1894_, v___x_1893_);
return v___x_1896_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(lean_object* v_val_1897_){
_start:
{
lean_object* v___x_1898_; lean_object* v___x_1899_; lean_object* v___x_1900_; lean_object* v___x_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; uint8_t v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; lean_object* v___x_1908_; lean_object* v___x_1909_; uint8_t v___x_1910_; lean_object* v___x_1911_; 
v___x_1898_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0));
v___x_1899_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1));
v___x_1900_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3, &l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3);
v___x_1901_ = l_Lake_Toml_trailingSep;
v___x_1902_ = l_Lean_Parser_andthen(v_val_1897_, v___x_1901_);
v___x_1903_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5));
v___x_1904_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4, &l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4);
v___x_1905_ = 1;
v___x_1906_ = l_Lean_Parser_sepBy(v___x_1902_, v___x_1903_, v___x_1904_, v___x_1905_);
v___x_1907_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__18, &l_Lake_Toml_stdTable___closed__18_once, _init_l_Lake_Toml_stdTable___closed__18);
v___x_1908_ = l_Lean_Parser_andthen(v___x_1906_, v___x_1907_);
v___x_1909_ = l_Lean_Parser_andthen(v___x_1900_, v___x_1908_);
v___x_1910_ = 0;
v___x_1911_ = l_Lean_Parser_nodeWithAntiquot(v___x_1898_, v___x_1899_, v___x_1909_, v___x_1910_);
return v___x_1911_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__3(void){
_start:
{
lean_object* v___x_1920_; lean_object* v___x_1921_; lean_object* v___x_1922_; 
v___x_1920_ = l_Lake_Toml_literalString;
v___x_1921_ = l_Lake_Toml_mlLiteralString;
v___x_1922_ = l_Lean_Parser_orelse(v___x_1921_, v___x_1920_);
return v___x_1922_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__4(void){
_start:
{
lean_object* v___x_1923_; lean_object* v___x_1924_; lean_object* v___x_1925_; 
v___x_1923_ = lean_obj_once(&l_Lake_Toml_string___closed__3, &l_Lake_Toml_string___closed__3_once, _init_l_Lake_Toml_string___closed__3);
v___x_1924_ = l_Lake_Toml_basicString;
v___x_1925_ = l_Lean_Parser_orelse(v___x_1924_, v___x_1923_);
return v___x_1925_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__5(void){
_start:
{
lean_object* v___x_1926_; lean_object* v___x_1927_; lean_object* v___x_1928_; 
v___x_1926_ = lean_obj_once(&l_Lake_Toml_string___closed__4, &l_Lake_Toml_string___closed__4_once, _init_l_Lake_Toml_string___closed__4);
v___x_1927_ = l_Lake_Toml_mlBasicString;
v___x_1928_ = l_Lean_Parser_orelse(v___x_1927_, v___x_1926_);
return v___x_1928_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__6(void){
_start:
{
lean_object* v___x_1929_; lean_object* v___x_1930_; lean_object* v___x_1931_; 
v___x_1929_ = lean_obj_once(&l_Lake_Toml_string___closed__5, &l_Lake_Toml_string___closed__5_once, _init_l_Lake_Toml_string___closed__5);
v___x_1930_ = ((lean_object*)(l_Lake_Toml_string___closed__2));
v___x_1931_ = l_Lean_Parser_setExpected(v___x_1930_, v___x_1929_);
return v___x_1931_;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__7(void){
_start:
{
uint8_t v___x_1932_; lean_object* v___x_1933_; lean_object* v___x_1934_; lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1932_ = 0;
v___x_1933_ = lean_obj_once(&l_Lake_Toml_string___closed__6, &l_Lake_Toml_string___closed__6_once, _init_l_Lake_Toml_string___closed__6);
v___x_1934_ = ((lean_object*)(l_Lake_Toml_string___closed__1));
v___x_1935_ = ((lean_object*)(l_Lake_Toml_string___closed__0));
v___x_1936_ = l_Lean_Parser_nodeWithAntiquot(v___x_1935_, v___x_1934_, v___x_1933_, v___x_1932_);
return v___x_1936_;
}
}
static lean_object* _init_l_Lake_Toml_string(void){
_start:
{
lean_object* v___x_1937_; 
v___x_1937_ = lean_obj_once(&l_Lake_Toml_string___closed__7, &l_Lake_Toml_string___closed__7_once, _init_l_Lake_Toml_string___closed__7);
return v___x_1937_;
}
}
static lean_object* _init_l_Lake_Toml_true___closed__5(void){
_start:
{
lean_object* v___x_1950_; lean_object* v___x_1951_; lean_object* v___x_1952_; lean_object* v___x_1953_; 
v___x_1950_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1951_ = ((lean_object*)(l_Lake_Toml_true___closed__4));
v___x_1952_ = ((lean_object*)(l_Lake_Toml_true___closed__1));
v___x_1953_ = l_Lake_Toml_lit(v___x_1952_, v___x_1951_, v___x_1950_);
return v___x_1953_;
}
}
static lean_object* _init_l_Lake_Toml_true(void){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = lean_obj_once(&l_Lake_Toml_true___closed__5, &l_Lake_Toml_true___closed__5_once, _init_l_Lake_Toml_true___closed__5);
return v___x_1954_;
}
}
static lean_object* _init_l_Lake_Toml_false___closed__5(void){
_start:
{
lean_object* v___x_1967_; lean_object* v___x_1968_; lean_object* v___x_1969_; lean_object* v___x_1970_; 
v___x_1967_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_1968_ = ((lean_object*)(l_Lake_Toml_false___closed__4));
v___x_1969_ = ((lean_object*)(l_Lake_Toml_false___closed__1));
v___x_1970_ = l_Lake_Toml_lit(v___x_1969_, v___x_1968_, v___x_1967_);
return v___x_1970_;
}
}
static lean_object* _init_l_Lake_Toml_false(void){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = lean_obj_once(&l_Lake_Toml_false___closed__5, &l_Lake_Toml_false___closed__5_once, _init_l_Lake_Toml_false___closed__5);
return v___x_1971_;
}
}
static lean_object* _init_l_Lake_Toml_boolean___closed__2(void){
_start:
{
lean_object* v___x_1977_; lean_object* v___x_1978_; lean_object* v___x_1979_; 
v___x_1977_ = l_Lake_Toml_false;
v___x_1978_ = l_Lake_Toml_true;
v___x_1979_ = l_Lean_Parser_orelse(v___x_1978_, v___x_1977_);
return v___x_1979_;
}
}
static lean_object* _init_l_Lake_Toml_boolean___closed__3(void){
_start:
{
uint8_t v___x_1980_; lean_object* v___x_1981_; lean_object* v___x_1982_; lean_object* v___x_1983_; lean_object* v___x_1984_; 
v___x_1980_ = 0;
v___x_1981_ = lean_obj_once(&l_Lake_Toml_boolean___closed__2, &l_Lake_Toml_boolean___closed__2_once, _init_l_Lake_Toml_boolean___closed__2);
v___x_1982_ = ((lean_object*)(l_Lake_Toml_boolean___closed__1));
v___x_1983_ = ((lean_object*)(l_Lake_Toml_boolean___closed__0));
v___x_1984_ = l_Lean_Parser_nodeWithAntiquot(v___x_1983_, v___x_1982_, v___x_1981_, v___x_1980_);
return v___x_1984_;
}
}
static lean_object* _init_l_Lake_Toml_boolean(void){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = lean_obj_once(&l_Lake_Toml_boolean___closed__3, &l_Lake_Toml_boolean___closed__3_once, _init_l_Lake_Toml_boolean___closed__3);
return v___x_1985_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__0(void){
_start:
{
uint8_t v___x_1986_; lean_object* v___x_1987_; lean_object* v___x_1988_; lean_object* v___x_1989_; 
v___x_1986_ = 0;
v___x_1987_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_1988_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2));
v___x_1989_ = l_Lean_Parser_mkAntiquot(v___x_1988_, v___x_1987_, v___x_1986_, v___x_1986_);
return v___x_1989_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__1(void){
_start:
{
uint8_t v___x_1990_; lean_object* v___x_1991_; lean_object* v___x_1992_; lean_object* v___x_1993_; 
v___x_1990_ = 0;
v___x_1991_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_1992_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5));
v___x_1993_ = l_Lean_Parser_mkAntiquot(v___x_1992_, v___x_1991_, v___x_1990_, v___x_1990_);
return v___x_1993_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__2(void){
_start:
{
uint8_t v___x_1994_; lean_object* v___x_1995_; lean_object* v___x_1996_; lean_object* v___x_1997_; 
v___x_1994_ = 0;
v___x_1995_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__17));
v___x_1996_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__16));
v___x_1997_ = l_Lean_Parser_mkAntiquot(v___x_1996_, v___x_1995_, v___x_1994_, v___x_1994_);
return v___x_1997_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__3(void){
_start:
{
uint8_t v___x_1998_; lean_object* v___x_1999_; lean_object* v___x_2000_; lean_object* v___x_2001_; 
v___x_1998_ = 0;
v___x_1999_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__12));
v___x_2000_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__11));
v___x_2001_ = l_Lean_Parser_mkAntiquot(v___x_2000_, v___x_1999_, v___x_1998_, v___x_1998_);
return v___x_2001_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__4(void){
_start:
{
uint8_t v___x_2002_; lean_object* v___x_2003_; lean_object* v___x_2004_; lean_object* v___x_2005_; 
v___x_2002_ = 0;
v___x_2003_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__7));
v___x_2004_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__6));
v___x_2005_ = l_Lean_Parser_mkAntiquot(v___x_2004_, v___x_2003_, v___x_2002_, v___x_2002_);
return v___x_2005_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__5(void){
_start:
{
uint8_t v___x_2006_; lean_object* v___x_2007_; lean_object* v___x_2008_; lean_object* v___x_2009_; 
v___x_2006_ = 0;
v___x_2007_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_2008_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0));
v___x_2009_ = l_Lean_Parser_mkAntiquot(v___x_2008_, v___x_2007_, v___x_2006_, v___x_2006_);
return v___x_2009_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__8(void){
_start:
{
uint8_t v___x_2015_; lean_object* v___x_2016_; lean_object* v___x_2017_; lean_object* v___x_2018_; 
v___x_2015_ = 1;
v___x_2016_ = ((lean_object*)(l_Lake_Toml_numeralAntiquot___closed__7));
v___x_2017_ = ((lean_object*)(l_Lake_Toml_numeralAntiquot___closed__6));
v___x_2018_ = l_Lean_Parser_mkAntiquot(v___x_2017_, v___x_2016_, v___x_2015_, v___x_2015_);
return v___x_2018_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__9(void){
_start:
{
lean_object* v___x_2019_; lean_object* v___x_2020_; lean_object* v___x_2021_; 
v___x_2019_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__8, &l_Lake_Toml_numeralAntiquot___closed__8_once, _init_l_Lake_Toml_numeralAntiquot___closed__8);
v___x_2020_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__5, &l_Lake_Toml_numeralAntiquot___closed__5_once, _init_l_Lake_Toml_numeralAntiquot___closed__5);
v___x_2021_ = l_Lean_Parser_orelse(v___x_2020_, v___x_2019_);
return v___x_2021_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__10(void){
_start:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2024_; 
v___x_2022_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__9, &l_Lake_Toml_numeralAntiquot___closed__9_once, _init_l_Lake_Toml_numeralAntiquot___closed__9);
v___x_2023_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__4, &l_Lake_Toml_numeralAntiquot___closed__4_once, _init_l_Lake_Toml_numeralAntiquot___closed__4);
v___x_2024_ = l_Lean_Parser_orelse(v___x_2023_, v___x_2022_);
return v___x_2024_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__11(void){
_start:
{
lean_object* v___x_2025_; lean_object* v___x_2026_; lean_object* v___x_2027_; 
v___x_2025_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__10, &l_Lake_Toml_numeralAntiquot___closed__10_once, _init_l_Lake_Toml_numeralAntiquot___closed__10);
v___x_2026_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__3, &l_Lake_Toml_numeralAntiquot___closed__3_once, _init_l_Lake_Toml_numeralAntiquot___closed__3);
v___x_2027_ = l_Lean_Parser_orelse(v___x_2026_, v___x_2025_);
return v___x_2027_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__12(void){
_start:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; lean_object* v___x_2030_; 
v___x_2028_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__11, &l_Lake_Toml_numeralAntiquot___closed__11_once, _init_l_Lake_Toml_numeralAntiquot___closed__11);
v___x_2029_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__2, &l_Lake_Toml_numeralAntiquot___closed__2_once, _init_l_Lake_Toml_numeralAntiquot___closed__2);
v___x_2030_ = l_Lean_Parser_orelse(v___x_2029_, v___x_2028_);
return v___x_2030_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__13(void){
_start:
{
lean_object* v___x_2031_; lean_object* v___x_2032_; lean_object* v___x_2033_; 
v___x_2031_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__12, &l_Lake_Toml_numeralAntiquot___closed__12_once, _init_l_Lake_Toml_numeralAntiquot___closed__12);
v___x_2032_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__1, &l_Lake_Toml_numeralAntiquot___closed__1_once, _init_l_Lake_Toml_numeralAntiquot___closed__1);
v___x_2033_ = l_Lean_Parser_orelse(v___x_2032_, v___x_2031_);
return v___x_2033_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__14(void){
_start:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2036_; 
v___x_2034_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__13, &l_Lake_Toml_numeralAntiquot___closed__13_once, _init_l_Lake_Toml_numeralAntiquot___closed__13);
v___x_2035_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__0, &l_Lake_Toml_numeralAntiquot___closed__0_once, _init_l_Lake_Toml_numeralAntiquot___closed__0);
v___x_2036_ = l_Lean_Parser_orelse(v___x_2035_, v___x_2034_);
return v___x_2036_;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot(void){
_start:
{
lean_object* v___x_2037_; 
v___x_2037_ = lean_obj_once(&l_Lake_Toml_numeralAntiquot___closed__14, &l_Lake_Toml_numeralAntiquot___closed__14_once, _init_l_Lake_Toml_numeralAntiquot___closed__14);
return v___x_2037_;
}
}
static lean_object* _init_l_Lake_Toml_numeral___closed__0(void){
_start:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = lean_alloc_closure((void*)(l_Lake_Toml_numeralFn), 2, 0);
v___x_2039_ = l_Lake_Toml_dynamicNode(v___x_2038_);
return v___x_2039_;
}
}
static lean_object* _init_l_Lake_Toml_numeral___closed__1(void){
_start:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2040_ = lean_obj_once(&l_Lake_Toml_numeral___closed__0, &l_Lake_Toml_numeral___closed__0_once, _init_l_Lake_Toml_numeral___closed__0);
v___x_2041_ = l_Lake_Toml_numeralAntiquot;
v___x_2042_ = l_Lean_Parser_withAntiquot(v___x_2041_, v___x_2040_);
return v___x_2042_;
}
}
static lean_object* _init_l_Lake_Toml_numeral(void){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = lean_obj_once(&l_Lake_Toml_numeral___closed__1, &l_Lake_Toml_numeral___closed__1_once, _init_l_Lake_Toml_numeral___closed__1);
return v___x_2043_;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_numeralOfKind___lam__0(lean_object* v_kind_2044_, lean_object* v_x_2045_){
_start:
{
uint8_t v___x_2046_; 
v___x_2046_ = l_Lean_Syntax_isOfKind(v_x_2045_, v_kind_2044_);
return v___x_2046_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralOfKind___lam__0___boxed(lean_object* v_kind_2047_, lean_object* v_x_2048_){
_start:
{
uint8_t v_res_2049_; lean_object* v_r_2050_; 
v_res_2049_ = l_Lake_Toml_numeralOfKind___lam__0(v_kind_2047_, v_x_2048_);
lean_dec(v_kind_2047_);
v_r_2050_ = lean_box(v_res_2049_);
return v_r_2050_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralOfKind(lean_object* v_name_2052_, lean_object* v_kind_2053_){
_start:
{
lean_object* v___f_2054_; lean_object* v___x_2055_; lean_object* v___x_2056_; lean_object* v___x_2057_; lean_object* v___x_2058_; lean_object* v___x_2059_; lean_object* v___x_2060_; lean_object* v___x_2061_; 
v___f_2054_ = lean_alloc_closure((void*)(l_Lake_Toml_numeralOfKind___lam__0___boxed), 2, 1);
lean_closure_set(v___f_2054_, 0, v_kind_2053_);
v___x_2055_ = l_Lake_Toml_numeral;
v___x_2056_ = lean_box(0);
v___x_2057_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_2057_, 0, v_name_2052_);
lean_ctor_set(v___x_2057_, 1, v___x_2056_);
v___x_2058_ = ((lean_object*)(l_Lake_Toml_numeralOfKind___closed__0));
v___x_2059_ = l_Lean_Parser_checkStackTop(v___f_2054_, v___x_2058_);
v___x_2060_ = l_Lean_Parser_setExpected(v___x_2057_, v___x_2059_);
v___x_2061_ = l_Lean_Parser_andthen(v___x_2055_, v___x_2060_);
return v___x_2061_;
}
}
static lean_object* _init_l_Lake_Toml_float___closed__0(void){
_start:
{
lean_object* v___x_2062_; lean_object* v___x_2063_; lean_object* v___x_2064_; 
v___x_2062_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3));
v___x_2063_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2));
v___x_2064_ = l_Lake_Toml_numeralOfKind(v___x_2063_, v___x_2062_);
return v___x_2064_;
}
}
static lean_object* _init_l_Lake_Toml_float(void){
_start:
{
lean_object* v___x_2065_; 
v___x_2065_ = lean_obj_once(&l_Lake_Toml_float___closed__0, &l_Lake_Toml_float___closed__0_once, _init_l_Lake_Toml_float___closed__0);
return v___x_2065_;
}
}
static lean_object* _init_l_Lake_Toml_decInt___closed__0(void){
_start:
{
lean_object* v___x_2066_; lean_object* v___x_2067_; lean_object* v___x_2068_; 
v___x_2066_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6));
v___x_2067_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0));
v___x_2068_ = l_Lake_Toml_numeralOfKind(v___x_2067_, v___x_2066_);
return v___x_2068_;
}
}
static lean_object* _init_l_Lake_Toml_decInt(void){
_start:
{
lean_object* v___x_2069_; 
v___x_2069_ = lean_obj_once(&l_Lake_Toml_decInt___closed__0, &l_Lake_Toml_decInt___closed__0_once, _init_l_Lake_Toml_decInt___closed__0);
return v___x_2069_;
}
}
static lean_object* _init_l_Lake_Toml_binNum___closed__1(void){
_start:
{
lean_object* v___x_2071_; lean_object* v___x_2072_; lean_object* v___x_2073_; 
v___x_2071_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__17));
v___x_2072_ = ((lean_object*)(l_Lake_Toml_binNum___closed__0));
v___x_2073_ = l_Lake_Toml_numeralOfKind(v___x_2072_, v___x_2071_);
return v___x_2073_;
}
}
static lean_object* _init_l_Lake_Toml_binNum(void){
_start:
{
lean_object* v___x_2074_; 
v___x_2074_ = lean_obj_once(&l_Lake_Toml_binNum___closed__1, &l_Lake_Toml_binNum___closed__1_once, _init_l_Lake_Toml_binNum___closed__1);
return v___x_2074_;
}
}
static lean_object* _init_l_Lake_Toml_octNum___closed__1(void){
_start:
{
lean_object* v___x_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; 
v___x_2076_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__12));
v___x_2077_ = ((lean_object*)(l_Lake_Toml_octNum___closed__0));
v___x_2078_ = l_Lake_Toml_numeralOfKind(v___x_2077_, v___x_2076_);
return v___x_2078_;
}
}
static lean_object* _init_l_Lake_Toml_octNum(void){
_start:
{
lean_object* v___x_2079_; 
v___x_2079_ = lean_obj_once(&l_Lake_Toml_octNum___closed__1, &l_Lake_Toml_octNum___closed__1_once, _init_l_Lake_Toml_octNum___closed__1);
return v___x_2079_;
}
}
static lean_object* _init_l_Lake_Toml_hexNum___closed__1(void){
_start:
{
lean_object* v___x_2081_; lean_object* v___x_2082_; lean_object* v___x_2083_; 
v___x_2081_ = ((lean_object*)(l_Lake_Toml_numeralFn___lam__0___closed__7));
v___x_2082_ = ((lean_object*)(l_Lake_Toml_hexNum___closed__0));
v___x_2083_ = l_Lake_Toml_numeralOfKind(v___x_2082_, v___x_2081_);
return v___x_2083_;
}
}
static lean_object* _init_l_Lake_Toml_hexNum(void){
_start:
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_obj_once(&l_Lake_Toml_hexNum___closed__1, &l_Lake_Toml_hexNum___closed__1_once, _init_l_Lake_Toml_hexNum___closed__1);
return v___x_2084_;
}
}
static lean_object* _init_l_Lake_Toml_dateTime___closed__0(void){
_start:
{
lean_object* v___x_2085_; lean_object* v___x_2086_; lean_object* v___x_2087_; 
v___x_2085_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1));
v___x_2086_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2));
v___x_2087_ = l_Lake_Toml_numeralOfKind(v___x_2086_, v___x_2085_);
return v___x_2087_;
}
}
static lean_object* _init_l_Lake_Toml_dateTime(void){
_start:
{
lean_object* v___x_2088_; 
v___x_2088_ = lean_obj_once(&l_Lake_Toml_dateTime___closed__0, &l_Lake_Toml_dateTime___closed__0_once, _init_l_Lake_Toml_dateTime___closed__0);
return v___x_2088_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_valCore(lean_object* v_val_2089_){
_start:
{
lean_object* v___x_2090_; lean_object* v___x_2091_; lean_object* v___x_2092_; lean_object* v___x_2093_; lean_object* v___x_2094_; lean_object* v___x_2095_; lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2090_ = l_Lake_Toml_string;
v___x_2091_ = l_Lake_Toml_boolean;
v___x_2092_ = l_Lake_Toml_numeral;
lean_inc_ref(v_val_2089_);
v___x_2093_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(v_val_2089_);
v___x_2094_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(v_val_2089_);
v___x_2095_ = l_Lean_Parser_orelse(v___x_2093_, v___x_2094_);
v___x_2096_ = l_Lean_Parser_orelse(v___x_2092_, v___x_2095_);
v___x_2097_ = l_Lean_Parser_orelse(v___x_2091_, v___x_2096_);
v___x_2098_ = l_Lean_Parser_orelse(v___x_2090_, v___x_2097_);
return v___x_2098_;
}
}
static lean_object* _init_l_Lake_Toml_val___closed__3(void){
_start:
{
uint8_t v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2105_ = 1;
v___x_2106_ = ((lean_object*)(l_Lake_Toml_val___closed__2));
v___x_2107_ = ((lean_object*)(l_Lake_Toml_val___closed__1));
v___x_2108_ = ((lean_object*)(l_Lake_Toml_val___closed__0));
v___x_2109_ = l_Lake_Toml_recNodeWithAntiquot(v___x_2108_, v___x_2107_, v___x_2106_, v___x_2105_);
return v___x_2109_;
}
}
static lean_object* _init_l_Lake_Toml_val(void){
_start:
{
lean_object* v___x_2110_; 
v___x_2110_ = lean_obj_once(&l_Lake_Toml_val___closed__3, &l_Lake_Toml_val___closed__3_once, _init_l_Lake_Toml_val___closed__3);
return v___x_2110_;
}
}
static lean_object* _init_l_Lake_Toml_array___closed__0(void){
_start:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = l_Lake_Toml_val;
v___x_2112_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(v___x_2111_);
return v___x_2112_;
}
}
static lean_object* _init_l_Lake_Toml_array(void){
_start:
{
lean_object* v___x_2113_; 
v___x_2113_ = lean_obj_once(&l_Lake_Toml_array___closed__0, &l_Lake_Toml_array___closed__0_once, _init_l_Lake_Toml_array___closed__0);
return v___x_2113_;
}
}
static lean_object* _init_l_Lake_Toml_inlineTable___closed__0(void){
_start:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
v___x_2114_ = l_Lake_Toml_val;
v___x_2115_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(v___x_2114_);
return v___x_2115_;
}
}
static lean_object* _init_l_Lake_Toml_inlineTable(void){
_start:
{
lean_object* v___x_2116_; 
v___x_2116_ = lean_obj_once(&l_Lake_Toml_inlineTable___closed__0, &l_Lake_Toml_inlineTable___closed__0_once, _init_l_Lake_Toml_inlineTable___closed__0);
return v___x_2116_;
}
}
static lean_object* _init_l_Lake_Toml_keyval___closed__0(void){
_start:
{
lean_object* v___x_2117_; lean_object* v___x_2118_; 
v___x_2117_ = l_Lake_Toml_val;
v___x_2118_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(v___x_2117_);
return v___x_2118_;
}
}
static lean_object* _init_l_Lake_Toml_keyval(void){
_start:
{
lean_object* v___x_2119_; 
v___x_2119_ = lean_obj_once(&l_Lake_Toml_keyval___closed__0, &l_Lake_Toml_keyval___closed__0_once, _init_l_Lake_Toml_keyval___closed__0);
return v___x_2119_;
}
}
static lean_object* _init_l_Lake_Toml_expression___closed__0(void){
_start:
{
lean_object* v___x_2120_; lean_object* v___x_2121_; 
v___x_2120_ = l_Lake_Toml_val;
v___x_2121_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(v___x_2120_);
return v___x_2121_;
}
}
static lean_object* _init_l_Lake_Toml_expression(void){
_start:
{
lean_object* v___x_2122_; 
v___x_2122_ = lean_obj_once(&l_Lake_Toml_expression___closed__0, &l_Lake_Toml_expression___closed__0_once, _init_l_Lake_Toml_expression___closed__0);
return v___x_2122_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_header_formatter(lean_object* v_a_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_a_2126_){
_start:
{
lean_object* v___x_2128_; lean_object* v___x_2129_; uint8_t v___x_2130_; lean_object* v___x_2131_; 
v___x_2128_ = ((lean_object*)(l_Lake_Toml_header___closed__0));
v___x_2129_ = ((lean_object*)(l_Lake_Toml_header___closed__1));
v___x_2130_ = 0;
v___x_2131_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v___x_2128_, v___x_2129_, v___x_2130_, v_a_2123_, v_a_2124_, v_a_2125_, v_a_2126_);
return v___x_2131_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_header_formatter___boxed(lean_object* v_a_2132_, lean_object* v_a_2133_, lean_object* v_a_2134_, lean_object* v_a_2135_, lean_object* v_a_2136_){
_start:
{
lean_object* v_res_2137_; 
v_res_2137_ = l_Lake_Toml_header_formatter(v_a_2132_, v_a_2133_, v_a_2134_, v_a_2135_);
lean_dec(v_a_2135_);
lean_dec_ref(v_a_2134_);
lean_dec(v_a_2133_);
lean_dec_ref(v_a_2132_);
return v_res_2137_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_formatter(lean_object* v_a_2138_, lean_object* v_a_2139_, lean_object* v_a_2140_, lean_object* v_a_2141_){
_start:
{
lean_object* v___x_2143_; lean_object* v___x_2144_; uint8_t v___x_2145_; lean_object* v___x_2146_; 
v___x_2143_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__0));
v___x_2144_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__1));
v___x_2145_ = 0;
v___x_2146_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v___x_2143_, v___x_2144_, v___x_2145_, v_a_2138_, v_a_2139_, v_a_2140_, v_a_2141_);
return v___x_2146_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_formatter___boxed(lean_object* v_a_2147_, lean_object* v_a_2148_, lean_object* v_a_2149_, lean_object* v_a_2150_, lean_object* v_a_2151_){
_start:
{
lean_object* v_res_2152_; 
v_res_2152_ = l_Lake_Toml_unquotedKey_formatter(v_a_2147_, v_a_2148_, v_a_2149_, v_a_2150_);
lean_dec(v_a_2150_);
lean_dec_ref(v_a_2149_);
lean_dec(v_a_2148_);
lean_dec_ref(v_a_2147_);
return v_res_2152_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_formatter(lean_object* v_a_2153_, lean_object* v_a_2154_, lean_object* v_a_2155_, lean_object* v_a_2156_){
_start:
{
lean_object* v___x_2158_; lean_object* v___x_2159_; uint8_t v___x_2160_; lean_object* v___x_2161_; 
v___x_2158_ = ((lean_object*)(l_Lake_Toml_basicString___closed__0));
v___x_2159_ = ((lean_object*)(l_Lake_Toml_basicString___closed__1));
v___x_2160_ = 0;
v___x_2161_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v___x_2158_, v___x_2159_, v___x_2160_, v_a_2153_, v_a_2154_, v_a_2155_, v_a_2156_);
return v___x_2161_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_formatter___boxed(lean_object* v_a_2162_, lean_object* v_a_2163_, lean_object* v_a_2164_, lean_object* v_a_2165_, lean_object* v_a_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l_Lake_Toml_basicString_formatter(v_a_2162_, v_a_2163_, v_a_2164_, v_a_2165_);
lean_dec(v_a_2165_);
lean_dec_ref(v_a_2164_);
lean_dec(v_a_2163_);
lean_dec_ref(v_a_2162_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_formatter(lean_object* v_a_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_){
_start:
{
lean_object* v___x_2173_; lean_object* v___x_2174_; uint8_t v___x_2175_; lean_object* v___x_2176_; 
v___x_2173_ = ((lean_object*)(l_Lake_Toml_literalString___closed__0));
v___x_2174_ = ((lean_object*)(l_Lake_Toml_literalString___closed__1));
v___x_2175_ = 0;
v___x_2176_ = l_Lake_Toml_litWithAntiquot_formatter___redArg(v___x_2173_, v___x_2174_, v___x_2175_, v_a_2168_, v_a_2169_, v_a_2170_, v_a_2171_);
return v___x_2176_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_formatter___boxed(lean_object* v_a_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_a_2180_, lean_object* v_a_2181_){
_start:
{
lean_object* v_res_2182_; 
v_res_2182_ = l_Lake_Toml_literalString_formatter(v_a_2177_, v_a_2178_, v_a_2179_, v_a_2180_);
lean_dec(v_a_2180_);
lean_dec_ref(v_a_2179_);
lean_dec(v_a_2178_);
lean_dec_ref(v_a_2177_);
return v_res_2182_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_formatter(lean_object* v_a_2183_, lean_object* v_a_2184_, lean_object* v_a_2185_, lean_object* v_a_2186_){
_start:
{
lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2190_; 
v___x_2188_ = lean_alloc_closure((void*)(l_Lake_Toml_basicString_formatter___boxed), 5, 0);
v___x_2189_ = lean_alloc_closure((void*)(l_Lake_Toml_literalString_formatter___boxed), 5, 0);
v___x_2190_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2188_, v___x_2189_, v_a_2183_, v_a_2184_, v_a_2185_, v_a_2186_);
return v___x_2190_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_formatter___boxed(lean_object* v_a_2191_, lean_object* v_a_2192_, lean_object* v_a_2193_, lean_object* v_a_2194_, lean_object* v_a_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l_Lake_Toml_quotedKey_formatter(v_a_2191_, v_a_2192_, v_a_2193_, v_a_2194_);
lean_dec(v_a_2194_);
lean_dec_ref(v_a_2193_);
lean_dec(v_a_2192_);
lean_dec_ref(v_a_2191_);
return v_res_2196_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey_formatter___closed__0(void){
_start:
{
lean_object* v___x_2197_; lean_object* v___x_2198_; lean_object* v___x_2199_; 
v___x_2197_ = lean_alloc_closure((void*)(l_Lake_Toml_quotedKey_formatter___boxed), 5, 0);
v___x_2198_ = lean_alloc_closure((void*)(l_Lake_Toml_unquotedKey_formatter___boxed), 5, 0);
v___x_2199_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2199_, 0, v___x_2198_);
lean_closure_set(v___x_2199_, 1, v___x_2197_);
return v___x_2199_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_formatter(lean_object* v_a_2200_, lean_object* v_a_2201_, lean_object* v_a_2202_, lean_object* v_a_2203_){
_start:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; uint8_t v___x_2208_; lean_object* v___x_2209_; 
v___x_2205_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__0));
v___x_2206_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__1));
v___x_2207_ = lean_obj_once(&l_Lake_Toml_simpleKey_formatter___closed__0, &l_Lake_Toml_simpleKey_formatter___closed__0_once, _init_l_Lake_Toml_simpleKey_formatter___closed__0);
v___x_2208_ = 1;
v___x_2209_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2205_, v___x_2206_, v___x_2207_, v___x_2208_, v_a_2200_, v_a_2201_, v_a_2202_, v_a_2203_);
return v___x_2209_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_formatter___boxed(lean_object* v_a_2210_, lean_object* v_a_2211_, lean_object* v_a_2212_, lean_object* v_a_2213_, lean_object* v_a_2214_){
_start:
{
lean_object* v_res_2215_; 
v_res_2215_ = l_Lake_Toml_simpleKey_formatter(v_a_2210_, v_a_2211_, v_a_2212_, v_a_2213_);
lean_dec(v_a_2213_);
lean_dec_ref(v_a_2212_);
lean_dec(v_a_2211_);
lean_dec_ref(v_a_2210_);
return v_res_2215_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter___redArg(){
_start:
{
lean_object* v___x_2217_; 
v___x_2217_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_2217_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter___redArg___boxed(lean_object* v_a_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_Lake_Toml_trailingWs_formatter___redArg();
return v_res_2219_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter(lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_){
_start:
{
lean_object* v___x_2225_; 
v___x_2225_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_2225_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter___boxed(lean_object* v_a_2226_, lean_object* v_a_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_a_2230_){
_start:
{
lean_object* v_res_2231_; 
v_res_2231_ = l_Lake_Toml_trailingWs_formatter(v_a_2226_, v_a_2227_, v_a_2228_, v_a_2229_);
lean_dec(v_a_2229_);
lean_dec_ref(v_a_2228_);
lean_dec(v_a_2227_);
lean_dec_ref(v_a_2226_);
return v_res_2231_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_2232_; lean_object* v___x_2233_; 
v___x_2232_ = 46;
v___x_2233_ = lean_box_uint32(v___x_2232_);
return v___x_2233_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__0(void){
_start:
{
lean_object* v___x_2234_; lean_object* v___x_2235_; lean_object* v___x_2236_; lean_object* v___x_2237_; 
v___x_2234_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2235_ = lean_obj_once(&l_Lake_Toml_key___closed__7, &l_Lake_Toml_key___closed__7_once, _init_l_Lake_Toml_key___closed__7);
v___x_2236_ = l_Lake_Toml_key_formatter___closed__0___boxed__const__1;
v___x_2237_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2237_, 0, v___x_2236_);
lean_closure_set(v___x_2237_, 1, v___x_2235_);
lean_closure_set(v___x_2237_, 2, v___x_2234_);
return v___x_2237_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__1(void){
_start:
{
lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2238_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2239_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__0, &l_Lake_Toml_key_formatter___closed__0_once, _init_l_Lake_Toml_key_formatter___closed__0);
v___x_2240_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2240_, 0, v___x_2239_);
lean_closure_set(v___x_2240_, 1, v___x_2238_);
return v___x_2240_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__2(void){
_start:
{
lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; 
v___x_2241_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__1, &l_Lake_Toml_key_formatter___closed__1_once, _init_l_Lake_Toml_key_formatter___closed__1);
v___x_2242_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2243_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2243_, 0, v___x_2242_);
lean_closure_set(v___x_2243_, 1, v___x_2241_);
return v___x_2243_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__3(void){
_start:
{
uint8_t v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; 
v___x_2244_ = 0;
v___x_2245_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__2, &l_Lake_Toml_key_formatter___closed__2_once, _init_l_Lake_Toml_key_formatter___closed__2);
v___x_2246_ = ((lean_object*)(l_Lake_Toml_key___closed__3));
v___x_2247_ = lean_alloc_closure((void*)(l_Lake_Toml_simpleKey_formatter___boxed), 5, 0);
v___x_2248_ = lean_box(v___x_2244_);
v___x_2249_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_formatter___boxed), 9, 4);
lean_closure_set(v___x_2249_, 0, v___x_2247_);
lean_closure_set(v___x_2249_, 1, v___x_2246_);
lean_closure_set(v___x_2249_, 2, v___x_2245_);
lean_closure_set(v___x_2249_, 3, v___x_2248_);
return v___x_2249_;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__4(void){
_start:
{
lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v___x_2250_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__3, &l_Lake_Toml_key_formatter___closed__3_once, _init_l_Lake_Toml_key_formatter___closed__3);
v___x_2251_ = ((lean_object*)(l_Lake_Toml_key___closed__2));
v___x_2252_ = lean_alloc_closure((void*)(l_Lean_Parser_setExpected_formatter___boxed), 7, 2);
lean_closure_set(v___x_2252_, 0, v___x_2251_);
lean_closure_set(v___x_2252_, 1, v___x_2250_);
return v___x_2252_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_key_formatter(lean_object* v_a_2253_, lean_object* v_a_2254_, lean_object* v_a_2255_, lean_object* v_a_2256_){
_start:
{
lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; uint8_t v___x_2261_; lean_object* v___x_2262_; 
v___x_2258_ = ((lean_object*)(l_Lake_Toml_key___closed__0));
v___x_2259_ = ((lean_object*)(l_Lake_Toml_key___closed__1));
v___x_2260_ = lean_obj_once(&l_Lake_Toml_key_formatter___closed__4, &l_Lake_Toml_key_formatter___closed__4_once, _init_l_Lake_Toml_key_formatter___closed__4);
v___x_2261_ = 1;
v___x_2262_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2258_, v___x_2259_, v___x_2260_, v___x_2261_, v_a_2253_, v_a_2254_, v_a_2255_, v_a_2256_);
return v___x_2262_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_key_formatter___boxed(lean_object* v_a_2263_, lean_object* v_a_2264_, lean_object* v_a_2265_, lean_object* v_a_2266_, lean_object* v_a_2267_){
_start:
{
lean_object* v_res_2268_; 
v_res_2268_ = l_Lake_Toml_key_formatter(v_a_2263_, v_a_2264_, v_a_2265_, v_a_2266_);
lean_dec(v_a_2266_);
lean_dec_ref(v_a_2265_);
lean_dec(v_a_2264_);
lean_dec_ref(v_a_2263_);
return v_res_2268_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_2269_; lean_object* v___x_2270_; 
v___x_2269_ = 61;
v___x_2270_ = lean_box_uint32(v___x_2269_);
return v___x_2270_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0(void){
_start:
{
lean_object* v___x_2271_; lean_object* v___x_2272_; lean_object* v___x_2273_; lean_object* v___x_2274_; 
v___x_2271_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2272_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5);
v___x_2273_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1;
v___x_2274_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2274_, 0, v___x_2273_);
lean_closure_set(v___x_2274_, 1, v___x_2272_);
lean_closure_set(v___x_2274_, 2, v___x_2271_);
return v___x_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter(lean_object* v_val_2275_, lean_object* v_a_2276_, lean_object* v_a_2277_, lean_object* v_a_2278_, lean_object* v_a_2279_){
_start:
{
lean_object* v___x_2281_; lean_object* v___x_2282_; lean_object* v___x_2283_; lean_object* v___x_2284_; lean_object* v___x_2285_; lean_object* v___x_2286_; lean_object* v___x_2287_; lean_object* v___x_2288_; lean_object* v___x_2289_; uint8_t v___x_2290_; lean_object* v___x_2291_; 
v___x_2281_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0));
v___x_2282_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1));
v___x_2283_ = lean_alloc_closure((void*)(l_Lake_Toml_key_formatter___boxed), 5, 0);
v___x_2284_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2285_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0);
lean_inc_ref(v___x_2284_);
v___x_2286_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2286_, 0, v___x_2284_);
lean_closure_set(v___x_2286_, 1, v_val_2275_);
v___x_2287_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2287_, 0, v___x_2285_);
lean_closure_set(v___x_2287_, 1, v___x_2286_);
v___x_2288_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2288_, 0, v___x_2284_);
lean_closure_set(v___x_2288_, 1, v___x_2287_);
v___x_2289_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2289_, 0, v___x_2283_);
lean_closure_set(v___x_2289_, 1, v___x_2288_);
v___x_2290_ = 1;
v___x_2291_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2281_, v___x_2282_, v___x_2289_, v___x_2290_, v_a_2276_, v_a_2277_, v_a_2278_, v_a_2279_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___boxed(lean_object* v_val_2292_, lean_object* v_a_2293_, lean_object* v_a_2294_, lean_object* v_a_2295_, lean_object* v_a_2296_, lean_object* v_a_2297_){
_start:
{
lean_object* v_res_2298_; 
v_res_2298_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter(v_val_2292_, v_a_2293_, v_a_2294_, v_a_2295_, v_a_2296_);
lean_dec(v_a_2296_);
lean_dec_ref(v_a_2295_);
lean_dec(v_a_2294_);
lean_dec_ref(v_a_2293_);
return v_res_2298_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1(void){
_start:
{
uint32_t v___x_2299_; lean_object* v___x_2300_; 
v___x_2299_ = 91;
v___x_2300_ = lean_box_uint32(v___x_2299_);
return v___x_2300_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__0(void){
_start:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2301_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2302_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__3));
v___x_2303_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
v___x_2304_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2304_, 0, v___x_2303_);
lean_closure_set(v___x_2304_, 1, v___x_2302_);
lean_closure_set(v___x_2304_, 2, v___x_2301_);
return v___x_2304_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__1(void){
_start:
{
lean_object* v___x_2305_; lean_object* v___x_2306_; lean_object* v___x_2307_; lean_object* v___x_2308_; 
v___x_2305_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2306_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__8, &l_Lake_Toml_stdTable___closed__8_once, _init_l_Lake_Toml_stdTable___closed__8);
v___x_2307_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
v___x_2308_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2308_, 0, v___x_2307_);
lean_closure_set(v___x_2308_, 1, v___x_2306_);
lean_closure_set(v___x_2308_, 2, v___x_2305_);
return v___x_2308_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__2(void){
_start:
{
lean_object* v___x_2309_; lean_object* v___x_2310_; 
v___x_2309_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__1, &l_Lake_Toml_stdTable_formatter___closed__1_once, _init_l_Lake_Toml_stdTable_formatter___closed__1);
v___x_2310_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed), 6, 1);
lean_closure_set(v___x_2310_, 0, v___x_2309_);
return v___x_2310_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__3(void){
_start:
{
lean_object* v___x_2311_; lean_object* v___x_2312_; lean_object* v___x_2313_; 
v___x_2311_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__2, &l_Lake_Toml_stdTable_formatter___closed__2_once, _init_l_Lake_Toml_stdTable_formatter___closed__2);
v___x_2312_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__0, &l_Lake_Toml_stdTable_formatter___closed__0_once, _init_l_Lake_Toml_stdTable_formatter___closed__0);
v___x_2313_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2313_, 0, v___x_2312_);
lean_closure_set(v___x_2313_, 1, v___x_2311_);
return v___x_2313_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__4(void){
_start:
{
lean_object* v___x_2314_; lean_object* v___x_2315_; 
v___x_2314_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__3, &l_Lake_Toml_stdTable_formatter___closed__3_once, _init_l_Lake_Toml_stdTable_formatter___closed__3);
v___x_2315_ = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter___boxed), 6, 1);
lean_closure_set(v___x_2315_, 0, v___x_2314_);
return v___x_2315_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1(void){
_start:
{
uint32_t v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = 93;
v___x_2317_ = lean_box_uint32(v___x_2316_);
return v___x_2317_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__5(void){
_start:
{
lean_object* v___x_2318_; lean_object* v___x_2319_; lean_object* v___x_2320_; lean_object* v___x_2321_; 
v___x_2318_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2319_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__17, &l_Lake_Toml_stdTable___closed__17_once, _init_l_Lake_Toml_stdTable___closed__17);
v___x_2320_ = l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1;
v___x_2321_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(v___x_2321_, 0, v___x_2320_);
lean_closure_set(v___x_2321_, 1, v___x_2319_);
lean_closure_set(v___x_2321_, 2, v___x_2318_);
return v___x_2321_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__6(void){
_start:
{
lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v___x_2322_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__5, &l_Lake_Toml_stdTable_formatter___closed__5_once, _init_l_Lake_Toml_stdTable_formatter___closed__5);
v___x_2323_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2324_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2324_, 0, v___x_2323_);
lean_closure_set(v___x_2324_, 1, v___x_2322_);
return v___x_2324_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__7(void){
_start:
{
lean_object* v___x_2325_; lean_object* v___x_2326_; lean_object* v___x_2327_; 
v___x_2325_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__6, &l_Lake_Toml_stdTable_formatter___closed__6_once, _init_l_Lake_Toml_stdTable_formatter___closed__6);
v___x_2326_ = lean_alloc_closure((void*)(l_Lake_Toml_key_formatter___boxed), 5, 0);
v___x_2327_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2327_, 0, v___x_2326_);
lean_closure_set(v___x_2327_, 1, v___x_2325_);
return v___x_2327_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__8(void){
_start:
{
lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2330_; 
v___x_2328_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__7, &l_Lake_Toml_stdTable_formatter___closed__7_once, _init_l_Lake_Toml_stdTable_formatter___closed__7);
v___x_2329_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2330_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2330_, 0, v___x_2329_);
lean_closure_set(v___x_2330_, 1, v___x_2328_);
return v___x_2330_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__9(void){
_start:
{
lean_object* v___x_2331_; lean_object* v___x_2332_; lean_object* v___x_2333_; 
v___x_2331_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__8, &l_Lake_Toml_stdTable_formatter___closed__8_once, _init_l_Lake_Toml_stdTable_formatter___closed__8);
v___x_2332_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__4, &l_Lake_Toml_stdTable_formatter___closed__4_once, _init_l_Lake_Toml_stdTable_formatter___closed__4);
v___x_2333_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2333_, 0, v___x_2332_);
lean_closure_set(v___x_2333_, 1, v___x_2331_);
return v___x_2333_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_formatter(lean_object* v_a_2334_, lean_object* v_a_2335_, lean_object* v_a_2336_, lean_object* v_a_2337_){
_start:
{
lean_object* v___x_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; uint8_t v___x_2342_; lean_object* v___x_2343_; 
v___x_2339_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__0));
v___x_2340_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__1));
v___x_2341_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__9, &l_Lake_Toml_stdTable_formatter___closed__9_once, _init_l_Lake_Toml_stdTable_formatter___closed__9);
v___x_2342_ = 0;
v___x_2343_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2339_, v___x_2340_, v___x_2341_, v___x_2342_, v_a_2334_, v_a_2335_, v_a_2336_, v_a_2337_);
return v___x_2343_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_formatter___boxed(lean_object* v_a_2344_, lean_object* v_a_2345_, lean_object* v_a_2346_, lean_object* v_a_2347_, lean_object* v_a_2348_){
_start:
{
lean_object* v_res_2349_; 
v_res_2349_ = l_Lake_Toml_stdTable_formatter(v_a_2344_, v_a_2345_, v_a_2346_, v_a_2347_);
lean_dec(v_a_2347_);
lean_dec_ref(v_a_2346_);
lean_dec(v_a_2345_);
lean_dec_ref(v_a_2344_);
return v_res_2349_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__0(void){
_start:
{
lean_object* v___x_2350_; lean_object* v___x_2351_; lean_object* v___x_2352_; 
v___x_2350_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__1, &l_Lake_Toml_stdTable_formatter___closed__1_once, _init_l_Lake_Toml_stdTable_formatter___closed__1);
v___x_2351_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__0, &l_Lake_Toml_stdTable_formatter___closed__0_once, _init_l_Lake_Toml_stdTable_formatter___closed__0);
v___x_2352_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2352_, 0, v___x_2351_);
lean_closure_set(v___x_2352_, 1, v___x_2350_);
return v___x_2352_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__1(void){
_start:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; 
v___x_2353_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__0, &l_Lake_Toml_arrayTable_formatter___closed__0_once, _init_l_Lake_Toml_arrayTable_formatter___closed__0);
v___x_2354_ = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter___boxed), 6, 1);
lean_closure_set(v___x_2354_, 0, v___x_2353_);
return v___x_2354_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__2(void){
_start:
{
lean_object* v___x_2355_; lean_object* v___x_2356_; 
v___x_2355_ = lean_obj_once(&l_Lake_Toml_stdTable_formatter___closed__5, &l_Lake_Toml_stdTable_formatter___closed__5_once, _init_l_Lake_Toml_stdTable_formatter___closed__5);
v___x_2356_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2356_, 0, v___x_2355_);
lean_closure_set(v___x_2356_, 1, v___x_2355_);
return v___x_2356_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__3(void){
_start:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; 
v___x_2357_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__2, &l_Lake_Toml_arrayTable_formatter___closed__2_once, _init_l_Lake_Toml_arrayTable_formatter___closed__2);
v___x_2358_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2359_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2359_, 0, v___x_2358_);
lean_closure_set(v___x_2359_, 1, v___x_2357_);
return v___x_2359_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__4(void){
_start:
{
lean_object* v___x_2360_; lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2360_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__3, &l_Lake_Toml_arrayTable_formatter___closed__3_once, _init_l_Lake_Toml_arrayTable_formatter___closed__3);
v___x_2361_ = lean_alloc_closure((void*)(l_Lake_Toml_key_formatter___boxed), 5, 0);
v___x_2362_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2362_, 0, v___x_2361_);
lean_closure_set(v___x_2362_, 1, v___x_2360_);
return v___x_2362_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__5(void){
_start:
{
lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v___x_2363_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__4, &l_Lake_Toml_arrayTable_formatter___closed__4_once, _init_l_Lake_Toml_arrayTable_formatter___closed__4);
v___x_2364_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
v___x_2365_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2365_, 0, v___x_2364_);
lean_closure_set(v___x_2365_, 1, v___x_2363_);
return v___x_2365_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__6(void){
_start:
{
lean_object* v___x_2366_; lean_object* v___x_2367_; lean_object* v___x_2368_; 
v___x_2366_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__5, &l_Lake_Toml_arrayTable_formatter___closed__5_once, _init_l_Lake_Toml_arrayTable_formatter___closed__5);
v___x_2367_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__1, &l_Lake_Toml_arrayTable_formatter___closed__1_once, _init_l_Lake_Toml_arrayTable_formatter___closed__1);
v___x_2368_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2368_, 0, v___x_2367_);
lean_closure_set(v___x_2368_, 1, v___x_2366_);
return v___x_2368_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_formatter(lean_object* v_a_2369_, lean_object* v_a_2370_, lean_object* v_a_2371_, lean_object* v_a_2372_){
_start:
{
lean_object* v___x_2374_; lean_object* v___x_2375_; lean_object* v___x_2376_; uint8_t v___x_2377_; lean_object* v___x_2378_; 
v___x_2374_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__0));
v___x_2375_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__1));
v___x_2376_ = lean_obj_once(&l_Lake_Toml_arrayTable_formatter___closed__6, &l_Lake_Toml_arrayTable_formatter___closed__6_once, _init_l_Lake_Toml_arrayTable_formatter___closed__6);
v___x_2377_ = 0;
v___x_2378_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2374_, v___x_2375_, v___x_2376_, v___x_2377_, v_a_2369_, v_a_2370_, v_a_2371_, v_a_2372_);
return v___x_2378_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_formatter___boxed(lean_object* v_a_2379_, lean_object* v_a_2380_, lean_object* v_a_2381_, lean_object* v_a_2382_, lean_object* v_a_2383_){
_start:
{
lean_object* v_res_2384_; 
v_res_2384_ = l_Lake_Toml_arrayTable_formatter(v_a_2379_, v_a_2380_, v_a_2381_, v_a_2382_);
lean_dec(v_a_2382_);
lean_dec_ref(v_a_2381_);
lean_dec(v_a_2380_);
lean_dec_ref(v_a_2379_);
return v_res_2384_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_table_formatter(lean_object* v_a_2385_, lean_object* v_a_2386_, lean_object* v_a_2387_, lean_object* v_a_2388_){
_start:
{
lean_object* v___x_2390_; lean_object* v___x_2391_; lean_object* v___x_2392_; 
v___x_2390_ = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_formatter___boxed), 5, 0);
v___x_2391_ = lean_alloc_closure((void*)(l_Lake_Toml_arrayTable_formatter___boxed), 5, 0);
v___x_2392_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2390_, v___x_2391_, v_a_2385_, v_a_2386_, v_a_2387_, v_a_2388_);
return v___x_2392_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_table_formatter___boxed(lean_object* v_a_2393_, lean_object* v_a_2394_, lean_object* v_a_2395_, lean_object* v_a_2396_, lean_object* v_a_2397_){
_start:
{
lean_object* v_res_2398_; 
v_res_2398_ = l_Lake_Toml_table_formatter(v_a_2393_, v_a_2394_, v_a_2395_, v_a_2396_);
lean_dec(v_a_2396_);
lean_dec_ref(v_a_2395_);
lean_dec(v_a_2394_);
lean_dec_ref(v_a_2393_);
return v_res_2398_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter(lean_object* v_val_2405_, lean_object* v_a_2406_, lean_object* v_a_2407_, lean_object* v_a_2408_, lean_object* v_a_2409_){
_start:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; lean_object* v___x_2415_; 
v___x_2411_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___closed__0));
v___x_2412_ = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___boxed), 6, 1);
lean_closure_set(v___x_2412_, 0, v_val_2405_);
v___x_2413_ = lean_alloc_closure((void*)(l_Lake_Toml_table_formatter___boxed), 5, 0);
v___x_2414_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter___boxed), 7, 2);
lean_closure_set(v___x_2414_, 0, v___x_2412_);
lean_closure_set(v___x_2414_, 1, v___x_2413_);
v___x_2415_ = l_Lean_PrettyPrinter_Formatter_orelse_formatter(v___x_2411_, v___x_2414_, v_a_2406_, v_a_2407_, v_a_2408_, v_a_2409_);
return v___x_2415_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___boxed(lean_object* v_val_2416_, lean_object* v_a_2417_, lean_object* v_a_2418_, lean_object* v_a_2419_, lean_object* v_a_2420_, lean_object* v_a_2421_){
_start:
{
lean_object* v_res_2422_; 
v_res_2422_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter(v_val_2416_, v_a_2417_, v_a_2418_, v_a_2419_, v_a_2420_);
lean_dec(v_a_2420_);
lean_dec_ref(v_a_2419_);
lean_dec(v_a_2418_);
lean_dec_ref(v_a_2417_);
return v_res_2422_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter___redArg(){
_start:
{
lean_object* v___x_2424_; 
v___x_2424_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_2424_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter___redArg___boxed(lean_object* v_a_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lake_Toml_trailingSep_formatter___redArg();
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter(lean_object* v_a_2427_, lean_object* v_a_2428_, lean_object* v_a_2429_, lean_object* v_a_2430_){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = l_Lake_Toml_epsilon_formatter___redArg();
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter___boxed(lean_object* v_a_2433_, lean_object* v_a_2434_, lean_object* v_a_2435_, lean_object* v_a_2436_, lean_object* v_a_2437_){
_start:
{
lean_object* v_res_2438_; 
v_res_2438_ = l_Lake_Toml_trailingSep_formatter(v_a_2433_, v_a_2434_, v_a_2435_, v_a_2436_);
lean_dec(v_a_2436_);
lean_dec_ref(v_a_2435_);
lean_dec(v_a_2434_);
lean_dec_ref(v_a_2433_);
return v_res_2438_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(lean_object* v_val_2439_, lean_object* v_a_2440_, lean_object* v_a_2441_, lean_object* v_a_2442_, lean_object* v_a_2443_){
_start:
{
lean_object* v___x_2445_; lean_object* v___x_2446_; lean_object* v___x_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; lean_object* v___x_2450_; uint8_t v___x_2451_; lean_object* v___x_2452_; lean_object* v___x_2453_; lean_object* v___x_2454_; lean_object* v___x_2455_; 
v___x_2445_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0));
v___x_2446_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1));
v___x_2447_ = lean_alloc_closure((void*)(l_Lake_Toml_header_formatter___boxed), 5, 0);
v___x_2448_ = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___boxed), 6, 1);
lean_closure_set(v___x_2448_, 0, v_val_2439_);
v___x_2449_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingSep_formatter___boxed), 5, 0);
v___x_2450_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2450_, 0, v___x_2448_);
lean_closure_set(v___x_2450_, 1, v___x_2449_);
v___x_2451_ = 1;
v___x_2452_ = lean_box(v___x_2451_);
v___x_2453_ = lean_alloc_closure((void*)(l_Lake_Toml_sepByLinebreak_formatter___boxed), 7, 2);
lean_closure_set(v___x_2453_, 0, v___x_2450_);
lean_closure_set(v___x_2453_, 1, v___x_2452_);
v___x_2454_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter___boxed), 7, 2);
lean_closure_set(v___x_2454_, 0, v___x_2447_);
lean_closure_set(v___x_2454_, 1, v___x_2453_);
v___x_2455_ = l_Lean_Parser_nodeWithAntiquot_formatter(v___x_2445_, v___x_2446_, v___x_2454_, v___x_2451_, v_a_2440_, v_a_2441_, v_a_2442_, v_a_2443_);
return v___x_2455_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter___boxed(lean_object* v_val_2456_, lean_object* v_a_2457_, lean_object* v_a_2458_, lean_object* v_a_2459_, lean_object* v_a_2460_, lean_object* v_a_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(v_val_2456_, v_a_2457_, v_a_2458_, v_a_2459_, v_a_2460_);
lean_dec(v_a_2460_);
lean_dec_ref(v_a_2459_);
lean_dec(v_a_2458_);
lean_dec_ref(v_a_2457_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_val_formatter(lean_object* v_a_2463_, lean_object* v_a_2464_, lean_object* v_a_2465_, lean_object* v_a_2466_){
_start:
{
lean_object* v___x_2468_; lean_object* v___x_2469_; lean_object* v___x_2470_; uint8_t v___x_2471_; lean_object* v___x_2472_; 
v___x_2468_ = ((lean_object*)(l_Lake_Toml_val___closed__0));
v___x_2469_ = ((lean_object*)(l_Lake_Toml_val___closed__1));
v___x_2470_ = ((lean_object*)(l_Lake_Toml_val___closed__2));
v___x_2471_ = 1;
v___x_2472_ = l_Lake_Toml_recNodeWithAntiquot_formatter(v___x_2468_, v___x_2469_, v___x_2470_, v___x_2471_, v_a_2463_, v_a_2464_, v_a_2465_, v_a_2466_);
return v___x_2472_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_val_formatter___boxed(lean_object* v_a_2473_, lean_object* v_a_2474_, lean_object* v_a_2475_, lean_object* v_a_2476_, lean_object* v_a_2477_){
_start:
{
lean_object* v_res_2478_; 
v_res_2478_ = l_Lake_Toml_val_formatter(v_a_2473_, v_a_2474_, v_a_2475_, v_a_2476_);
lean_dec(v_a_2476_);
lean_dec_ref(v_a_2475_);
lean_dec(v_a_2474_);
lean_dec_ref(v_a_2473_);
return v_res_2478_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_toml_formatter(lean_object* v_a_2479_, lean_object* v_a_2480_, lean_object* v_a_2481_, lean_object* v_a_2482_){
_start:
{
lean_object* v___x_2484_; lean_object* v___x_2485_; 
v___x_2484_ = lean_alloc_closure((void*)(l_Lake_Toml_val_formatter___boxed), 5, 0);
v___x_2485_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(v___x_2484_, v_a_2479_, v_a_2480_, v_a_2481_, v_a_2482_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_toml_formatter___boxed(lean_object* v_a_2486_, lean_object* v_a_2487_, lean_object* v_a_2488_, lean_object* v_a_2489_, lean_object* v_a_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_Lake_Toml_toml_formatter(v_a_2486_, v_a_2487_, v_a_2488_, v_a_2489_);
lean_dec(v_a_2489_);
lean_dec_ref(v_a_2488_);
lean_dec(v_a_2487_);
lean_dec_ref(v_a_2486_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_header_parenthesizer(lean_object* v_a_2492_, lean_object* v_a_2493_, lean_object* v_a_2494_, lean_object* v_a_2495_){
_start:
{
lean_object* v___x_2497_; lean_object* v___x_2498_; uint8_t v___x_2499_; lean_object* v___x_2500_; 
v___x_2497_ = ((lean_object*)(l_Lake_Toml_header___closed__0));
v___x_2498_ = ((lean_object*)(l_Lake_Toml_header___closed__1));
v___x_2499_ = 0;
v___x_2500_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v___x_2497_, v___x_2498_, v___x_2499_, v_a_2492_, v_a_2493_, v_a_2494_, v_a_2495_);
return v___x_2500_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_header_parenthesizer___boxed(lean_object* v_a_2501_, lean_object* v_a_2502_, lean_object* v_a_2503_, lean_object* v_a_2504_, lean_object* v_a_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_Lake_Toml_header_parenthesizer(v_a_2501_, v_a_2502_, v_a_2503_, v_a_2504_);
lean_dec(v_a_2504_);
lean_dec_ref(v_a_2503_);
lean_dec(v_a_2502_);
lean_dec_ref(v_a_2501_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_parenthesizer(lean_object* v_a_2507_, lean_object* v_a_2508_, lean_object* v_a_2509_, lean_object* v_a_2510_){
_start:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; uint8_t v___x_2514_; lean_object* v___x_2515_; 
v___x_2512_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__0));
v___x_2513_ = ((lean_object*)(l_Lake_Toml_unquotedKey___closed__1));
v___x_2514_ = 0;
v___x_2515_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v___x_2512_, v___x_2513_, v___x_2514_, v_a_2507_, v_a_2508_, v_a_2509_, v_a_2510_);
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_parenthesizer___boxed(lean_object* v_a_2516_, lean_object* v_a_2517_, lean_object* v_a_2518_, lean_object* v_a_2519_, lean_object* v_a_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l_Lake_Toml_unquotedKey_parenthesizer(v_a_2516_, v_a_2517_, v_a_2518_, v_a_2519_);
lean_dec(v_a_2519_);
lean_dec_ref(v_a_2518_);
lean_dec(v_a_2517_);
lean_dec_ref(v_a_2516_);
return v_res_2521_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_parenthesizer(lean_object* v_a_2522_, lean_object* v_a_2523_, lean_object* v_a_2524_, lean_object* v_a_2525_){
_start:
{
lean_object* v___x_2527_; lean_object* v___x_2528_; uint8_t v___x_2529_; lean_object* v___x_2530_; 
v___x_2527_ = ((lean_object*)(l_Lake_Toml_basicString___closed__0));
v___x_2528_ = ((lean_object*)(l_Lake_Toml_basicString___closed__1));
v___x_2529_ = 0;
v___x_2530_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v___x_2527_, v___x_2528_, v___x_2529_, v_a_2522_, v_a_2523_, v_a_2524_, v_a_2525_);
return v___x_2530_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_parenthesizer___boxed(lean_object* v_a_2531_, lean_object* v_a_2532_, lean_object* v_a_2533_, lean_object* v_a_2534_, lean_object* v_a_2535_){
_start:
{
lean_object* v_res_2536_; 
v_res_2536_ = l_Lake_Toml_basicString_parenthesizer(v_a_2531_, v_a_2532_, v_a_2533_, v_a_2534_);
lean_dec(v_a_2534_);
lean_dec_ref(v_a_2533_);
lean_dec(v_a_2532_);
lean_dec_ref(v_a_2531_);
return v_res_2536_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_parenthesizer(lean_object* v_a_2537_, lean_object* v_a_2538_, lean_object* v_a_2539_, lean_object* v_a_2540_){
_start:
{
lean_object* v___x_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; lean_object* v___x_2545_; 
v___x_2542_ = ((lean_object*)(l_Lake_Toml_literalString___closed__0));
v___x_2543_ = ((lean_object*)(l_Lake_Toml_literalString___closed__1));
v___x_2544_ = 0;
v___x_2545_ = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(v___x_2542_, v___x_2543_, v___x_2544_, v_a_2537_, v_a_2538_, v_a_2539_, v_a_2540_);
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_parenthesizer___boxed(lean_object* v_a_2546_, lean_object* v_a_2547_, lean_object* v_a_2548_, lean_object* v_a_2549_, lean_object* v_a_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_Lake_Toml_literalString_parenthesizer(v_a_2546_, v_a_2547_, v_a_2548_, v_a_2549_);
lean_dec(v_a_2549_);
lean_dec_ref(v_a_2548_);
lean_dec(v_a_2547_);
lean_dec_ref(v_a_2546_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_parenthesizer(lean_object* v_a_2552_, lean_object* v_a_2553_, lean_object* v_a_2554_, lean_object* v_a_2555_){
_start:
{
lean_object* v___x_2557_; lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2557_ = lean_alloc_closure((void*)(l_Lake_Toml_basicString_parenthesizer___boxed), 5, 0);
v___x_2558_ = lean_alloc_closure((void*)(l_Lake_Toml_literalString_parenthesizer___boxed), 5, 0);
v___x_2559_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___x_2557_, v___x_2558_, v_a_2552_, v_a_2553_, v_a_2554_, v_a_2555_);
return v___x_2559_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_parenthesizer___boxed(lean_object* v_a_2560_, lean_object* v_a_2561_, lean_object* v_a_2562_, lean_object* v_a_2563_, lean_object* v_a_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_Lake_Toml_quotedKey_parenthesizer(v_a_2560_, v_a_2561_, v_a_2562_, v_a_2563_);
lean_dec(v_a_2563_);
lean_dec_ref(v_a_2562_);
lean_dec(v_a_2561_);
lean_dec_ref(v_a_2560_);
return v_res_2565_;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2566_; lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2566_ = lean_alloc_closure((void*)(l_Lake_Toml_quotedKey_parenthesizer___boxed), 5, 0);
v___x_2567_ = lean_alloc_closure((void*)(l_Lake_Toml_unquotedKey_parenthesizer___boxed), 5, 0);
v___x_2568_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2568_, 0, v___x_2567_);
lean_closure_set(v___x_2568_, 1, v___x_2566_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_parenthesizer(lean_object* v_a_2569_, lean_object* v_a_2570_, lean_object* v_a_2571_, lean_object* v_a_2572_){
_start:
{
lean_object* v___x_2574_; lean_object* v___x_2575_; lean_object* v___x_2576_; uint8_t v___x_2577_; lean_object* v___x_2578_; 
v___x_2574_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__0));
v___x_2575_ = ((lean_object*)(l_Lake_Toml_simpleKey___closed__1));
v___x_2576_ = lean_obj_once(&l_Lake_Toml_simpleKey_parenthesizer___closed__0, &l_Lake_Toml_simpleKey_parenthesizer___closed__0_once, _init_l_Lake_Toml_simpleKey_parenthesizer___closed__0);
v___x_2577_ = 1;
v___x_2578_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2574_, v___x_2575_, v___x_2576_, v___x_2577_, v_a_2569_, v_a_2570_, v_a_2571_, v_a_2572_);
return v___x_2578_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_parenthesizer___boxed(lean_object* v_a_2579_, lean_object* v_a_2580_, lean_object* v_a_2581_, lean_object* v_a_2582_, lean_object* v_a_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_Lake_Toml_simpleKey_parenthesizer(v_a_2579_, v_a_2580_, v_a_2581_, v_a_2582_);
lean_dec(v_a_2582_);
lean_dec_ref(v_a_2581_);
lean_dec(v_a_2580_);
lean_dec_ref(v_a_2579_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer___redArg(){
_start:
{
lean_object* v___x_2586_; 
v___x_2586_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_2586_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer___redArg___boxed(lean_object* v_a_2587_){
_start:
{
lean_object* v_res_2588_; 
v_res_2588_ = l_Lake_Toml_trailingWs_parenthesizer___redArg();
return v_res_2588_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer(lean_object* v_a_2589_, lean_object* v_a_2590_, lean_object* v_a_2591_, lean_object* v_a_2592_){
_start:
{
lean_object* v___x_2594_; 
v___x_2594_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_2594_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer___boxed(lean_object* v_a_2595_, lean_object* v_a_2596_, lean_object* v_a_2597_, lean_object* v_a_2598_, lean_object* v_a_2599_){
_start:
{
lean_object* v_res_2600_; 
v_res_2600_ = l_Lake_Toml_trailingWs_parenthesizer(v_a_2595_, v_a_2596_, v_a_2597_, v_a_2598_);
lean_dec(v_a_2598_);
lean_dec_ref(v_a_2597_);
lean_dec(v_a_2596_);
lean_dec_ref(v_a_2595_);
return v_res_2600_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; 
v___x_2601_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2602_ = lean_obj_once(&l_Lake_Toml_key___closed__7, &l_Lake_Toml_key___closed__7_once, _init_l_Lake_Toml_key___closed__7);
v___x_2603_ = l_Lake_Toml_key_formatter___closed__0___boxed__const__1;
v___x_2604_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2604_, 0, v___x_2603_);
lean_closure_set(v___x_2604_, 1, v___x_2602_);
lean_closure_set(v___x_2604_, 2, v___x_2601_);
return v___x_2604_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; 
v___x_2605_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2606_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__0, &l_Lake_Toml_key_parenthesizer___closed__0_once, _init_l_Lake_Toml_key_parenthesizer___closed__0);
v___x_2607_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2607_, 0, v___x_2606_);
lean_closure_set(v___x_2607_, 1, v___x_2605_);
return v___x_2607_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; 
v___x_2608_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__1, &l_Lake_Toml_key_parenthesizer___closed__1_once, _init_l_Lake_Toml_key_parenthesizer___closed__1);
v___x_2609_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2610_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2610_, 0, v___x_2609_);
lean_closure_set(v___x_2610_, 1, v___x_2608_);
return v___x_2610_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__3(void){
_start:
{
uint8_t v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2616_; 
v___x_2611_ = 0;
v___x_2612_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__2, &l_Lake_Toml_key_parenthesizer___closed__2_once, _init_l_Lake_Toml_key_parenthesizer___closed__2);
v___x_2613_ = ((lean_object*)(l_Lake_Toml_key___closed__3));
v___x_2614_ = lean_alloc_closure((void*)(l_Lake_Toml_simpleKey_parenthesizer___boxed), 5, 0);
v___x_2615_ = lean_box(v___x_2611_);
v___x_2616_ = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_parenthesizer___boxed), 9, 4);
lean_closure_set(v___x_2616_, 0, v___x_2614_);
lean_closure_set(v___x_2616_, 1, v___x_2613_);
lean_closure_set(v___x_2616_, 2, v___x_2612_);
lean_closure_set(v___x_2616_, 3, v___x_2615_);
return v___x_2616_;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2617_; lean_object* v___x_2618_; lean_object* v___x_2619_; 
v___x_2617_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__3, &l_Lake_Toml_key_parenthesizer___closed__3_once, _init_l_Lake_Toml_key_parenthesizer___closed__3);
v___x_2618_ = ((lean_object*)(l_Lake_Toml_key___closed__2));
v___x_2619_ = lean_alloc_closure((void*)(l_Lean_Parser_setExpected_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2619_, 0, v___x_2618_);
lean_closure_set(v___x_2619_, 1, v___x_2617_);
return v___x_2619_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_key_parenthesizer(lean_object* v_a_2620_, lean_object* v_a_2621_, lean_object* v_a_2622_, lean_object* v_a_2623_){
_start:
{
lean_object* v___x_2625_; lean_object* v___x_2626_; lean_object* v___x_2627_; uint8_t v___x_2628_; lean_object* v___x_2629_; 
v___x_2625_ = ((lean_object*)(l_Lake_Toml_key___closed__0));
v___x_2626_ = ((lean_object*)(l_Lake_Toml_key___closed__1));
v___x_2627_ = lean_obj_once(&l_Lake_Toml_key_parenthesizer___closed__4, &l_Lake_Toml_key_parenthesizer___closed__4_once, _init_l_Lake_Toml_key_parenthesizer___closed__4);
v___x_2628_ = 1;
v___x_2629_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2625_, v___x_2626_, v___x_2627_, v___x_2628_, v_a_2620_, v_a_2621_, v_a_2622_, v_a_2623_);
return v___x_2629_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_key_parenthesizer___boxed(lean_object* v_a_2630_, lean_object* v_a_2631_, lean_object* v_a_2632_, lean_object* v_a_2633_, lean_object* v_a_2634_){
_start:
{
lean_object* v_res_2635_; 
v_res_2635_ = l_Lake_Toml_key_parenthesizer(v_a_2630_, v_a_2631_, v_a_2632_, v_a_2633_);
lean_dec(v_a_2633_);
lean_dec_ref(v_a_2632_);
lean_dec(v_a_2631_);
lean_dec_ref(v_a_2630_);
return v_res_2635_;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v___x_2636_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2637_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5);
v___x_2638_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1;
v___x_2639_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2639_, 0, v___x_2638_);
lean_closure_set(v___x_2639_, 1, v___x_2637_);
lean_closure_set(v___x_2639_, 2, v___x_2636_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer(lean_object* v_val_2640_, lean_object* v_a_2641_, lean_object* v_a_2642_, lean_object* v_a_2643_, lean_object* v_a_2644_){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; lean_object* v___x_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; uint8_t v___x_2655_; lean_object* v___x_2656_; 
v___x_2646_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0));
v___x_2647_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1));
v___x_2648_ = lean_alloc_closure((void*)(l_Lake_Toml_key_parenthesizer___boxed), 5, 0);
v___x_2649_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2650_ = lean_obj_once(&l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0, &l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0_once, _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0);
lean_inc_ref(v___x_2649_);
v___x_2651_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2651_, 0, v___x_2649_);
lean_closure_set(v___x_2651_, 1, v_val_2640_);
v___x_2652_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2652_, 0, v___x_2650_);
lean_closure_set(v___x_2652_, 1, v___x_2651_);
v___x_2653_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2653_, 0, v___x_2649_);
lean_closure_set(v___x_2653_, 1, v___x_2652_);
v___x_2654_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2654_, 0, v___x_2648_);
lean_closure_set(v___x_2654_, 1, v___x_2653_);
v___x_2655_ = 1;
v___x_2656_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2646_, v___x_2647_, v___x_2654_, v___x_2655_, v_a_2641_, v_a_2642_, v_a_2643_, v_a_2644_);
return v___x_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___boxed(lean_object* v_val_2657_, lean_object* v_a_2658_, lean_object* v_a_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_, lean_object* v_a_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer(v_val_2657_, v_a_2658_, v_a_2659_, v_a_2660_, v_a_2661_);
lean_dec(v_a_2661_);
lean_dec_ref(v_a_2660_);
lean_dec(v_a_2659_);
lean_dec_ref(v_a_2658_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer___lam__0(lean_object* v___x_2664_, lean_object* v___x_2665_, lean_object* v___y_2666_, lean_object* v___y_2667_, lean_object* v___y_2668_, lean_object* v___y_2669_){
_start:
{
lean_object* v___x_2671_; 
v___x_2671_ = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(v___x_2664_, v___x_2665_, v___y_2666_, v___y_2667_, v___y_2668_, v___y_2669_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer___lam__0___boxed(lean_object* v___x_2672_, lean_object* v___x_2673_, lean_object* v___y_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_Lake_Toml_stdTable_parenthesizer___lam__0(v___x_2672_, v___x_2673_, v___y_2674_, v___y_2675_, v___y_2676_, v___y_2677_);
lean_dec(v___y_2677_);
lean_dec_ref(v___y_2676_);
lean_dec(v___y_2675_);
lean_dec_ref(v___y_2674_);
return v_res_2679_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; 
v___x_2680_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2681_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__3));
v___x_2682_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
v___x_2683_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2683_, 0, v___x_2682_);
lean_closure_set(v___x_2683_, 1, v___x_2681_);
lean_closure_set(v___x_2683_, 2, v___x_2680_);
return v___x_2683_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; 
v___x_2684_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2685_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__8, &l_Lake_Toml_stdTable___closed__8_once, _init_l_Lake_Toml_stdTable___closed__8);
v___x_2686_ = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
v___x_2687_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2687_, 0, v___x_2686_);
lean_closure_set(v___x_2687_, 1, v___x_2685_);
lean_closure_set(v___x_2687_, 2, v___x_2684_);
return v___x_2687_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2688_; lean_object* v___x_2689_; 
v___x_2688_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__1, &l_Lake_Toml_stdTable_parenthesizer___closed__1_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__1);
v___x_2689_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2689_, 0, v___x_2688_);
return v___x_2689_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; lean_object* v___f_2692_; 
v___x_2690_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__2, &l_Lake_Toml_stdTable_parenthesizer___closed__2_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__2);
v___x_2691_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__0, &l_Lake_Toml_stdTable_parenthesizer___closed__0_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__0);
v___f_2692_ = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_parenthesizer___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2692_, 0, v___x_2691_);
lean_closure_set(v___f_2692_, 1, v___x_2690_);
return v___f_2692_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; 
v___x_2693_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4));
v___x_2694_ = lean_obj_once(&l_Lake_Toml_stdTable___closed__17, &l_Lake_Toml_stdTable___closed__17_once, _init_l_Lake_Toml_stdTable___closed__17);
v___x_2695_ = l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1;
v___x_2696_ = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(v___x_2696_, 0, v___x_2695_);
lean_closure_set(v___x_2696_, 1, v___x_2694_);
lean_closure_set(v___x_2696_, 2, v___x_2693_);
return v___x_2696_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; 
v___x_2697_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__4, &l_Lake_Toml_stdTable_parenthesizer___closed__4_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__4);
v___x_2698_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2699_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2699_, 0, v___x_2698_);
lean_closure_set(v___x_2699_, 1, v___x_2697_);
return v___x_2699_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__6(void){
_start:
{
lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v___x_2700_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__5, &l_Lake_Toml_stdTable_parenthesizer___closed__5_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__5);
v___x_2701_ = lean_alloc_closure((void*)(l_Lake_Toml_key_parenthesizer___boxed), 5, 0);
v___x_2702_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2702_, 0, v___x_2701_);
lean_closure_set(v___x_2702_, 1, v___x_2700_);
return v___x_2702_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__7(void){
_start:
{
lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; 
v___x_2703_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__6, &l_Lake_Toml_stdTable_parenthesizer___closed__6_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__6);
v___x_2704_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2705_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2705_, 0, v___x_2704_);
lean_closure_set(v___x_2705_, 1, v___x_2703_);
return v___x_2705_;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__8(void){
_start:
{
lean_object* v___x_2706_; lean_object* v___f_2707_; lean_object* v___x_2708_; 
v___x_2706_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__7, &l_Lake_Toml_stdTable_parenthesizer___closed__7_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__7);
v___f_2707_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__3, &l_Lake_Toml_stdTable_parenthesizer___closed__3_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__3);
v___x_2708_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2708_, 0, v___f_2707_);
lean_closure_set(v___x_2708_, 1, v___x_2706_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer(lean_object* v_a_2709_, lean_object* v_a_2710_, lean_object* v_a_2711_, lean_object* v_a_2712_){
_start:
{
lean_object* v___x_2714_; lean_object* v___x_2715_; lean_object* v___x_2716_; uint8_t v___x_2717_; lean_object* v___x_2718_; 
v___x_2714_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__0));
v___x_2715_ = ((lean_object*)(l_Lake_Toml_stdTable___closed__1));
v___x_2716_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__8, &l_Lake_Toml_stdTable_parenthesizer___closed__8_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__8);
v___x_2717_ = 0;
v___x_2718_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2714_, v___x_2715_, v___x_2716_, v___x_2717_, v_a_2709_, v_a_2710_, v_a_2711_, v_a_2712_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer___boxed(lean_object* v_a_2719_, lean_object* v_a_2720_, lean_object* v_a_2721_, lean_object* v_a_2722_, lean_object* v_a_2723_){
_start:
{
lean_object* v_res_2724_; 
v_res_2724_ = l_Lake_Toml_stdTable_parenthesizer(v_a_2719_, v_a_2720_, v_a_2721_, v_a_2722_);
lean_dec(v_a_2722_);
lean_dec_ref(v_a_2721_);
lean_dec(v_a_2720_);
lean_dec_ref(v_a_2719_);
return v_res_2724_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__0(void){
_start:
{
lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___f_2727_; 
v___x_2725_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__1, &l_Lake_Toml_stdTable_parenthesizer___closed__1_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__1);
v___x_2726_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__0, &l_Lake_Toml_stdTable_parenthesizer___closed__0_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__0);
v___f_2727_ = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_parenthesizer___lam__0___boxed), 7, 2);
lean_closure_set(v___f_2727_, 0, v___x_2726_);
lean_closure_set(v___f_2727_, 1, v___x_2725_);
return v___f_2727_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__1(void){
_start:
{
lean_object* v___x_2728_; lean_object* v___x_2729_; 
v___x_2728_ = lean_obj_once(&l_Lake_Toml_stdTable_parenthesizer___closed__4, &l_Lake_Toml_stdTable_parenthesizer___closed__4_once, _init_l_Lake_Toml_stdTable_parenthesizer___closed__4);
v___x_2729_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2729_, 0, v___x_2728_);
lean_closure_set(v___x_2729_, 1, v___x_2728_);
return v___x_2729_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__2(void){
_start:
{
lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; 
v___x_2730_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__1, &l_Lake_Toml_arrayTable_parenthesizer___closed__1_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__1);
v___x_2731_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2732_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2732_, 0, v___x_2731_);
lean_closure_set(v___x_2732_, 1, v___x_2730_);
return v___x_2732_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__3(void){
_start:
{
lean_object* v___x_2733_; lean_object* v___x_2734_; lean_object* v___x_2735_; 
v___x_2733_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__2, &l_Lake_Toml_arrayTable_parenthesizer___closed__2_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__2);
v___x_2734_ = lean_alloc_closure((void*)(l_Lake_Toml_key_parenthesizer___boxed), 5, 0);
v___x_2735_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2735_, 0, v___x_2734_);
lean_closure_set(v___x_2735_, 1, v___x_2733_);
return v___x_2735_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__4(void){
_start:
{
lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; 
v___x_2736_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__3, &l_Lake_Toml_arrayTable_parenthesizer___closed__3_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__3);
v___x_2737_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
v___x_2738_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2738_, 0, v___x_2737_);
lean_closure_set(v___x_2738_, 1, v___x_2736_);
return v___x_2738_;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__5(void){
_start:
{
lean_object* v___x_2739_; lean_object* v___f_2740_; lean_object* v___x_2741_; 
v___x_2739_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__4, &l_Lake_Toml_arrayTable_parenthesizer___closed__4_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__4);
v___f_2740_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__0, &l_Lake_Toml_arrayTable_parenthesizer___closed__0_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__0);
v___x_2741_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2741_, 0, v___f_2740_);
lean_closure_set(v___x_2741_, 1, v___x_2739_);
return v___x_2741_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_parenthesizer(lean_object* v_a_2742_, lean_object* v_a_2743_, lean_object* v_a_2744_, lean_object* v_a_2745_){
_start:
{
lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2749_; uint8_t v___x_2750_; lean_object* v___x_2751_; 
v___x_2747_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__0));
v___x_2748_ = ((lean_object*)(l_Lake_Toml_arrayTable___closed__1));
v___x_2749_ = lean_obj_once(&l_Lake_Toml_arrayTable_parenthesizer___closed__5, &l_Lake_Toml_arrayTable_parenthesizer___closed__5_once, _init_l_Lake_Toml_arrayTable_parenthesizer___closed__5);
v___x_2750_ = 0;
v___x_2751_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2747_, v___x_2748_, v___x_2749_, v___x_2750_, v_a_2742_, v_a_2743_, v_a_2744_, v_a_2745_);
return v___x_2751_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_parenthesizer___boxed(lean_object* v_a_2752_, lean_object* v_a_2753_, lean_object* v_a_2754_, lean_object* v_a_2755_, lean_object* v_a_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_Lake_Toml_arrayTable_parenthesizer(v_a_2752_, v_a_2753_, v_a_2754_, v_a_2755_);
lean_dec(v_a_2755_);
lean_dec_ref(v_a_2754_);
lean_dec(v_a_2753_);
lean_dec_ref(v_a_2752_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_table_parenthesizer(lean_object* v_a_2758_, lean_object* v_a_2759_, lean_object* v_a_2760_, lean_object* v_a_2761_){
_start:
{
lean_object* v___x_2763_; lean_object* v___x_2764_; lean_object* v___x_2765_; 
v___x_2763_ = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_parenthesizer___boxed), 5, 0);
v___x_2764_ = lean_alloc_closure((void*)(l_Lake_Toml_arrayTable_parenthesizer___boxed), 5, 0);
v___x_2765_ = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(v___x_2763_, v___x_2764_, v_a_2758_, v_a_2759_, v_a_2760_, v_a_2761_);
return v___x_2765_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_table_parenthesizer___boxed(lean_object* v_a_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_, lean_object* v_a_2769_, lean_object* v_a_2770_){
_start:
{
lean_object* v_res_2771_; 
v_res_2771_ = l_Lake_Toml_table_parenthesizer(v_a_2766_, v_a_2767_, v_a_2768_, v_a_2769_);
lean_dec(v_a_2769_);
lean_dec_ref(v_a_2768_);
lean_dec(v_a_2767_);
lean_dec_ref(v_a_2766_);
return v_res_2771_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer(lean_object* v_val_2778_, lean_object* v_a_2779_, lean_object* v_a_2780_, lean_object* v_a_2781_, lean_object* v_a_2782_){
_start:
{
lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; 
v___x_2784_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___closed__0));
v___x_2785_ = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2785_, 0, v_val_2778_);
v___x_2786_ = lean_alloc_closure((void*)(l_Lake_Toml_table_parenthesizer___boxed), 5, 0);
v___x_2787_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2787_, 0, v___x_2785_);
lean_closure_set(v___x_2787_, 1, v___x_2786_);
v___x_2788_ = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(v___x_2784_, v___x_2787_, v_a_2779_, v_a_2780_, v_a_2781_, v_a_2782_);
return v___x_2788_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___boxed(lean_object* v_val_2789_, lean_object* v_a_2790_, lean_object* v_a_2791_, lean_object* v_a_2792_, lean_object* v_a_2793_, lean_object* v_a_2794_){
_start:
{
lean_object* v_res_2795_; 
v_res_2795_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer(v_val_2789_, v_a_2790_, v_a_2791_, v_a_2792_, v_a_2793_);
lean_dec(v_a_2793_);
lean_dec_ref(v_a_2792_);
lean_dec(v_a_2791_);
lean_dec_ref(v_a_2790_);
return v_res_2795_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer___redArg(){
_start:
{
lean_object* v___x_2797_; 
v___x_2797_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_2797_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer___redArg___boxed(lean_object* v_a_2798_){
_start:
{
lean_object* v_res_2799_; 
v_res_2799_ = l_Lake_Toml_trailingSep_parenthesizer___redArg();
return v_res_2799_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer(lean_object* v_a_2800_, lean_object* v_a_2801_, lean_object* v_a_2802_, lean_object* v_a_2803_){
_start:
{
lean_object* v___x_2805_; 
v___x_2805_ = l_Lake_Toml_epsilon_parenthesizer___redArg();
return v___x_2805_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer___boxed(lean_object* v_a_2806_, lean_object* v_a_2807_, lean_object* v_a_2808_, lean_object* v_a_2809_, lean_object* v_a_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_Lake_Toml_trailingSep_parenthesizer(v_a_2806_, v_a_2807_, v_a_2808_, v_a_2809_);
lean_dec(v_a_2809_);
lean_dec_ref(v_a_2808_);
lean_dec(v_a_2807_);
lean_dec_ref(v_a_2806_);
return v_res_2811_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(lean_object* v_val_2812_, lean_object* v_a_2813_, lean_object* v_a_2814_, lean_object* v_a_2815_, lean_object* v_a_2816_){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; lean_object* v___x_2823_; uint8_t v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2818_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0));
v___x_2819_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1));
v___x_2820_ = lean_alloc_closure((void*)(l_Lake_Toml_header_parenthesizer___boxed), 5, 0);
v___x_2821_ = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___boxed), 6, 1);
lean_closure_set(v___x_2821_, 0, v_val_2812_);
v___x_2822_ = lean_alloc_closure((void*)(l_Lake_Toml_trailingSep_parenthesizer___boxed), 5, 0);
v___x_2823_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2823_, 0, v___x_2821_);
lean_closure_set(v___x_2823_, 1, v___x_2822_);
v___x_2824_ = 1;
v___x_2825_ = lean_box(v___x_2824_);
v___x_2826_ = lean_alloc_closure((void*)(l_Lake_Toml_sepByLinebreak_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2826_, 0, v___x_2823_);
lean_closure_set(v___x_2826_, 1, v___x_2825_);
v___x_2827_ = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer___boxed), 7, 2);
lean_closure_set(v___x_2827_, 0, v___x_2820_);
lean_closure_set(v___x_2827_, 1, v___x_2826_);
v___x_2828_ = l_Lean_Parser_nodeWithAntiquot_parenthesizer(v___x_2818_, v___x_2819_, v___x_2827_, v___x_2824_, v_a_2813_, v_a_2814_, v_a_2815_, v_a_2816_);
return v___x_2828_;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer___boxed(lean_object* v_val_2829_, lean_object* v_a_2830_, lean_object* v_a_2831_, lean_object* v_a_2832_, lean_object* v_a_2833_, lean_object* v_a_2834_){
_start:
{
lean_object* v_res_2835_; 
v_res_2835_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(v_val_2829_, v_a_2830_, v_a_2831_, v_a_2832_, v_a_2833_);
lean_dec(v_a_2833_);
lean_dec_ref(v_a_2832_);
lean_dec(v_a_2831_);
lean_dec_ref(v_a_2830_);
return v_res_2835_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_val_parenthesizer(lean_object* v_a_2836_, lean_object* v_a_2837_, lean_object* v_a_2838_, lean_object* v_a_2839_){
_start:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; uint8_t v___x_2844_; lean_object* v___x_2845_; 
v___x_2841_ = ((lean_object*)(l_Lake_Toml_val___closed__0));
v___x_2842_ = ((lean_object*)(l_Lake_Toml_val___closed__1));
v___x_2843_ = ((lean_object*)(l_Lake_Toml_val___closed__2));
v___x_2844_ = 1;
v___x_2845_ = l_Lake_Toml_recNodeWithAntiquot_parenthesizer(v___x_2841_, v___x_2842_, v___x_2843_, v___x_2844_, v_a_2836_, v_a_2837_, v_a_2838_, v_a_2839_);
return v___x_2845_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_val_parenthesizer___boxed(lean_object* v_a_2846_, lean_object* v_a_2847_, lean_object* v_a_2848_, lean_object* v_a_2849_, lean_object* v_a_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l_Lake_Toml_val_parenthesizer(v_a_2846_, v_a_2847_, v_a_2848_, v_a_2849_);
lean_dec(v_a_2849_);
lean_dec_ref(v_a_2848_);
lean_dec(v_a_2847_);
lean_dec_ref(v_a_2846_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_toml_parenthesizer(lean_object* v_a_2852_, lean_object* v_a_2853_, lean_object* v_a_2854_, lean_object* v_a_2855_){
_start:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; 
v___x_2857_ = lean_alloc_closure((void*)(l_Lake_Toml_val_parenthesizer___boxed), 5, 0);
v___x_2858_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(v___x_2857_, v_a_2852_, v_a_2853_, v_a_2854_, v_a_2855_);
return v___x_2858_;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_toml_parenthesizer___boxed(lean_object* v_a_2859_, lean_object* v_a_2860_, lean_object* v_a_2861_, lean_object* v_a_2862_, lean_object* v_a_2863_){
_start:
{
lean_object* v_res_2864_; 
v_res_2864_ = l_Lake_Toml_toml_parenthesizer(v_a_2859_, v_a_2860_, v_a_2861_, v_a_2862_);
lean_dec(v_a_2862_);
lean_dec_ref(v_a_2861_);
lean_dec(v_a_2860_);
lean_dec_ref(v_a_2859_);
return v_res_2864_;
}
}
static lean_object* _init_l_Lake_Toml_toml___closed__0(void){
_start:
{
lean_object* v___x_2865_; lean_object* v___x_2866_; 
v___x_2865_ = l_Lake_Toml_val;
v___x_2866_ = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore(v___x_2865_);
return v___x_2866_;
}
}
static lean_object* _init_l_Lake_Toml_toml___closed__1(void){
_start:
{
lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
v___x_2867_ = lean_obj_once(&l_Lake_Toml_toml___closed__0, &l_Lake_Toml_toml___closed__0_once, _init_l_Lake_Toml_toml___closed__0);
v___x_2868_ = ((lean_object*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1));
v___x_2869_ = l_Lean_Parser_withCache(v___x_2868_, v___x_2867_);
return v___x_2869_;
}
}
static lean_object* _init_l_Lake_Toml_toml(void){
_start:
{
lean_object* v___x_2870_; 
v___x_2870_ = lean_obj_once(&l_Lake_Toml_toml___closed__1, &l_Lake_Toml_toml___closed__1_once, _init_l_Lake_Toml_toml___closed__1);
return v___x_2870_;
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
