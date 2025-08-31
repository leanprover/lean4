// Lean compiler output
// Module: Lake.Toml.Grammar
// Imports: Lean.Parser.Types Lake.Toml.ParserUtil Lean.Parser
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
static lean_object* l_Lake_Toml_stdTable_formatter___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_boolean;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__3;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__0;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_sepByLinebreak_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_string___closed__3;
lean_object* l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_unquotedKeyFn___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_binNum;
static lean_object* l_Lake_Toml_string___closed__6;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_stdTable_parenthesizer___closed__0;
static lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlBasicStringFn_spec__0___closed__0;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__6;
static lean_object* l_Lake_Toml_key___closed__11;
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_stdTable___closed__13;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7;
extern lean_object* l_Lean_Parser_pushNone;
lean_object* l_Lake_Toml_sepByLinebreak_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___closed__0;
static lean_object* l_Lake_Toml_hexNum___closed__0;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1___boxed(lean_object*, lean_object*);
lean_object* l_Lake_Toml_litWithAntiquot_formatter___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_header;
static lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlLiteralStringFn_spec__0___closed__1;
lean_object* l_Lake_Toml_dynamicNode(lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_numeralAntiquot___closed__8;
static lean_object* l_Lake_Toml_arrayTable___closed__2;
static lean_object* l_Lake_Toml_stdTable___closed__17;
static lean_object* l_Lake_Toml_mlBasicString___closed__2;
static lean_object* l_Lake_Toml_true___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_stdTable___closed__14;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__1;
static lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_dateTimeFn_spec__0___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_basicString___closed__2;
LEAN_EXPORT lean_object* l_Lake_Toml_header_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_arrayTable___closed__5;
lean_object* l_Lean_PrettyPrinter_Formatter_orelse_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_stdTable___closed__9;
static lean_object* l_Lake_Toml_numeralAntiquot___closed__9;
LEAN_EXPORT lean_object* l_Lake_Toml_val_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable;
static lean_object* l_Lake_Toml_float___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at_____private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_val___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6;
static lean_object* l_Lake_Toml_arrayTable_formatter___closed__6;
LEAN_EXPORT lean_object* l_Lake_Toml_inlineTable;
static lean_object* l_Lake_Toml_trailingSep___closed__0;
lean_object* l_Lake_Toml_chFn(uint32_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_key___closed__13;
LEAN_EXPORT lean_object* l_Lake_Toml_keyval;
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicString;
static lean_object* l_Lake_Toml_numeralAntiquot___closed__1;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14;
LEAN_EXPORT lean_object* l_Lake_Toml_val_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_val___closed__2;
static lean_object* l_Lake_Toml_timeFn___closed__0;
static lean_object* l_Lake_Toml_numeralFn___lam__0___closed__14;
static lean_object* l_Lake_Toml_mlLiteralString___closed__2;
lean_object* l_Lake_Toml_isHexDigit___boxed(lean_object*);
static lean_object* l_Lake_Toml_stdTable___closed__12;
static lean_object* l_Lake_Toml_key_parenthesizer___closed__0;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4;
static lean_object* l_Lake_Toml_arrayTable___closed__9;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_numeralAntiquot;
static lean_object* l_Lake_Toml_numeralFn___lam__0___closed__16;
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicStringFn___lam__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_stdTable___closed__19;
lean_object* l_Lake_Toml_isBinDigit___boxed(lean_object*);
static lean_object* l_Lake_Toml_arrayTable_parenthesizer___closed__0;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_unquotedKey___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_numeral;
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_key___closed__5;
static lean_object* l_Lake_Toml_numeralFn___lam__0___closed__7;
static lean_object* l_Lake_Toml_stdTable___closed__15;
static lean_object* l_Lake_Toml_numeralFn___lam__0___closed__4;
static lean_object* l_Lake_Toml_stdTable___closed__5;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2;
static lean_object* l_Lake_Toml_numeralFn___lam__0___closed__15;
static lean_object* l_Lake_Toml_numeralFn___lam__0___closed__12;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn___closed__0;
lean_object* l_Lean_Parser_ParserState_mkUnexpectedError(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lake_Toml_stdTable___closed__20;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__1;
lean_object* l_Lean_Parser_checkLinebreakBefore(lean_object*);
static lean_object* l_Lake_Toml_true___closed__5;
static lean_object* l_Lake_Toml_simpleKey___closed__1;
static lean_object* l_Lake_Toml_stdTable___closed__10;
static lean_object* l_Lake_Toml_arrayTable_parenthesizer___closed__2;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__0;
lean_object* l_Lake_Toml_takeWhile1Fn(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_stdTable_parenthesizer___closed__3;
static lean_object* l_Lake_Toml_stdTable_parenthesizer___closed__1;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__0;
static lean_object* l_Lake_Toml_key_formatter___closed__1;
static lean_object* l_Lake_Toml_false___closed__3;
lean_object* l_Lean_Parser_ParserState_next_x27___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_orelse(lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5;
static lean_object* l_Lake_Toml_stdTable___closed__1;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__2;
static lean_object* l_Lake_Toml_arrayTable_formatter___closed__2;
static lean_object* l_Lake_Toml_boolean___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_toml_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_restore(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_key;
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralString;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decimalFn(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
static lean_object* l_Lake_Toml_arrayTable___closed__7;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__7;
lean_object* l_Lean_Parser_setExpected(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_false;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__4;
static lean_object* l_Lake_Toml_stdTable___closed__2;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__7;
LEAN_EXPORT lean_object* l_Lake_Toml_trailingFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_numeralAntiquot___closed__13;
static lean_object* l_Lake_Toml_stdTable___closed__8;
static lean_object* l_Lake_Toml_table___closed__0;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5;
static lean_object* l_Lake_Toml_numeralFn___lam__0___closed__11;
static lean_object* l_Lake_Toml_unquotedKeyFn___closed__0;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__1;
static lean_object* l_Lake_Toml_simpleKey___closed__3;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralStringFn___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_wsFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_key_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_toml;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9;
lean_object* l_Lean_Parser_ParserState_stackSize(lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__1;
lean_object* l_Lake_Toml_digitPairFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_timeFn(uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_trailingSep___closed__1;
static lean_object* l_Lake_Toml_stdTable_parenthesizer___closed__2;
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepByNoAntiquot(lean_object*, lean_object*, uint8_t);
static lean_object* l_Lake_Toml_numeralFn___lam__0___closed__0;
lean_object* lean_string_push(lean_object*, uint32_t);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_key_parenthesizer___closed__1;
static lean_object* l_Lake_Toml_arrayTable_formatter___closed__0;
static lean_object* l_Lake_Toml_newlineFn___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_numeralOfKind___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_numeralFn___lam__0___closed__10;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15;
static lean_object* l_Lake_Toml_unquotedKey___closed__1;
static lean_object* l_Lake_Toml_key_parenthesizer___closed__0___boxed__const__1;
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at_____private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_string___closed__2;
LEAN_EXPORT lean_object* l_Lake_Toml_dateTimeFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_stdTable___closed__4;
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_header___closed__0;
static lean_object* l_Lake_Toml_string___closed__7;
static lean_object* l_Lake_Toml_stdTable_formatter___closed__1;
uint8_t l_Lean_Parser_beqError____x40_Lean_Parser_Types_2111619821____hygCtx___hyg_42_(lean_object*, lean_object*);
lean_object* l_Lean_Parser_mkAntiquot_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_numeralFn___lam__0___closed__13;
static lean_object* l_Lake_Toml_array___closed__0;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0;
static lean_object* l_Lake_Toml_arrayTable___closed__6;
LEAN_EXPORT lean_object* l_Lake_Toml_trailingFn(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_key_formatter___closed__2;
static lean_object* l_Lake_Toml_numeralFn___lam__0___closed__2;
LEAN_EXPORT lean_object* l_Lake_Toml_timeFn___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_numeral___closed__0;
static lean_object* l_Lake_Toml_binNum___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_true;
static lean_object* l_Lake_Toml_numeralOfKind___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_literalString;
lean_object* l_Lake_Toml_recNodeWithAntiquot_formatter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9;
static lean_object* l_Lake_Toml_simpleKey___closed__2;
static lean_object* l_Lake_Toml_mlLiteralString___closed__0;
static lean_object* l_Lake_Toml_numeralFn___lam__0___closed__9;
LEAN_EXPORT uint8_t l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0(uint32_t);
static lean_object* l_Lake_Toml_stdTable_formatter___closed__6;
static lean_object* l_Lake_Toml_numeralAntiquot___closed__7;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__2;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10;
uint8_t l_Lean_Parser_InputContext_atEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlBasicStringFn_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_newlineFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_valCore(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_isEscapeChar___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_key___closed__4;
LEAN_EXPORT uint8_t l_Lake_Toml_isControlChar(uint32_t);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
static lean_object* l_Lake_Toml_mlBasicString___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_commentFn___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_arrayTable_parenthesizer___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__0;
static lean_object* l_Lake_Toml_stdTable___closed__0;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3;
static lean_object* l_Lake_Toml_stdTable___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_basicStringFn(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_stdTable_parenthesizer___closed__4;
static lean_object* l_Lake_Toml_numeralAntiquot___closed__2;
static lean_object* l_Lake_Toml_key___closed__10;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_numeralAntiquot___closed__6;
static lean_object* l_Lake_Toml_key_parenthesizer___closed__2;
static lean_object* l_Lake_Toml_basicString___closed__1;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___closed__0;
static lean_object* l_Lake_Toml_simpleKey___closed__0;
static lean_object* l_Lake_Toml_keyval___closed__0;
lean_object* l_Lake_Toml_mkUnexpectedCharError(lean_object*, uint32_t, lean_object*, uint8_t);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11;
LEAN_EXPORT lean_object* l_Lake_Toml_decInt;
static lean_object* l_Lake_Toml_arrayTable___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_digitFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_wsFn___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_numeralAntiquot___closed__11;
static lean_object* l_Lake_Toml_numeral___closed__1;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_isOctDigit___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy1(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lake_Toml_stdTable___closed__23;
lean_object* l_Lean_Parser_notFollowedBy(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_trailingWs___closed__0;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__5;
lean_object* l_Lean_Parser_symbol(lean_object*);
static lean_object* l_Lake_Toml_literalStringFn___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
static lean_object* l_Lake_Toml_numeralFn___lam__0___closed__3;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_key___closed__7;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_arrayTable___closed__0;
lean_object* l_Lake_Toml_recNodeWithAntiquot(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs;
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlLiteralStringFn_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_val___closed__3;
static lean_object* l_Lake_Toml_key_formatter___closed__3;
static lean_object* l_Lake_Toml_numeralAntiquot___closed__12;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_inlineTable___closed__0;
lean_object* l_Lean_Parser_takeUntilFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_numeralAntiquot___closed__0;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0;
lean_object* l_Lean_Parser_withAntiquot(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_literalString___closed__2;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_string___closed__0;
static lean_object* l_Lake_Toml_val___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_numeralFn___lam__0(lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicStringFn(lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__0;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__3;
static lean_object* l_Lake_Toml_literalString___closed__0;
static lean_object* l_Lake_Toml_basicStringFn___closed__1;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__8;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_epsilon_parenthesizer___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_array;
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_dateTimeFn_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_simpleKey_parenthesizer___closed__0;
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_nodeWithAntiquot(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6;
LEAN_EXPORT lean_object* l_Lake_Toml_toml_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_commentFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_table_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_key___closed__0;
static lean_object* l_Lake_Toml_dateTime___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_table_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2;
static lean_object* l_Lake_Toml_binNum___closed__0;
static lean_object* l_Lake_Toml_numeralFn___lam__0___closed__6;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__2;
static lean_object* l_Lake_Toml_numeralAntiquot___closed__4;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_string___closed__5;
static lean_object* l_Lake_Toml_numeralFn___lam__0___closed__5;
static lean_object* l_Lake_Toml_arrayTable___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_true___closed__4;
LEAN_EXPORT lean_object* l_Lake_Toml_isControlChar___boxed(lean_object*);
static lean_object* l_Lake_Toml_unquotedKey___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6;
static lean_object* l_Lake_Toml_key___closed__12;
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn___lam__0___boxed(lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__4;
lean_object* l_Lean_Parser_andthen(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_stdTable_parenthesizer___closed__5;
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_key___closed__1;
static lean_object* l_Lake_Toml_octNum___closed__1;
lean_object* l_Lake_Toml_skipFn___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Parser_setExpected_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_epsilon_formatter___redArg(lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__2;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__6;
lean_object* l_Lake_Toml_strFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep;
static lean_object* l_Lake_Toml_literalString___closed__1;
lean_object* l_Lean_Parser_atomic(lean_object*);
lean_object* l_Lean_Parser_nodeWithAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_numeralOfKind___lam__0(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_expression___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___boxed(lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0___boxed__const__1;
lean_object* l_Lake_Toml_sepByChar1AuxFn(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__4;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0;
static lean_object* l_Lake_Toml_true___closed__1;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1;
static lean_object* l_Lake_Toml_timeFn___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_basicStringFn___closed__0;
static lean_object* l_Lake_Toml_arrayTable_formatter___closed__1;
static lean_object* l_Lake_Toml_stdTable_formatter___closed__1___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_Toml_key_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_stdTable_formatter___closed__5;
static lean_object* l_Lake_Toml_stdTable_formatter___closed__9;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_stdTable_formatter___closed__4;
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_newlineFn___closed__1;
static lean_object* l_Lake_Toml_key___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_simpleKey_formatter___closed__0;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__1;
static lean_object* l_Lake_Toml_arrayTable___closed__8;
lean_object* l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4;
static lean_object* l_Lake_Toml_arrayTable___closed__4;
LEAN_EXPORT lean_object* l_Lake_Toml_numeralFn(lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3;
lean_object* l_Lean_Parser_sepBy1_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_true___closed__3;
static lean_object* l_Lake_Toml_arrayTable_parenthesizer___closed__1;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4;
static lean_object* l_Lake_Toml_false___closed__2;
LEAN_EXPORT lean_object* l_Lake_Toml_wsNewlineFn(lean_object*, lean_object*);
lean_object* l_Lean_Parser_ParserState_setPos(lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_numeralOfKind(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_mlBasicString___closed__0;
static lean_object* l_Lake_Toml_arrayTable_formatter___closed__5;
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withCache(lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5;
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
static lean_object* l_Lake_Toml_boolean___closed__1;
lean_object* l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_atomic_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_key_formatter___closed__4;
static lean_object* l_Lake_Toml_string___closed__4;
static lean_object* l_Lake_Toml_stdTable___closed__21;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn(uint8_t, uint32_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_withAntiquotSpliceAndSuffix(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter___redArg(lean_object*);
lean_object* l_Lean_Parser_ParserState_mkEOIError(lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1;
static lean_object* l_Lake_Toml_stdTable___closed__18;
static lean_object* l_Lake_Toml_false___closed__1;
static lean_object* l_Lake_Toml_stdTable_formatter___closed__0;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0;
static lean_object* l_Lake_Toml_commentFn___closed__1;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
static lean_object* l_Lake_Toml_toml___closed__1;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0;
lean_object* l_Lean_Parser_checkStackTop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(uint8_t, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_stdTable_parenthesizer___closed__3___boxed__const__1;
static lean_object* l_Lake_Toml_literalStringFn___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_key_formatter___closed__0;
static lean_object* l_Lake_Toml_boolean___closed__2;
static lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlLiteralStringFn_spec__0___closed__0;
lean_object* l_Lake_Toml_litWithAntiquot(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l_Lake_Toml_key___closed__9;
LEAN_EXPORT lean_object* l_Lake_Toml_commentFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_false___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_key___closed__2;
lean_object* lean_nat_sub(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable;
static lean_object* l_Lake_Toml_false___closed__5;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0___boxed(lean_object*);
static lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlBasicStringFn_spec__0___closed__1;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5;
static lean_object* l_Lake_Toml_true___closed__2;
LEAN_EXPORT lean_object* l_Lake_Toml_octNum;
LEAN_EXPORT uint8_t l_Lake_Toml_wsFn___lam__0(uint32_t);
static lean_object* l_Lake_Toml_quotedKey___closed__0;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6;
lean_object* l_Lake_Toml_chAtom_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicStringFn___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2;
lean_object* l_Lake_Toml_chAtom(uint32_t, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_key___closed__8;
static lean_object* l_Lake_Toml_header___closed__1;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Formatter_andthen_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_setExpected_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__3;
lean_object* l_Lean_Parser_atomicFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_sepBy(lean_object*, lean_object*, lean_object*, uint8_t);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_dateTime;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_string;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(lean_object*);
static lean_object* l_Lake_Toml_decInt___closed__0;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__1;
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1;
lean_object* l_Lake_Toml_trailing(lean_object*);
static lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_dateTimeFn_spec__0___closed__1;
static lean_object* l_Lake_Toml_numeralFn___lam__0___closed__1;
lean_object* l_Lake_Toml_pushLit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_numeralAntiquot___closed__14;
lean_object* l_Lean_Parser_sepBy1_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_chAtom_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_stdTable_formatter___closed__2;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__9;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0;
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralStringFn___lam__0___boxed(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_lt(uint32_t, uint32_t);
lean_object* l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_isEscapeChar(uint32_t);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter___redArg(lean_object*);
static lean_object* l_Lake_Toml_stdTable_parenthesizer___closed__6;
LEAN_EXPORT lean_object* l_Lake_Toml_table;
lean_object* l_Lean_Parser_mkAntiquot(lean_object*, lean_object*, uint8_t, uint8_t);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2;
static lean_object* l_Lake_Toml_stdTable___closed__22;
lean_object* l_Lean_Parser_nodeWithAntiquot_formatter(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_stdTable___closed__11;
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlLiteralStringFn_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey;
static lean_object* l_Lake_Toml_key___closed__6;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static lean_object* l_Lake_Toml_basicString___closed__0;
static lean_object* l_Lake_Toml_key_parenthesizer___closed__3;
static lean_object* l_Lake_Toml_arrayTable_parenthesizer___closed__4;
lean_object* l_Lean_Parser_takeWhileFn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_octNum___closed__0;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralStringFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_val;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8;
lean_object* lean_string_append(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_numeralFn___lam__0___closed__8;
LEAN_EXPORT lean_object* l_Lake_Toml_literalStringFn(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_header___closed__2;
static lean_object* l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1;
static lean_object* l_Lake_Toml_numeralAntiquot___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_hexNum___closed__1;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__2;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__0;
static lean_object* l_Lake_Toml_arrayTable_parenthesizer___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_header_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_sepByChar1Fn(lean_object*, uint32_t, lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_numeralFn___lam__0___closed__17;
static lean_object* l_Lake_Toml_stdTable___closed__7;
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_dateTimeFn_spec__0(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_stdTable_parenthesizer___closed__0___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_Toml_basicString;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2;
LEAN_EXPORT lean_object* l_Lake_Toml_wsNewlineFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn(lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___closed__0;
lean_object* l_Lean_Parser_hexDigitFn(lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__1;
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_literalStringFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_dateTimeFn(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_string___closed__1;
static lean_object* l_Lake_Toml_arrayTable_formatter___closed__4;
static lean_object* l_Lake_Toml_false___closed__4;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_expression;
lean_object* l_Lean_Parser_ParserState_mkUnexpectedErrorAt(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_arrayTable_formatter___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey;
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey;
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lake_Toml_lit(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_stdTable_parenthesizer___closed__1___boxed__const__1;
LEAN_EXPORT lean_object* l_Lake_Toml_wsFn(lean_object*, lean_object*);
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__0;
LEAN_EXPORT uint8_t l_Lake_Toml_unquotedKeyFn___lam__0(uint32_t);
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_formatter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_newlineFn___boxed(lean_object*, lean_object*);
static lean_object* l_Lake_Toml_key_parenthesizer___closed__4;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5;
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lake_Toml_float;
static lean_object* l_Lake_Toml_toml___closed__0;
static lean_object* l_Lake_Toml_stdTable_formatter___closed__7;
static lean_object* l_Lake_Toml_key_formatter___closed__0___boxed__const__1;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3;
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer___redArg(lean_object*);
static lean_object* l_Lake_Toml_stdTable___closed__6;
static lean_object* l_Lake_Toml_stdTable___closed__16;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___closed__0;
static lean_object* l_Lake_Toml_stdTable_formatter___closed__8;
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(lean_object*);
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlBasicStringFn_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static lean_object* l_Lake_Toml_mlLiteralString___closed__1;
LEAN_EXPORT lean_object* l_Lake_Toml_hexNum;
static lean_object* l_Lake_Toml_numeralAntiquot___closed__5;
static lean_object* l_Lake_Toml_numeralAntiquot___closed__10;
static lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__8;
static lean_object* l_Lake_Toml_boolean___closed__0;
lean_object* l_Lake_Toml_recNodeWithAntiquot_parenthesizer(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lake_Toml_isControlChar(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 127;
x_3 = lean_uint32_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 32;
x_5 = lean_uint32_dec_lt(x_1, x_4);
if (x_5 == 0)
{
return x_5;
}
else
{
uint32_t x_6; uint8_t x_7; 
x_6 = 9;
x_7 = lean_uint32_dec_eq(x_1, x_6);
if (x_7 == 0)
{
return x_5;
}
else
{
return x_3;
}
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_isControlChar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lake_Toml_isControlChar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_wsFn___lam__0(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 32;
x_3 = lean_uint32_dec_eq(x_1, x_2);
if (x_3 == 0)
{
uint32_t x_4; uint8_t x_5; 
x_4 = 9;
x_5 = lean_uint32_dec_eq(x_1, x_4);
return x_5;
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_wsFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lake_Toml_wsFn___lam__0___boxed), 1, 0);
x_4 = l_Lean_Parser_takeWhileFn(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_wsFn___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lake_Toml_wsFn___lam__0(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_wsFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_wsFn(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid newline; no LF after CR", 31, 31);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; uint8_t x_7; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 2);
x_5 = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___closed__0;
x_6 = l_Lean_Parser_InputContext_atEnd(x_3, x_4);
x_7 = 1;
if (x_6 == 0)
{
lean_object* x_8; uint32_t x_9; uint32_t x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_3, 0);
x_9 = lean_string_utf8_get_fast(x_8, x_4);
x_10 = 10;
x_11 = lean_uint32_dec_eq(x_9, x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_box(0);
x_13 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_5, x_12, x_7);
return x_13;
}
else
{
lean_object* x_14; 
lean_inc(x_4);
x_14 = l_Lean_Parser_ParserState_next_x27___redArg(x_2, x_1, x_4);
lean_dec(x_4);
return x_14;
}
}
else
{
lean_object* x_15; lean_object* x_16; 
x_15 = lean_box(0);
x_16 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_5, x_15, x_7);
return x_16;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_newlineFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("newline", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_newlineFn___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_newlineFn___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_newlineFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 2);
x_5 = l_Lean_Parser_InputContext_atEnd(x_3, x_4);
if (x_5 == 0)
{
lean_object* x_6; uint32_t x_7; uint32_t x_8; uint8_t x_9; 
x_6 = lean_ctor_get(x_3, 0);
x_7 = lean_string_utf8_get_fast(x_6, x_4);
x_8 = 10;
x_9 = lean_uint32_dec_eq(x_7, x_8);
if (x_9 == 0)
{
uint32_t x_10; uint8_t x_11; 
x_10 = 13;
x_11 = lean_uint32_dec_eq(x_7, x_10);
if (x_11 == 0)
{
uint8_t x_12; lean_object* x_13; lean_object* x_14; 
x_12 = 1;
x_13 = l_Lake_Toml_newlineFn___closed__1;
x_14 = l_Lake_Toml_mkUnexpectedCharError(x_2, x_7, x_13, x_12);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; 
lean_inc(x_4);
x_15 = l_Lean_Parser_ParserState_next_x27___redArg(x_2, x_1, x_4);
lean_dec(x_4);
x_16 = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(x_1, x_15);
return x_16;
}
}
else
{
lean_object* x_17; 
lean_inc(x_4);
x_17 = l_Lean_Parser_ParserState_next_x27___redArg(x_2, x_1, x_4);
lean_dec(x_4);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; 
x_18 = l_Lake_Toml_newlineFn___closed__1;
x_19 = l_Lean_Parser_ParserState_mkEOIError(x_2, x_18);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_newlineFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_newlineFn(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_isControlChar___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___closed__0;
x_4 = l_Lean_Parser_takeUntilFn(x_3, x_1, x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_3; 
x_3 = 1;
return x_3;
}
else
{
uint8_t x_4; 
lean_dec_ref(x_2);
x_4 = 0;
return x_4;
}
}
else
{
if (lean_obj_tag(x_2) == 0)
{
uint8_t x_5; 
lean_dec_ref(x_1);
x_5 = 0;
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
lean_dec_ref(x_1);
x_7 = lean_ctor_get(x_2, 0);
lean_inc(x_7);
lean_dec_ref(x_2);
x_8 = l_Lean_Parser_beqError____x40_Lean_Parser_Types_2111619821____hygCtx___hyg_42_(x_6, x_7);
return x_8;
}
}
}
}
static lean_object* _init_l_Lake_Toml_commentFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("comment", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_commentFn___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_commentFn___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_commentFn(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = 35;
x_4 = l_Lake_Toml_commentFn___closed__1;
x_5 = l_Lake_Toml_chFn(x_3, x_4, x_1, x_2);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_6, x_7);
if (x_8 == 0)
{
return x_5;
}
else
{
lean_object* x_9; 
x_9 = l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(x_1, x_5);
return x_9;
}
}
}
LEAN_EXPORT lean_object* l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_1, x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_commentFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_commentFn(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_wsNewlineFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 2);
x_8 = l_Lean_Parser_InputContext_atEnd(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; uint32_t x_10; uint8_t x_11; uint32_t x_23; uint8_t x_24; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_string_utf8_get_fast(x_9, x_4);
x_23 = 32;
x_24 = lean_uint32_dec_eq(x_10, x_23);
if (x_24 == 0)
{
uint32_t x_25; uint8_t x_26; 
x_25 = 9;
x_26 = lean_uint32_dec_eq(x_10, x_25);
x_11 = x_26;
goto block_22;
}
else
{
x_11 = x_24;
goto block_22;
}
block_22:
{
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 10;
x_13 = lean_uint32_dec_eq(x_10, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 13;
x_15 = lean_uint32_dec_eq(x_10, x_14);
if (x_15 == 0)
{
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
lean_inc(x_4);
x_16 = l_Lean_Parser_ParserState_next_x27___redArg(x_2, x_1, x_4);
lean_dec(x_4);
x_17 = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(x_1, x_16);
x_18 = lean_ctor_get(x_17, 4);
lean_inc(x_18);
x_19 = lean_box(0);
x_20 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_18, x_19);
if (x_20 == 0)
{
return x_17;
}
else
{
x_2 = x_17;
goto _start;
}
}
}
else
{
lean_inc(x_4);
goto block_7;
}
}
else
{
lean_inc(x_4);
goto block_7;
}
}
}
else
{
return x_2;
}
block_7:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_ParserState_next_x27___redArg(x_2, x_1, x_4);
lean_dec(x_4);
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_wsNewlineFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_wsNewlineFn(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 2);
x_8 = l_Lean_Parser_InputContext_atEnd(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; uint32_t x_10; uint8_t x_11; uint32_t x_31; uint8_t x_32; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_string_utf8_get_fast(x_9, x_4);
x_31 = 32;
x_32 = lean_uint32_dec_eq(x_10, x_31);
if (x_32 == 0)
{
uint32_t x_33; uint8_t x_34; 
x_33 = 9;
x_34 = lean_uint32_dec_eq(x_10, x_33);
x_11 = x_34;
goto block_30;
}
else
{
x_11 = x_32;
goto block_30;
}
block_30:
{
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 10;
x_13 = lean_uint32_dec_eq(x_10, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 13;
x_15 = lean_uint32_dec_eq(x_10, x_14);
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; 
x_16 = 35;
x_17 = lean_uint32_dec_eq(x_10, x_16);
if (x_17 == 0)
{
return x_2;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_inc(x_4);
x_18 = l_Lean_Parser_ParserState_next_x27___redArg(x_2, x_1, x_4);
lean_dec(x_4);
x_19 = l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn(x_1, x_18);
x_20 = lean_ctor_get(x_19, 4);
lean_inc(x_20);
x_21 = lean_box(0);
x_22 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_20, x_21);
if (x_22 == 0)
{
return x_19;
}
else
{
x_2 = x_19;
goto _start;
}
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; 
lean_inc(x_4);
x_24 = l_Lean_Parser_ParserState_next_x27___redArg(x_2, x_1, x_4);
lean_dec(x_4);
x_25 = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(x_1, x_24);
x_26 = lean_ctor_get(x_25, 4);
lean_inc(x_26);
x_27 = lean_box(0);
x_28 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_26, x_27);
if (x_28 == 0)
{
return x_25;
}
else
{
x_2 = x_25;
goto _start;
}
}
}
else
{
lean_inc(x_4);
goto block_7;
}
}
else
{
lean_inc(x_4);
goto block_7;
}
}
}
else
{
return x_2;
}
block_7:
{
lean_object* x_5; 
x_5 = l_Lean_Parser_ParserState_next_x27___redArg(x_2, x_1, x_4);
lean_dec(x_4);
x_2 = x_5;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_trailingFn(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_isEscapeChar(uint32_t x_1) {
_start:
{
uint8_t x_2; uint32_t x_14; uint8_t x_15; 
x_14 = 98;
x_15 = lean_uint32_dec_eq(x_1, x_14);
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; 
x_16 = 116;
x_17 = lean_uint32_dec_eq(x_1, x_16);
x_2 = x_17;
goto block_13;
}
else
{
x_2 = x_15;
goto block_13;
}
block_13:
{
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = 110;
x_4 = lean_uint32_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 102;
x_6 = lean_uint32_dec_eq(x_1, x_5);
if (x_6 == 0)
{
uint32_t x_7; uint8_t x_8; 
x_7 = 114;
x_8 = lean_uint32_dec_eq(x_1, x_7);
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 34;
x_10 = lean_uint32_dec_eq(x_1, x_9);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 92;
x_12 = lean_uint32_dec_eq(x_1, x_11);
return x_12;
}
else
{
return x_10;
}
}
else
{
return x_8;
}
}
else
{
return x_6;
}
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_isEscapeChar___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lake_Toml_isEscapeChar(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at_____private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 1)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_6 = l_Lean_Parser_hexDigitFn(x_1, x_3);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_7, x_8);
if (x_9 == 0)
{
lean_dec(x_2);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = lean_nat_sub(x_2, x_10);
lean_dec(x_2);
x_2 = x_11;
x_3 = x_6;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l_Lake_Toml_wsFn(x_1, x_2);
x_4 = lean_ctor_get(x_3, 4);
lean_inc(x_4);
x_5 = lean_box(0);
x_6 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_4, x_5);
if (x_6 == 0)
{
return x_3;
}
else
{
lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_7 = l_Lake_Toml_newlineFn(x_1, x_3);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_8, x_5);
if (x_9 == 0)
{
return x_7;
}
else
{
lean_object* x_10; 
x_10 = l_Lake_Toml_wsNewlineFn(x_1, x_7);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(x_1, x_2);
x_4 = lean_ctor_get(x_3, 4);
lean_inc(x_4);
x_5 = lean_box(0);
x_6 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_4, x_5);
if (x_6 == 0)
{
return x_3;
}
else
{
lean_object* x_7; 
x_7 = l_Lake_Toml_wsNewlineFn(x_1, x_3);
return x_7;
}
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("escape sequence", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("string gap is forbidden here", 28, 28);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("invalid escape sequence", 23, 23);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_wsNewlineFn___boxed), 2, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_3, 2);
x_6 = lean_box(0);
x_7 = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__1;
x_8 = l_Lean_Parser_InputContext_atEnd(x_4, x_5);
if (x_8 == 0)
{
lean_object* x_9; uint32_t x_10; uint8_t x_11; 
x_9 = lean_ctor_get(x_4, 0);
x_10 = lean_string_utf8_get_fast(x_9, x_5);
x_11 = l_Lake_Toml_isEscapeChar(x_10);
if (x_11 == 0)
{
uint32_t x_12; uint8_t x_13; 
x_12 = 117;
x_13 = lean_uint32_dec_eq(x_10, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 85;
x_15 = lean_uint32_dec_eq(x_10, x_14);
if (x_15 == 0)
{
lean_object* x_16; uint8_t x_17; lean_object* x_18; uint32_t x_24; uint8_t x_25; 
x_16 = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0___boxed), 2, 0);
x_17 = 1;
x_24 = 32;
x_25 = lean_uint32_dec_eq(x_10, x_24);
if (x_25 == 0)
{
uint32_t x_26; uint8_t x_27; 
x_26 = 9;
x_27 = lean_uint32_dec_eq(x_10, x_26);
if (x_27 == 0)
{
uint32_t x_28; uint8_t x_29; 
lean_dec_ref(x_16);
x_28 = 10;
x_29 = lean_uint32_dec_eq(x_10, x_28);
if (x_29 == 0)
{
uint32_t x_30; uint8_t x_31; 
x_30 = 13;
x_31 = lean_uint32_dec_eq(x_10, x_30);
if (x_31 == 0)
{
lean_object* x_32; lean_object* x_33; 
lean_dec_ref(x_2);
x_32 = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__3;
x_33 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_32, x_6, x_17);
return x_33;
}
else
{
lean_object* x_34; 
x_34 = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1___boxed), 2, 0);
x_18 = x_34;
goto block_23;
}
}
else
{
lean_object* x_35; 
x_35 = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__4;
x_18 = x_35;
goto block_23;
}
}
else
{
x_18 = x_16;
goto block_23;
}
}
else
{
x_18 = x_16;
goto block_23;
}
block_23:
{
if (x_1 == 0)
{
lean_object* x_19; lean_object* x_20; 
lean_dec_ref(x_18);
lean_dec_ref(x_2);
x_19 = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__2;
x_20 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_19, x_7, x_17);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_inc(x_5);
x_21 = l_Lean_Parser_ParserState_next_x27___redArg(x_3, x_2, x_5);
lean_dec(x_5);
x_22 = lean_apply_2(x_18, x_2, x_21);
return x_22;
}
}
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
lean_inc(x_5);
x_36 = lean_unsigned_to_nat(8u);
x_37 = l_Lean_Parser_ParserState_next_x27___redArg(x_3, x_2, x_5);
lean_dec(x_5);
x_38 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at_____private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(x_2, x_36, x_37);
lean_dec_ref(x_2);
return x_38;
}
}
else
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; 
lean_inc(x_5);
x_39 = lean_unsigned_to_nat(4u);
x_40 = l_Lean_Parser_ParserState_next_x27___redArg(x_3, x_2, x_5);
lean_dec(x_5);
x_41 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at_____private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(x_2, x_39, x_40);
lean_dec_ref(x_2);
return x_41;
}
}
else
{
lean_object* x_42; 
lean_inc(x_5);
x_42 = l_Lean_Parser_ParserState_next_x27___redArg(x_3, x_2, x_5);
lean_dec(x_5);
lean_dec_ref(x_2);
return x_42;
}
}
else
{
lean_object* x_43; 
lean_dec_ref(x_2);
x_43 = l_Lean_Parser_ParserState_mkEOIError(x_3, x_7);
return x_43;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at_____private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at_____private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__0(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___lam__1(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(x_4, x_2, x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unterminated basic string", 25, 25);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lean_Parser_InputContext_atEnd(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_string_utf8_get_fast(x_7, x_5);
x_9 = 34;
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
uint32_t x_11; uint8_t x_12; 
x_11 = 92;
x_12 = lean_uint32_dec_eq(x_8, x_11);
if (x_12 == 0)
{
uint8_t x_13; 
x_13 = l_Lake_Toml_isControlChar(x_8);
if (x_13 == 0)
{
lean_object* x_14; 
lean_inc(x_5);
x_14 = l_Lean_Parser_ParserState_next_x27___redArg(x_3, x_2, x_5);
lean_dec(x_5);
x_3 = x_14;
goto _start;
}
else
{
lean_object* x_16; lean_object* x_17; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_16 = lean_box(0);
x_17 = l_Lake_Toml_mkUnexpectedCharError(x_3, x_8, x_16, x_13);
return x_17;
}
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; uint8_t x_22; 
lean_inc(x_5);
x_18 = l_Lean_Parser_ParserState_next_x27___redArg(x_3, x_2, x_5);
lean_dec(x_5);
lean_inc_ref(x_2);
x_19 = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(x_10, x_2, x_18);
x_20 = lean_ctor_get(x_19, 4);
lean_inc(x_20);
x_21 = lean_box(0);
x_22 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_20, x_21);
if (x_22 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_19;
}
else
{
x_3 = x_19;
goto _start;
}
}
}
else
{
lean_object* x_24; 
lean_inc(x_5);
lean_dec(x_1);
x_24 = l_Lean_Parser_ParserState_next_x27___redArg(x_3, x_2, x_5);
lean_dec(x_5);
lean_dec_ref(x_2);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_2);
x_25 = l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn___closed__0;
x_26 = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(x_3, x_25, x_1);
return x_26;
}
}
}
static lean_object* _init_l_Lake_Toml_basicStringFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("basic string", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_basicStringFn___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_basicStringFn___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicStringFn(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = 34;
x_4 = l_Lake_Toml_basicStringFn___closed__1;
lean_inc_ref(x_2);
x_5 = l_Lake_Toml_chFn(x_3, x_4, x_1, x_2);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_6, x_7);
if (x_8 == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn(x_9, x_1, x_5);
return x_10;
}
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unterminated literal string", 27, 27);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lean_Parser_InputContext_atEnd(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_string_utf8_get_fast(x_7, x_5);
x_9 = 39;
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
uint8_t x_11; 
x_11 = l_Lake_Toml_isControlChar(x_8);
if (x_11 == 0)
{
lean_object* x_12; 
lean_inc(x_5);
x_12 = l_Lean_Parser_ParserState_next_x27___redArg(x_3, x_2, x_5);
lean_dec(x_5);
x_3 = x_12;
goto _start;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec(x_1);
x_14 = lean_box(0);
x_15 = l_Lake_Toml_mkUnexpectedCharError(x_3, x_8, x_14, x_11);
return x_15;
}
}
else
{
lean_object* x_16; 
lean_inc(x_5);
lean_dec(x_1);
x_16 = l_Lean_Parser_ParserState_next_x27___redArg(x_3, x_2, x_5);
lean_dec(x_5);
return x_16;
}
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___closed__0;
x_18 = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(x_3, x_17, x_1);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_literalStringFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("literal string", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_literalStringFn___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_literalStringFn___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalStringFn(lean_object* x_1, lean_object* x_2) {
_start:
{
uint32_t x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = 39;
x_4 = l_Lake_Toml_literalStringFn___closed__1;
lean_inc_ref(x_2);
x_5 = l_Lake_Toml_chFn(x_3, x_4, x_1, x_2);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_6, x_7);
if (x_8 == 0)
{
lean_dec_ref(x_2);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn(x_9, x_1, x_5);
return x_10;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalStringFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_literalStringFn(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("too many quotes", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unterminated multi-line literal string", 38, 38);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_4, 2);
x_7 = l_Lean_Parser_InputContext_atEnd(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = 1;
x_10 = lean_string_utf8_get_fast(x_8, x_6);
x_11 = 39;
x_12 = lean_uint32_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(3u);
x_14 = lean_nat_dec_le(x_13, x_2);
lean_dec(x_2);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 10;
x_16 = lean_uint32_dec_eq(x_10, x_15);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 13;
x_18 = lean_uint32_dec_eq(x_10, x_17);
if (x_18 == 0)
{
uint8_t x_19; 
x_19 = l_Lake_Toml_isControlChar(x_10);
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; 
lean_inc(x_6);
x_20 = lean_unsigned_to_nat(0u);
x_21 = l_Lean_Parser_ParserState_next_x27___redArg(x_4, x_3, x_6);
lean_dec(x_6);
x_2 = x_20;
x_4 = x_21;
goto _start;
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_dec(x_1);
x_23 = lean_box(0);
x_24 = l_Lake_Toml_mkUnexpectedCharError(x_4, x_10, x_23, x_9);
return x_24;
}
}
else
{
lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; uint8_t x_29; 
lean_inc(x_6);
x_25 = l_Lean_Parser_ParserState_next_x27___redArg(x_4, x_3, x_6);
lean_dec(x_6);
x_26 = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(x_3, x_25);
x_27 = lean_ctor_get(x_26, 4);
lean_inc(x_27);
x_28 = lean_box(0);
x_29 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_27, x_28);
if (x_29 == 0)
{
lean_dec(x_1);
return x_26;
}
else
{
lean_object* x_30; 
x_30 = lean_unsigned_to_nat(0u);
x_2 = x_30;
x_4 = x_26;
goto _start;
}
}
}
else
{
lean_object* x_32; lean_object* x_33; 
lean_inc(x_6);
x_32 = lean_unsigned_to_nat(0u);
x_33 = l_Lean_Parser_ParserState_next_x27___redArg(x_4, x_3, x_6);
lean_dec(x_6);
x_2 = x_32;
x_4 = x_33;
goto _start;
}
}
else
{
lean_dec(x_1);
return x_4;
}
}
else
{
lean_object* x_35; lean_object* x_36; uint8_t x_37; 
lean_inc(x_6);
x_35 = l_Lean_Parser_ParserState_next_x27___redArg(x_4, x_3, x_6);
lean_dec(x_6);
x_36 = lean_unsigned_to_nat(5u);
x_37 = lean_nat_dec_le(x_36, x_2);
if (x_37 == 0)
{
lean_object* x_38; lean_object* x_39; 
x_38 = lean_unsigned_to_nat(1u);
x_39 = lean_nat_add(x_2, x_38);
lean_dec(x_2);
x_2 = x_39;
x_4 = x_35;
goto _start;
}
else
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec(x_2);
lean_dec(x_1);
x_41 = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0;
x_42 = lean_box(0);
x_43 = l_Lean_Parser_ParserState_mkUnexpectedError(x_35, x_41, x_42, x_9);
return x_43;
}
}
}
else
{
lean_object* x_44; uint8_t x_45; 
x_44 = lean_unsigned_to_nat(3u);
x_45 = lean_nat_dec_le(x_44, x_2);
lean_dec(x_2);
if (x_45 == 0)
{
lean_object* x_46; lean_object* x_47; 
x_46 = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__1;
x_47 = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(x_4, x_46, x_1);
return x_47;
}
else
{
lean_dec(x_1);
return x_4;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
static lean_object* _init_l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlLiteralStringFn_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("multi-line literal string", 25, 25);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlLiteralStringFn_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlLiteralStringFn_spec__0___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlLiteralStringFn_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 1)
{
lean_dec(x_2);
return x_3;
}
else
{
uint32_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = 39;
x_7 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlLiteralStringFn_spec__0___closed__1;
x_8 = l_Lake_Toml_chFn(x_6, x_7, x_1, x_3);
x_9 = lean_ctor_get(x_8, 4);
lean_inc(x_9);
x_10 = lean_box(0);
x_11 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_9, x_10);
if (x_11 == 0)
{
lean_dec(x_2);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_2, x_12);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralStringFn___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlLiteralStringFn_spec__0(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralStringFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_unsigned_to_nat(3u);
x_4 = lean_alloc_closure((void*)(l_Lake_Toml_mlLiteralStringFn___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_5 = l_Lean_Parser_atomicFn(x_4, x_1, x_2);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_6, x_7);
if (x_8 == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn(x_9, x_10, x_1, x_5);
lean_dec_ref(x_1);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlLiteralStringFn_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlLiteralStringFn_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlLiteralStringFn___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Toml_mlLiteralStringFn___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unterminated multi-line basic string", 36, 36);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 0);
x_6 = lean_ctor_get(x_4, 2);
x_7 = l_Lean_Parser_InputContext_atEnd(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = 1;
x_10 = lean_string_utf8_get_fast(x_8, x_6);
x_11 = 34;
x_12 = lean_uint32_dec_eq(x_10, x_11);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_unsigned_to_nat(3u);
x_14 = lean_nat_dec_le(x_13, x_2);
lean_dec(x_2);
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 10;
x_16 = lean_uint32_dec_eq(x_10, x_15);
if (x_16 == 0)
{
uint32_t x_17; uint8_t x_18; 
x_17 = 13;
x_18 = lean_uint32_dec_eq(x_10, x_17);
if (x_18 == 0)
{
uint32_t x_19; uint8_t x_20; 
x_19 = 92;
x_20 = lean_uint32_dec_eq(x_10, x_19);
if (x_20 == 0)
{
uint8_t x_21; 
x_21 = l_Lake_Toml_isControlChar(x_10);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; 
lean_inc(x_6);
x_22 = lean_unsigned_to_nat(0u);
x_23 = l_Lean_Parser_ParserState_next_x27___redArg(x_4, x_3, x_6);
lean_dec(x_6);
x_2 = x_22;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_25; lean_object* x_26; 
lean_dec_ref(x_3);
lean_dec(x_1);
x_25 = lean_box(0);
x_26 = l_Lake_Toml_mkUnexpectedCharError(x_4, x_10, x_25, x_9);
return x_26;
}
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; uint8_t x_31; 
lean_inc(x_6);
x_27 = l_Lean_Parser_ParserState_next_x27___redArg(x_4, x_3, x_6);
lean_dec(x_6);
lean_inc_ref(x_3);
x_28 = l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn(x_9, x_3, x_27);
x_29 = lean_ctor_get(x_28, 4);
lean_inc(x_29);
x_30 = lean_box(0);
x_31 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_29, x_30);
if (x_31 == 0)
{
lean_dec_ref(x_3);
lean_dec(x_1);
return x_28;
}
else
{
lean_object* x_32; 
x_32 = lean_unsigned_to_nat(0u);
x_2 = x_32;
x_4 = x_28;
goto _start;
}
}
}
else
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; uint8_t x_38; 
lean_inc(x_6);
x_34 = l_Lean_Parser_ParserState_next_x27___redArg(x_4, x_3, x_6);
lean_dec(x_6);
x_35 = l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn(x_3, x_34);
x_36 = lean_ctor_get(x_35, 4);
lean_inc(x_36);
x_37 = lean_box(0);
x_38 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_36, x_37);
if (x_38 == 0)
{
lean_dec_ref(x_3);
lean_dec(x_1);
return x_35;
}
else
{
lean_object* x_39; 
x_39 = lean_unsigned_to_nat(0u);
x_2 = x_39;
x_4 = x_35;
goto _start;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; 
lean_inc(x_6);
x_41 = lean_unsigned_to_nat(0u);
x_42 = l_Lean_Parser_ParserState_next_x27___redArg(x_4, x_3, x_6);
lean_dec(x_6);
x_2 = x_41;
x_4 = x_42;
goto _start;
}
}
else
{
lean_dec_ref(x_3);
lean_dec(x_1);
return x_4;
}
}
else
{
lean_object* x_44; lean_object* x_45; uint8_t x_46; 
lean_inc(x_6);
x_44 = l_Lean_Parser_ParserState_next_x27___redArg(x_4, x_3, x_6);
lean_dec(x_6);
x_45 = lean_unsigned_to_nat(5u);
x_46 = lean_nat_dec_le(x_45, x_2);
if (x_46 == 0)
{
lean_object* x_47; lean_object* x_48; 
x_47 = lean_unsigned_to_nat(1u);
x_48 = lean_nat_add(x_2, x_47);
lean_dec(x_2);
x_2 = x_48;
x_4 = x_44;
goto _start;
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; 
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec(x_1);
x_50 = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0;
x_51 = lean_box(0);
x_52 = l_Lean_Parser_ParserState_mkUnexpectedError(x_44, x_50, x_51, x_9);
return x_52;
}
}
}
else
{
lean_object* x_53; uint8_t x_54; 
lean_dec_ref(x_3);
x_53 = lean_unsigned_to_nat(3u);
x_54 = lean_nat_dec_le(x_53, x_2);
lean_dec(x_2);
if (x_54 == 0)
{
lean_object* x_55; lean_object* x_56; 
x_55 = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn___closed__0;
x_56 = l_Lean_Parser_ParserState_mkUnexpectedErrorAt(x_4, x_55, x_1);
return x_56;
}
else
{
lean_dec(x_1);
return x_4;
}
}
}
}
static lean_object* _init_l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlBasicStringFn_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("multi-line basic string", 23, 23);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlBasicStringFn_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlBasicStringFn_spec__0___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlBasicStringFn_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 1)
{
lean_dec(x_2);
return x_3;
}
else
{
uint32_t x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; 
x_6 = 34;
x_7 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlBasicStringFn_spec__0___closed__1;
x_8 = l_Lake_Toml_chFn(x_6, x_7, x_1, x_3);
x_9 = lean_ctor_get(x_8, 4);
lean_inc(x_9);
x_10 = lean_box(0);
x_11 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_9, x_10);
if (x_11 == 0)
{
lean_dec(x_2);
return x_8;
}
else
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_unsigned_to_nat(1u);
x_13 = lean_nat_sub(x_2, x_12);
lean_dec(x_2);
x_2 = x_13;
x_3 = x_8;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicStringFn___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlBasicStringFn_spec__0(x_2, x_1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicStringFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_3 = lean_unsigned_to_nat(3u);
x_4 = lean_alloc_closure((void*)(l_Lake_Toml_mlBasicStringFn___lam__0___boxed), 3, 1);
lean_closure_set(x_4, 0, x_3);
lean_inc_ref(x_2);
lean_inc_ref(x_1);
x_5 = l_Lean_Parser_atomicFn(x_4, x_1, x_2);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_6, x_7);
if (x_8 == 0)
{
lean_dec_ref(x_2);
lean_dec_ref(x_1);
return x_5;
}
else
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_9 = lean_ctor_get(x_2, 2);
lean_inc(x_9);
lean_dec_ref(x_2);
x_10 = lean_unsigned_to_nat(0u);
x_11 = l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn(x_9, x_10, x_1, x_5);
return x_11;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlBasicStringFn_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlBasicStringFn_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_mlBasicStringFn___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lake_Toml_mlBasicStringFn___lam__0(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hour digit", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("", 0, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 58;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("minute digit", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__1;
x_4 = l_Lake_Toml_digitPairFn(x_3, x_1, x_2);
x_5 = lean_ctor_get(x_4, 4);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_5, x_6);
if (x_7 == 0)
{
return x_4;
}
else
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = 58;
x_9 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7;
x_10 = l_Lake_Toml_chFn(x_8, x_9, x_1, x_4);
x_11 = lean_ctor_get(x_10, 4);
lean_inc(x_11);
x_12 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_11, x_6);
if (x_12 == 0)
{
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; 
x_13 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9;
x_14 = l_Lake_Toml_digitPairFn(x_13, x_1, x_10);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("time offset is forbidden here", 29, 29);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn(uint8_t x_1, uint32_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint8_t x_7; uint8_t x_14; uint32_t x_25; uint8_t x_26; 
x_25 = 90;
x_26 = lean_uint32_dec_eq(x_2, x_25);
if (x_26 == 0)
{
uint32_t x_27; uint8_t x_28; 
x_27 = 122;
x_28 = lean_uint32_dec_eq(x_2, x_27);
x_14 = x_28;
goto block_24;
}
else
{
x_14 = x_26;
goto block_24;
}
block_13:
{
if (x_7 == 0)
{
lean_dec(x_3);
return x_5;
}
else
{
if (x_1 == 0)
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; 
lean_dec(x_3);
x_8 = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0;
x_9 = lean_box(0);
x_10 = l_Lean_Parser_ParserState_mkUnexpectedError(x_5, x_8, x_9, x_6);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = l_Lean_Parser_ParserState_setPos(x_5, x_3);
x_12 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(x_4, x_11);
return x_12;
}
}
}
block_24:
{
uint8_t x_15; 
x_15 = 1;
if (x_14 == 0)
{
uint32_t x_16; uint8_t x_17; 
x_16 = 43;
x_17 = lean_uint32_dec_eq(x_2, x_16);
if (x_17 == 0)
{
uint32_t x_18; uint8_t x_19; 
x_18 = 45;
x_19 = lean_uint32_dec_eq(x_2, x_18);
x_6 = x_15;
x_7 = x_19;
goto block_13;
}
else
{
x_6 = x_15;
x_7 = x_17;
goto block_13;
}
}
else
{
if (x_1 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
lean_dec(x_3);
x_20 = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0;
x_21 = lean_box(0);
x_22 = l_Lean_Parser_ParserState_mkUnexpectedError(x_5, x_20, x_21, x_15);
return x_22;
}
else
{
lean_object* x_23; 
x_23 = l_Lean_Parser_ParserState_setPos(x_5, x_3);
return x_23;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint8_t x_6; uint32_t x_7; lean_object* x_8; 
x_6 = lean_unbox(x_1);
x_7 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_8 = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn(x_6, x_7, x_3, x_4, x_5);
lean_dec_ref(x_4);
return x_8;
}
}
LEAN_EXPORT uint8_t l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0(uint32_t x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; 
x_2 = 48;
x_3 = lean_uint32_dec_le(x_2, x_1);
if (x_3 == 0)
{
return x_3;
}
else
{
uint32_t x_4; uint8_t x_5; 
x_4 = 57;
x_5 = lean_uint32_dec_le(x_1, x_4);
return x_5;
}
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("millisecond", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lean_Parser_InputContext_atEnd(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint32_t x_8; uint32_t x_9; uint8_t x_10; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_string_utf8_get_fast(x_7, x_5);
x_9 = 46;
x_10 = lean_uint32_dec_eq(x_8, x_9);
if (x_10 == 0)
{
lean_object* x_11; uint8_t x_12; uint8_t x_13; uint8_t x_20; uint32_t x_31; uint8_t x_32; 
x_11 = lean_string_utf8_next_fast(x_7, x_5);
x_31 = 90;
x_32 = lean_uint32_dec_eq(x_8, x_31);
if (x_32 == 0)
{
uint32_t x_33; uint8_t x_34; 
x_33 = 122;
x_34 = lean_uint32_dec_eq(x_8, x_33);
x_20 = x_34;
goto block_30;
}
else
{
x_20 = x_32;
goto block_30;
}
block_19:
{
if (x_13 == 0)
{
lean_dec(x_11);
return x_3;
}
else
{
if (x_1 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
lean_dec(x_11);
x_14 = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0;
x_15 = lean_box(0);
x_16 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_14, x_15, x_12);
return x_16;
}
else
{
lean_object* x_17; lean_object* x_18; 
x_17 = l_Lean_Parser_ParserState_setPos(x_3, x_11);
x_18 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(x_2, x_17);
return x_18;
}
}
}
block_30:
{
uint8_t x_21; 
x_21 = 1;
if (x_20 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = 43;
x_23 = lean_uint32_dec_eq(x_8, x_22);
if (x_23 == 0)
{
uint32_t x_24; uint8_t x_25; 
x_24 = 45;
x_25 = lean_uint32_dec_eq(x_8, x_24);
x_12 = x_21;
x_13 = x_25;
goto block_19;
}
else
{
x_12 = x_21;
x_13 = x_23;
goto block_19;
}
}
else
{
if (x_1 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_11);
x_26 = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0;
x_27 = lean_box(0);
x_28 = l_Lean_Parser_ParserState_mkUnexpectedError(x_3, x_26, x_27, x_21);
return x_28;
}
else
{
lean_object* x_29; 
x_29 = l_Lean_Parser_ParserState_setPos(x_3, x_11);
return x_29;
}
}
}
}
else
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_5);
x_35 = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0___boxed), 1, 0);
x_36 = l_Lean_Parser_ParserState_next_x27___redArg(x_3, x_2, x_5);
lean_dec(x_5);
x_37 = lean_box(0);
x_38 = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__1;
x_39 = l_Lake_Toml_takeWhile1Fn(x_35, x_38, x_2, x_36);
x_40 = lean_ctor_get(x_39, 2);
lean_inc(x_40);
x_41 = lean_ctor_get(x_39, 4);
lean_inc(x_41);
x_42 = lean_box(0);
x_43 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_41, x_42);
if (x_43 == 0)
{
lean_dec(x_40);
return x_39;
}
else
{
if (x_6 == 0)
{
uint8_t x_44; 
x_44 = l_Lean_Parser_InputContext_atEnd(x_4, x_40);
if (x_44 == 0)
{
uint32_t x_45; lean_object* x_46; uint8_t x_47; uint8_t x_53; uint32_t x_62; uint8_t x_63; 
x_45 = lean_string_utf8_get_fast(x_7, x_40);
x_46 = lean_string_utf8_next_fast(x_7, x_40);
lean_dec(x_40);
x_62 = 90;
x_63 = lean_uint32_dec_eq(x_45, x_62);
if (x_63 == 0)
{
uint32_t x_64; uint8_t x_65; 
x_64 = 122;
x_65 = lean_uint32_dec_eq(x_45, x_64);
x_53 = x_65;
goto block_61;
}
else
{
x_53 = x_63;
goto block_61;
}
block_52:
{
if (x_47 == 0)
{
lean_dec(x_46);
return x_39;
}
else
{
if (x_1 == 0)
{
lean_object* x_48; lean_object* x_49; 
lean_dec(x_46);
x_48 = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0;
x_49 = l_Lean_Parser_ParserState_mkUnexpectedError(x_39, x_48, x_37, x_43);
return x_49;
}
else
{
lean_object* x_50; lean_object* x_51; 
x_50 = l_Lean_Parser_ParserState_setPos(x_39, x_46);
x_51 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn(x_2, x_50);
return x_51;
}
}
}
block_61:
{
if (x_53 == 0)
{
uint32_t x_54; uint8_t x_55; 
x_54 = 43;
x_55 = lean_uint32_dec_eq(x_45, x_54);
if (x_55 == 0)
{
uint32_t x_56; uint8_t x_57; 
x_56 = 45;
x_57 = lean_uint32_dec_eq(x_45, x_56);
x_47 = x_57;
goto block_52;
}
else
{
x_47 = x_55;
goto block_52;
}
}
else
{
if (x_1 == 0)
{
lean_object* x_58; lean_object* x_59; 
lean_dec(x_46);
x_58 = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0;
x_59 = l_Lean_Parser_ParserState_mkUnexpectedError(x_39, x_58, x_37, x_43);
return x_59;
}
else
{
lean_object* x_60; 
x_60 = l_Lean_Parser_ParserState_setPos(x_39, x_46);
return x_60;
}
}
}
}
else
{
lean_dec(x_40);
return x_39;
}
}
else
{
lean_dec(x_40);
return x_39;
}
}
}
}
else
{
return x_3;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(x_4, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("second digit", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9;
x_5 = l_Lake_Toml_digitPairFn(x_4, x_2, x_3);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_6, x_7);
if (x_8 == 0)
{
return x_5;
}
else
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = 58;
x_10 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7;
x_11 = l_Lake_Toml_chFn(x_9, x_10, x_2, x_5);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
x_13 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_12, x_7);
if (x_13 == 0)
{
return x_11;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_14 = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__1;
x_15 = l_Lake_Toml_digitPairFn(x_14, x_2, x_11);
x_16 = lean_ctor_get(x_15, 4);
lean_inc(x_16);
x_17 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_16, x_7);
if (x_17 == 0)
{
return x_15;
}
else
{
lean_object* x_18; 
x_18 = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn(x_1, x_2, x_15);
return x_18;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(x_4, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
static lean_object* _init_l_Lake_Toml_timeFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hour", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_timeFn___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_timeFn___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_timeFn(uint8_t x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_4 = l_Lake_Toml_timeFn___closed__1;
x_5 = l_Lake_Toml_digitPairFn(x_4, x_2, x_3);
x_6 = lean_ctor_get(x_5, 4);
lean_inc(x_6);
x_7 = lean_box(0);
x_8 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_6, x_7);
if (x_8 == 0)
{
return x_5;
}
else
{
uint32_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_9 = 58;
x_10 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7;
x_11 = l_Lake_Toml_chFn(x_9, x_10, x_2, x_5);
x_12 = lean_ctor_get(x_11, 4);
lean_inc(x_12);
x_13 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_12, x_7);
if (x_13 == 0)
{
return x_11;
}
else
{
lean_object* x_14; 
x_14 = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(x_1, x_2, x_11);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_timeFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = lean_unbox(x_1);
x_5 = l_Lake_Toml_timeFn(x_4, x_2, x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_5; 
x_3 = lean_ctor_get(x_2, 2);
x_4 = lean_ctor_get(x_1, 0);
x_5 = l_Lean_Parser_InputContext_atEnd(x_4, x_3);
if (x_5 == 0)
{
lean_object* x_6; uint8_t x_7; uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_6 = lean_ctor_get(x_4, 0);
x_7 = 1;
x_11 = lean_string_utf8_get_fast(x_6, x_3);
x_12 = 84;
x_13 = lean_uint32_dec_eq(x_11, x_12);
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 116;
x_15 = lean_uint32_dec_eq(x_11, x_14);
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; 
x_16 = 32;
x_17 = lean_uint32_dec_eq(x_11, x_16);
if (x_17 == 0)
{
return x_2;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
lean_inc(x_3);
x_18 = lean_string_utf8_next_fast(x_6, x_3);
lean_inc(x_18);
x_19 = l_Lean_Parser_ParserState_setPos(x_2, x_18);
x_20 = l_Lake_Toml_timeFn(x_7, x_1, x_19);
x_28 = lean_ctor_get(x_20, 4);
lean_inc(x_28);
x_29 = lean_box(0);
x_30 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_28, x_29);
if (x_30 == 0)
{
goto block_27;
}
else
{
if (x_15 == 0)
{
lean_dec(x_18);
lean_dec(x_3);
return x_20;
}
else
{
goto block_27;
}
}
block_27:
{
lean_object* x_21; uint8_t x_22; 
x_21 = lean_ctor_get(x_20, 2);
lean_inc(x_21);
x_22 = lean_nat_dec_eq(x_21, x_18);
lean_dec(x_18);
lean_dec(x_21);
if (x_22 == 0)
{
lean_dec(x_3);
return x_20;
}
else
{
lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_23 = l_Lean_Parser_ParserState_stackSize(x_20);
x_24 = lean_unsigned_to_nat(1u);
x_25 = lean_nat_sub(x_23, x_24);
lean_dec(x_23);
x_26 = l_Lean_Parser_ParserState_restore(x_20, x_25, x_3);
lean_dec(x_25);
return x_26;
}
}
}
}
else
{
lean_inc(x_3);
goto block_10;
}
}
else
{
lean_inc(x_3);
goto block_10;
}
block_10:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_Parser_ParserState_next_x27___redArg(x_2, x_1, x_3);
lean_dec(x_3);
x_9 = l_Lake_Toml_timeFn(x_7, x_1, x_8);
return x_9;
}
}
else
{
return x_2;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("month digit", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 45;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("day digit", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__1;
x_4 = l_Lake_Toml_digitPairFn(x_3, x_1, x_2);
x_5 = lean_ctor_get(x_4, 4);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_5, x_6);
if (x_7 == 0)
{
return x_4;
}
else
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = 45;
x_9 = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5;
x_10 = l_Lake_Toml_chFn(x_8, x_9, x_1, x_4);
x_11 = lean_ctor_get(x_10, 4);
lean_inc(x_11);
x_12 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_11, x_6);
if (x_12 == 0)
{
return x_10;
}
else
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_13 = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__7;
x_14 = l_Lake_Toml_digitPairFn(x_13, x_1, x_10);
x_15 = lean_ctor_get(x_14, 4);
lean_inc(x_15);
x_16 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_15, x_6);
if (x_16 == 0)
{
return x_14;
}
else
{
lean_object* x_17; 
x_17 = l___private_Lake_Toml_Grammar_0__Lake_Toml_optTimeFn(x_1, x_14);
return x_17;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_dateTimeFn_spec__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("year digit", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_dateTimeFn_spec__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_dateTimeFn_spec__0___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_dateTimeFn_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_unsigned_to_nat(0u);
x_5 = lean_nat_dec_eq(x_2, x_4);
if (x_5 == 1)
{
lean_dec(x_2);
return x_3;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_6 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_dateTimeFn_spec__0___closed__1;
x_7 = l_Lake_Toml_digitFn(x_6, x_1, x_3);
x_8 = lean_ctor_get(x_7, 4);
lean_inc(x_8);
x_9 = lean_box(0);
x_10 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_8, x_9);
if (x_10 == 0)
{
lean_dec(x_2);
return x_7;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_unsigned_to_nat(1u);
x_12 = lean_nat_sub(x_2, x_11);
lean_dec(x_2);
x_2 = x_12;
x_3 = x_7;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dateTimeFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_3 = lean_unsigned_to_nat(4u);
x_4 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_dateTimeFn_spec__0(x_1, x_3, x_2);
x_5 = lean_ctor_get(x_4, 4);
lean_inc(x_5);
x_6 = lean_box(0);
x_7 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_5, x_6);
if (x_7 == 0)
{
return x_4;
}
else
{
uint32_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_8 = 45;
x_9 = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5;
x_10 = l_Lake_Toml_chFn(x_8, x_9, x_1, x_4);
x_11 = lean_ctor_get(x_10, 4);
lean_inc(x_11);
x_12 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_11, x_6);
if (x_12 == 0)
{
return x_10;
}
else
{
lean_object* x_13; 
x_13 = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(x_1, x_10);
return x_13;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_dateTimeFn_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_dateTimeFn_spec__0(x_1, x_2, x_3);
lean_dec_ref(x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_dateTimeFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_dateTimeFn(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decimal exponent", 16, 16);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___lam__0___boxed), 1, 0);
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 2);
x_5 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__1;
x_6 = l_Lean_Parser_InputContext_atEnd(x_3, x_4);
if (x_6 == 0)
{
lean_object* x_7; lean_object* x_8; uint32_t x_13; uint32_t x_14; uint8_t x_15; 
x_7 = lean_ctor_get(x_3, 0);
x_8 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__2;
x_13 = lean_string_utf8_get_fast(x_7, x_4);
x_14 = 45;
x_15 = lean_uint32_dec_eq(x_13, x_14);
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; 
x_16 = 43;
x_17 = lean_uint32_dec_eq(x_13, x_16);
if (x_17 == 0)
{
uint8_t x_18; uint8_t x_19; uint32_t x_25; uint8_t x_26; 
x_18 = 1;
x_25 = 48;
x_26 = lean_uint32_dec_le(x_25, x_13);
if (x_26 == 0)
{
x_19 = x_26;
goto block_24;
}
else
{
uint32_t x_27; uint8_t x_28; 
x_27 = 57;
x_28 = lean_uint32_dec_le(x_13, x_27);
x_19 = x_28;
goto block_24;
}
block_24:
{
if (x_19 == 0)
{
lean_object* x_20; 
x_20 = l_Lake_Toml_mkUnexpectedCharError(x_2, x_13, x_5, x_18);
return x_20;
}
else
{
lean_object* x_21; uint32_t x_22; lean_object* x_23; 
lean_inc(x_4);
x_21 = l_Lean_Parser_ParserState_next_x27___redArg(x_2, x_1, x_4);
lean_dec(x_4);
x_22 = 95;
x_23 = l_Lake_Toml_sepByChar1AuxFn(x_8, x_22, x_5, x_1, x_21);
return x_23;
}
}
}
else
{
lean_inc(x_4);
goto block_12;
}
}
else
{
lean_inc(x_4);
goto block_12;
}
block_12:
{
lean_object* x_9; uint32_t x_10; lean_object* x_11; 
x_9 = l_Lean_Parser_ParserState_next_x27___redArg(x_2, x_1, x_4);
lean_dec(x_4);
x_10 = 95;
x_11 = l_Lake_Toml_sepByChar1Fn(x_8, x_10, x_5, x_1, x_9);
return x_11;
}
}
else
{
lean_object* x_29; 
x_29 = l_Lean_Parser_ParserState_mkEOIError(x_2, x_5);
return x_29;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint8_t x_8; 
x_3 = lean_ctor_get(x_1, 0);
x_4 = lean_ctor_get(x_2, 2);
x_8 = l_Lean_Parser_InputContext_atEnd(x_3, x_4);
if (x_8 == 0)
{
lean_object* x_9; uint32_t x_10; uint32_t x_11; uint8_t x_12; 
x_9 = lean_ctor_get(x_3, 0);
x_10 = lean_string_utf8_get_fast(x_9, x_4);
x_11 = 101;
x_12 = lean_uint32_dec_eq(x_10, x_11);
if (x_12 == 0)
{
uint32_t x_13; uint8_t x_14; 
x_13 = 69;
x_14 = lean_uint32_dec_eq(x_10, x_13);
if (x_14 == 0)
{
return x_2;
}
else
{
lean_inc(x_4);
goto block_7;
}
}
else
{
lean_inc(x_4);
goto block_7;
}
}
else
{
return x_2;
}
block_7:
{
lean_object* x_5; lean_object* x_6; 
x_5 = l_Lean_Parser_ParserState_next_x27___redArg(x_2, x_1, x_4);
lean_dec(x_4);
x_6 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(x_1, x_5);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Lake", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("Toml", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("float", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_skipFn___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decInt", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__7() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decimal fraction", 16, 16);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(lean_object* x_1, uint32_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; uint32_t x_11; uint8_t x_12; 
x_11 = 46;
x_12 = lean_uint32_dec_eq(x_2, x_11);
if (x_12 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = 101;
x_23 = lean_uint32_dec_eq(x_2, x_22);
if (x_23 == 0)
{
uint32_t x_24; uint8_t x_25; 
x_24 = 69;
x_25 = lean_uint32_dec_eq(x_2, x_24);
if (x_25 == 0)
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
lean_dec(x_3);
x_26 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6;
x_27 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_28 = l_Lake_Toml_pushLit(x_26, x_1, x_27, x_4, x_5);
return x_28;
}
else
{
goto block_21;
}
}
else
{
goto block_21;
}
}
else
{
lean_object* x_29; lean_object* x_30; uint32_t x_31; lean_object* x_32; lean_object* x_33; lean_object* x_39; lean_object* x_40; uint8_t x_41; 
x_29 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__2;
x_30 = l_Lean_Parser_ParserState_setPos(x_5, x_3);
x_31 = 95;
x_32 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__8;
x_33 = l_Lake_Toml_sepByChar1Fn(x_29, x_31, x_32, x_4, x_30);
x_39 = lean_ctor_get(x_33, 4);
lean_inc(x_39);
x_40 = lean_box(0);
x_41 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_39, x_40);
if (x_41 == 0)
{
if (x_12 == 0)
{
goto block_38;
}
else
{
lean_dec_ref(x_4);
lean_dec(x_1);
return x_33;
}
}
else
{
goto block_38;
}
block_38:
{
lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_34 = l___private_Lake_Toml_Grammar_0__Lake_Toml_optDecExpFn(x_4, x_33);
x_35 = lean_ctor_get(x_34, 4);
lean_inc(x_35);
x_36 = lean_box(0);
x_37 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_35, x_36);
if (x_37 == 0)
{
if (x_12 == 0)
{
x_6 = x_34;
goto block_10;
}
else
{
lean_dec_ref(x_4);
lean_dec(x_1);
return x_34;
}
}
else
{
x_6 = x_34;
goto block_10;
}
}
}
block_10:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; 
x_7 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3;
x_8 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_9 = l_Lake_Toml_pushLit(x_7, x_1, x_8, x_4, x_6);
return x_9;
}
block_21:
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; uint8_t x_17; 
x_13 = l_Lean_Parser_ParserState_setPos(x_5, x_3);
x_14 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn(x_4, x_13);
x_15 = lean_ctor_get(x_14, 4);
lean_inc(x_15);
x_16 = lean_box(0);
x_17 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_15, x_16);
if (x_17 == 0)
{
lean_dec_ref(x_4);
lean_dec(x_1);
return x_14;
}
else
{
if (x_12 == 0)
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3;
x_19 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_20 = l_Lake_Toml_pushLit(x_18, x_1, x_19, x_4, x_14);
return x_20;
}
else
{
lean_dec_ref(x_4);
lean_dec(x_1);
return x_14;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_7 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lean_Parser_InputContext_atEnd(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint32_t x_8; lean_object* x_9; lean_object* x_10; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_string_utf8_get_fast(x_7, x_5);
x_9 = lean_string_utf8_next_fast(x_7, x_5);
x_10 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(x_1, x_8, x_9, x_2, x_3);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6;
x_12 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_13 = l_Lake_Toml_pushLit(x_11, x_1, x_12, x_2, x_3);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(lean_object* x_1, uint32_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; uint8_t x_7; 
x_6 = 95;
x_7 = lean_uint32_dec_eq(x_2, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(x_1, x_2, x_3, x_4, x_5);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Parser_ParserState_setPos(x_5, x_3);
x_10 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn(x_1, x_4, x_9);
return x_10;
}
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("decimal integer", 15, 15);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__1;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_3, 2);
x_5 = lean_ctor_get(x_2, 0);
x_6 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2;
x_7 = l_Lean_Parser_InputContext_atEnd(x_5, x_4);
if (x_7 == 0)
{
lean_object* x_8; uint8_t x_9; uint32_t x_10; uint8_t x_11; uint32_t x_16; uint8_t x_17; 
x_8 = lean_ctor_get(x_5, 0);
x_9 = 1;
x_10 = lean_string_utf8_get_fast(x_8, x_4);
x_16 = 48;
x_17 = lean_uint32_dec_le(x_16, x_10);
if (x_17 == 0)
{
x_11 = x_17;
goto block_15;
}
else
{
uint32_t x_18; uint8_t x_19; 
x_18 = 57;
x_19 = lean_uint32_dec_le(x_10, x_18);
x_11 = x_19;
goto block_15;
}
block_15:
{
if (x_11 == 0)
{
lean_object* x_12; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_12 = l_Lake_Toml_mkUnexpectedCharError(x_3, x_10, x_6, x_9);
return x_12;
}
else
{
lean_object* x_13; lean_object* x_14; 
lean_inc(x_4);
x_13 = l_Lean_Parser_ParserState_next_x27___redArg(x_3, x_2, x_4);
lean_dec(x_4);
x_14 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(x_1, x_2, x_13);
return x_14;
}
}
}
else
{
lean_object* x_20; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_20 = l_Lean_Parser_ParserState_mkEOIError(x_3, x_6);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; uint8_t x_6; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lean_Parser_InputContext_atEnd(x_4, x_5);
if (x_6 == 0)
{
lean_object* x_7; uint32_t x_8; uint8_t x_9; uint32_t x_15; uint8_t x_16; 
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_string_utf8_get_fast(x_7, x_5);
x_15 = 48;
x_16 = lean_uint32_dec_le(x_15, x_8);
if (x_16 == 0)
{
x_9 = x_16;
goto block_14;
}
else
{
uint32_t x_17; uint8_t x_18; 
x_17 = 57;
x_18 = lean_uint32_dec_le(x_8, x_17);
x_9 = x_18;
goto block_14;
}
block_14:
{
if (x_9 == 0)
{
lean_object* x_10; lean_object* x_11; 
x_10 = lean_string_utf8_next_fast(x_7, x_5);
x_11 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(x_1, x_8, x_10, x_2, x_3);
return x_11;
}
else
{
lean_object* x_12; 
lean_inc(x_5);
x_12 = l_Lean_Parser_ParserState_next_x27___redArg(x_3, x_2, x_5);
lean_dec(x_5);
x_3 = x_12;
goto _start;
}
}
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6;
x_20 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_21 = l_Lake_Toml_pushLit(x_19, x_1, x_20, x_2, x_3);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
uint32_t x_6; lean_object* x_7; 
x_6 = lean_unbox_uint32(x_2);
lean_dec(x_2);
x_7 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(x_1, x_6, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("nf", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'inf'", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__0;
x_5 = l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__2;
lean_inc_ref(x_2);
x_6 = l_Lake_Toml_strFn(x_4, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_7, x_8);
if (x_9 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3;
x_11 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_12 = l_Lake_Toml_pushLit(x_10, x_1, x_11, x_2, x_6);
return x_12;
}
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("an", 2, 2);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__1() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'nan'", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__1;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_4 = l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__0;
x_5 = l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__2;
lean_inc_ref(x_2);
x_6 = l_Lake_Toml_strFn(x_4, x_5, x_2, x_3);
x_7 = lean_ctor_get(x_6, 4);
lean_inc(x_7);
x_8 = lean_box(0);
x_9 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_7, x_8);
if (x_9 == 0)
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_6;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3;
x_11 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_12 = l_Lake_Toml_pushLit(x_10, x_1, x_11, x_2, x_6);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decimalFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_3, 2);
x_6 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2;
x_7 = l_Lean_Parser_InputContext_atEnd(x_4, x_5);
if (x_7 == 0)
{
lean_object* x_8; uint32_t x_9; uint32_t x_10; uint8_t x_11; 
x_8 = lean_ctor_get(x_4, 0);
x_9 = lean_string_utf8_get_fast(x_8, x_5);
x_10 = 48;
x_11 = lean_uint32_dec_eq(x_9, x_10);
if (x_11 == 0)
{
uint8_t x_12; uint8_t x_13; uint8_t x_26; 
x_12 = 1;
x_26 = lean_uint32_dec_le(x_10, x_9);
if (x_26 == 0)
{
x_13 = x_26;
goto block_25;
}
else
{
uint32_t x_27; uint8_t x_28; 
x_27 = 57;
x_28 = lean_uint32_dec_le(x_9, x_27);
x_13 = x_28;
goto block_25;
}
block_25:
{
if (x_13 == 0)
{
uint32_t x_14; uint8_t x_15; 
x_14 = 105;
x_15 = lean_uint32_dec_eq(x_9, x_14);
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; 
x_16 = 110;
x_17 = lean_uint32_dec_eq(x_9, x_16);
if (x_17 == 0)
{
lean_object* x_18; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_18 = l_Lake_Toml_mkUnexpectedCharError(x_3, x_9, x_6, x_12);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; 
lean_inc(x_5);
x_19 = l_Lean_Parser_ParserState_next_x27___redArg(x_3, x_2, x_5);
lean_dec(x_5);
x_20 = l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(x_1, x_2, x_19);
return x_20;
}
}
else
{
lean_object* x_21; lean_object* x_22; 
lean_inc(x_5);
x_21 = l_Lean_Parser_ParserState_next_x27___redArg(x_3, x_2, x_5);
lean_dec(x_5);
x_22 = l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(x_1, x_2, x_21);
return x_22;
}
}
else
{
lean_object* x_23; lean_object* x_24; 
lean_inc(x_5);
x_23 = l_Lean_Parser_ParserState_next_x27___redArg(x_3, x_2, x_5);
lean_dec(x_5);
x_24 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(x_1, x_2, x_23);
return x_24;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
lean_inc(x_5);
x_29 = l_Lean_Parser_ParserState_next_x27___redArg(x_3, x_2, x_5);
lean_dec(x_5);
x_30 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailFn(x_1, x_2, x_29);
return x_30;
}
}
else
{
lean_object* x_31; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_31 = l_Lean_Parser_ParserState_mkEOIError(x_3, x_6);
return x_31;
}
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("dateTime", 8, 8);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("date-time", 9, 9);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__3;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__4;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint32_t x_5; lean_object* x_6; uint8_t x_7; lean_object* x_12; uint8_t x_13; lean_object* x_18; uint8_t x_19; lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_3, 2);
x_26 = l_Lean_Parser_InputContext_atEnd(x_24, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; uint32_t x_30; uint8_t x_31; lean_object* x_53; uint32_t x_54; lean_object* x_55; uint8_t x_56; uint32_t x_71; lean_object* x_72; uint8_t x_73; uint32_t x_95; uint8_t x_96; 
x_27 = lean_ctor_get(x_24, 0);
x_71 = lean_string_utf8_get_fast(x_27, x_25);
x_72 = lean_string_utf8_next_fast(x_27, x_25);
x_95 = 48;
x_96 = lean_uint32_dec_le(x_95, x_71);
if (x_96 == 0)
{
x_73 = x_96;
goto block_94;
}
else
{
uint32_t x_97; uint8_t x_98; 
x_97 = 57;
x_98 = lean_uint32_dec_le(x_71, x_97);
x_73 = x_98;
goto block_94;
}
block_52:
{
if (x_31 == 0)
{
lean_object* x_32; 
x_32 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(x_1, x_30, x_28, x_2, x_29);
return x_32;
}
else
{
lean_object* x_33; uint8_t x_34; 
lean_inc(x_28);
x_33 = l_Lean_Parser_ParserState_setPos(x_29, x_28);
x_34 = l_Lean_Parser_InputContext_atEnd(x_24, x_28);
lean_dec(x_28);
if (x_34 == 0)
{
lean_object* x_35; uint32_t x_36; lean_object* x_37; uint32_t x_38; uint8_t x_39; 
x_35 = lean_ctor_get(x_33, 2);
lean_inc(x_35);
x_36 = lean_string_utf8_get_fast(x_27, x_35);
x_37 = lean_string_utf8_next_fast(x_27, x_35);
lean_dec(x_35);
x_38 = 45;
x_39 = lean_uint32_dec_eq(x_36, x_38);
if (x_39 == 0)
{
uint32_t x_40; uint8_t x_41; 
x_40 = 48;
x_41 = lean_uint32_dec_le(x_40, x_36);
if (x_41 == 0)
{
x_4 = x_37;
x_5 = x_36;
x_6 = x_33;
x_7 = x_41;
goto block_11;
}
else
{
uint32_t x_42; uint8_t x_43; 
x_42 = 57;
x_43 = lean_uint32_dec_le(x_36, x_42);
x_4 = x_37;
x_5 = x_36;
x_6 = x_33;
x_7 = x_43;
goto block_11;
}
}
else
{
lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_44 = l_Lean_Parser_ParserState_setPos(x_33, x_37);
x_45 = l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn(x_2, x_44);
x_46 = lean_ctor_get(x_45, 4);
lean_inc(x_46);
x_47 = lean_box(0);
x_48 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_46, x_47);
if (x_48 == 0)
{
x_12 = x_45;
x_13 = x_39;
goto block_17;
}
else
{
x_12 = x_45;
x_13 = x_34;
goto block_17;
}
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; 
x_49 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6;
x_50 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_51 = l_Lake_Toml_pushLit(x_49, x_1, x_50, x_2, x_33);
return x_51;
}
}
}
block_70:
{
if (x_56 == 0)
{
lean_object* x_57; 
x_57 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(x_1, x_54, x_55, x_2, x_53);
return x_57;
}
else
{
lean_object* x_58; lean_object* x_59; uint8_t x_60; 
x_58 = l_Lean_Parser_ParserState_setPos(x_53, x_55);
x_59 = lean_ctor_get(x_58, 2);
lean_inc(x_59);
x_60 = l_Lean_Parser_InputContext_atEnd(x_24, x_59);
if (x_60 == 0)
{
uint32_t x_61; lean_object* x_62; uint32_t x_63; uint8_t x_64; 
x_61 = lean_string_utf8_get_fast(x_27, x_59);
x_62 = lean_string_utf8_next_fast(x_27, x_59);
lean_dec(x_59);
x_63 = 48;
x_64 = lean_uint32_dec_le(x_63, x_61);
if (x_64 == 0)
{
x_28 = x_62;
x_29 = x_58;
x_30 = x_61;
x_31 = x_64;
goto block_52;
}
else
{
uint32_t x_65; uint8_t x_66; 
x_65 = 57;
x_66 = lean_uint32_dec_le(x_61, x_65);
x_28 = x_62;
x_29 = x_58;
x_30 = x_61;
x_31 = x_66;
goto block_52;
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; 
lean_dec(x_59);
x_67 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6;
x_68 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_69 = l_Lake_Toml_pushLit(x_67, x_1, x_68, x_2, x_58);
return x_69;
}
}
}
block_94:
{
if (x_73 == 0)
{
lean_object* x_74; 
x_74 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(x_1, x_71, x_72, x_2, x_3);
return x_74;
}
else
{
lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_75 = l_Lean_Parser_ParserState_setPos(x_3, x_72);
x_76 = lean_ctor_get(x_75, 2);
lean_inc(x_76);
x_77 = l_Lean_Parser_InputContext_atEnd(x_24, x_76);
if (x_77 == 0)
{
uint32_t x_78; lean_object* x_79; uint32_t x_80; uint8_t x_81; 
x_78 = lean_string_utf8_get_fast(x_27, x_76);
x_79 = lean_string_utf8_next_fast(x_27, x_76);
lean_dec(x_76);
x_80 = 58;
x_81 = lean_uint32_dec_eq(x_78, x_80);
if (x_81 == 0)
{
uint32_t x_82; uint8_t x_83; 
x_82 = 48;
x_83 = lean_uint32_dec_le(x_82, x_78);
if (x_83 == 0)
{
x_53 = x_75;
x_54 = x_78;
x_55 = x_79;
x_56 = x_83;
goto block_70;
}
else
{
uint32_t x_84; uint8_t x_85; 
x_84 = 57;
x_85 = lean_uint32_dec_le(x_78, x_84);
x_53 = x_75;
x_54 = x_78;
x_55 = x_79;
x_56 = x_85;
goto block_70;
}
}
else
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; uint8_t x_90; 
x_86 = l_Lean_Parser_ParserState_setPos(x_75, x_79);
x_87 = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(x_77, x_2, x_86);
x_88 = lean_ctor_get(x_87, 4);
lean_inc(x_88);
x_89 = lean_box(0);
x_90 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_88, x_89);
if (x_90 == 0)
{
x_18 = x_87;
x_19 = x_81;
goto block_23;
}
else
{
x_18 = x_87;
x_19 = x_77;
goto block_23;
}
}
}
else
{
lean_object* x_91; lean_object* x_92; lean_object* x_93; 
lean_dec(x_76);
x_91 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6;
x_92 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_93 = l_Lake_Toml_pushLit(x_91, x_1, x_92, x_2, x_75);
return x_93;
}
}
}
}
else
{
lean_object* x_99; lean_object* x_100; 
lean_dec_ref(x_2);
lean_dec(x_1);
x_99 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__5;
x_100 = l_Lean_Parser_ParserState_mkEOIError(x_3, x_99);
return x_100;
}
block_11:
{
if (x_7 == 0)
{
lean_object* x_8; 
x_8 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberSepFn(x_1, x_5, x_4, x_2, x_6);
return x_8;
}
else
{
lean_object* x_9; lean_object* x_10; 
x_9 = l_Lean_Parser_ParserState_setPos(x_6, x_4);
x_10 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberAuxFn(x_1, x_2, x_9);
return x_10;
}
}
block_17:
{
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; 
x_14 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1;
x_15 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_16 = l_Lake_Toml_pushLit(x_14, x_1, x_15, x_2, x_12);
return x_16;
}
else
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_12;
}
}
block_23:
{
if (x_19 == 0)
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_20 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1;
x_21 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_22 = l_Lake_Toml_pushLit(x_20, x_1, x_21, x_2, x_18);
return x_22;
}
else
{
lean_dec_ref(x_2);
lean_dec(x_1);
return x_18;
}
}
}
}
static lean_object* _init_l_Lake_Toml_numeralFn___lam__0___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("integer", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_numeralFn___lam__0___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__4;
x_2 = l_Lake_Toml_numeralFn___lam__0___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_numeralFn___lam__0___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unexpected '", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_numeralFn___lam__0___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_isHexDigit___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_numeralFn___lam__0___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hexadecimal integer", 19, 19);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_numeralFn___lam__0___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_numeralFn___lam__0___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_numeralFn___lam__0___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hexNum", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_numeralFn___lam__0___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_numeralFn___lam__0___closed__6;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_numeralFn___lam__0___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_isOctDigit___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_numeralFn___lam__0___closed__9() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("octal integer", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_numeralFn___lam__0___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_numeralFn___lam__0___closed__9;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_numeralFn___lam__0___closed__11() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("octNum", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_numeralFn___lam__0___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_numeralFn___lam__0___closed__11;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_numeralFn___lam__0___closed__13() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_isBinDigit___boxed), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_numeralFn___lam__0___closed__14() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("binary integer", 14, 14);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_numeralFn___lam__0___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_numeralFn___lam__0___closed__14;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_numeralFn___lam__0___closed__16() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("binNum", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_numeralFn___lam__0___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_numeralFn___lam__0___closed__16;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralFn___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_7; lean_object* x_8; uint8_t x_9; 
x_3 = lean_ctor_get(x_2, 2);
x_7 = lean_ctor_get(x_1, 0);
x_8 = l_Lake_Toml_numeralFn___lam__0___closed__1;
x_9 = l_Lean_Parser_InputContext_atEnd(x_7, x_3);
if (x_9 == 0)
{
lean_object* x_10; uint32_t x_11; uint32_t x_12; uint8_t x_13; 
x_10 = lean_ctor_get(x_7, 0);
x_11 = lean_string_utf8_get_fast(x_10, x_3);
x_12 = 48;
x_13 = lean_uint32_dec_eq(x_11, x_12);
if (x_13 == 0)
{
uint8_t x_14; uint8_t x_15; uint8_t x_38; 
x_14 = 1;
x_38 = lean_uint32_dec_le(x_12, x_11);
if (x_38 == 0)
{
x_15 = x_38;
goto block_37;
}
else
{
uint32_t x_39; uint8_t x_40; 
x_39 = 57;
x_40 = lean_uint32_dec_le(x_11, x_39);
x_15 = x_40;
goto block_37;
}
block_37:
{
if (x_15 == 0)
{
uint32_t x_16; uint8_t x_17; 
x_16 = 43;
x_17 = lean_uint32_dec_eq(x_11, x_16);
if (x_17 == 0)
{
uint32_t x_18; uint8_t x_19; 
x_18 = 45;
x_19 = lean_uint32_dec_eq(x_11, x_18);
if (x_19 == 0)
{
uint32_t x_20; uint8_t x_21; 
x_20 = 105;
x_21 = lean_uint32_dec_eq(x_11, x_20);
if (x_21 == 0)
{
uint32_t x_22; uint8_t x_23; 
x_22 = 110;
x_23 = lean_uint32_dec_eq(x_11, x_22);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
lean_dec_ref(x_1);
x_24 = l_Lake_Toml_numeralFn___lam__0___closed__2;
x_25 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
x_26 = lean_string_push(x_25, x_11);
x_27 = lean_string_append(x_24, x_26);
lean_dec_ref(x_26);
x_28 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
x_29 = lean_string_append(x_27, x_28);
x_30 = l_Lean_Parser_ParserState_mkUnexpectedError(x_2, x_29, x_8, x_14);
return x_30;
}
else
{
lean_object* x_31; lean_object* x_32; 
lean_inc(x_3);
x_31 = l_Lean_Parser_ParserState_next_x27___redArg(x_2, x_1, x_3);
x_32 = l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn(x_3, x_1, x_31);
return x_32;
}
}
else
{
lean_object* x_33; lean_object* x_34; 
lean_inc(x_3);
x_33 = l_Lean_Parser_ParserState_next_x27___redArg(x_2, x_1, x_3);
x_34 = l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn(x_3, x_1, x_33);
return x_34;
}
}
else
{
lean_inc(x_3);
goto block_6;
}
}
else
{
lean_inc(x_3);
goto block_6;
}
}
else
{
lean_object* x_35; lean_object* x_36; 
lean_inc(x_3);
x_35 = l_Lean_Parser_ParserState_next_x27___redArg(x_2, x_1, x_3);
x_36 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn(x_3, x_1, x_35);
return x_36;
}
}
}
else
{
lean_object* x_41; lean_object* x_42; uint8_t x_43; 
lean_inc(x_3);
x_41 = l_Lean_Parser_ParserState_next_x27___redArg(x_2, x_1, x_3);
x_42 = lean_ctor_get(x_41, 2);
lean_inc(x_42);
x_43 = l_Lean_Parser_InputContext_atEnd(x_7, x_42);
if (x_43 == 0)
{
uint32_t x_44; uint32_t x_45; uint8_t x_46; 
x_44 = lean_string_utf8_get_fast(x_10, x_42);
x_45 = 98;
x_46 = lean_uint32_dec_eq(x_44, x_45);
if (x_46 == 0)
{
uint32_t x_47; uint8_t x_48; 
x_47 = 111;
x_48 = lean_uint32_dec_eq(x_44, x_47);
if (x_48 == 0)
{
uint32_t x_49; uint8_t x_50; lean_object* x_51; uint8_t x_59; 
x_49 = 120;
x_50 = lean_uint32_dec_eq(x_44, x_49);
if (x_50 == 0)
{
uint8_t x_71; 
x_71 = lean_uint32_dec_le(x_12, x_44);
if (x_71 == 0)
{
x_59 = x_71;
goto block_70;
}
else
{
uint32_t x_72; uint8_t x_73; 
x_72 = 57;
x_73 = lean_uint32_dec_le(x_44, x_72);
x_59 = x_73;
goto block_70;
}
}
else
{
lean_object* x_74; lean_object* x_75; uint32_t x_76; lean_object* x_77; lean_object* x_78; uint8_t x_79; lean_object* x_84; lean_object* x_85; uint8_t x_86; 
x_74 = l_Lean_Parser_ParserState_next_x27___redArg(x_41, x_1, x_42);
lean_dec(x_42);
x_75 = l_Lake_Toml_numeralFn___lam__0___closed__3;
x_76 = 95;
x_77 = l_Lake_Toml_numeralFn___lam__0___closed__5;
x_78 = l_Lake_Toml_sepByChar1Fn(x_75, x_76, x_77, x_1, x_74);
x_84 = lean_ctor_get(x_78, 4);
lean_inc(x_84);
x_85 = lean_box(0);
x_86 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_84, x_85);
if (x_86 == 0)
{
x_79 = x_50;
goto block_83;
}
else
{
x_79 = x_48;
goto block_83;
}
block_83:
{
if (x_79 == 0)
{
lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_80 = l_Lake_Toml_numeralFn___lam__0___closed__7;
x_81 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_82 = l_Lake_Toml_pushLit(x_80, x_3, x_81, x_1, x_78);
return x_82;
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_78;
}
}
}
block_58:
{
lean_object* x_52; lean_object* x_53; uint8_t x_54; 
x_52 = lean_ctor_get(x_51, 4);
x_53 = lean_box(0);
lean_inc(x_52);
x_54 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_52, x_53);
if (x_54 == 0)
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_51;
}
else
{
if (x_50 == 0)
{
lean_object* x_55; lean_object* x_56; lean_object* x_57; 
x_55 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1;
x_56 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_57 = l_Lake_Toml_pushLit(x_55, x_3, x_56, x_1, x_51);
return x_57;
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_51;
}
}
}
block_70:
{
if (x_59 == 0)
{
lean_object* x_60; lean_object* x_61; 
x_60 = lean_string_utf8_next_fast(x_10, x_42);
lean_dec(x_42);
x_61 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn(x_3, x_44, x_60, x_1, x_41);
return x_61;
}
else
{
lean_object* x_62; uint32_t x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; uint8_t x_68; 
x_62 = l_Lean_Parser_ParserState_next_x27___redArg(x_41, x_1, x_42);
lean_dec(x_42);
x_63 = 58;
x_64 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7;
x_65 = l_Lake_Toml_chFn(x_63, x_64, x_1, x_62);
x_66 = lean_ctor_get(x_65, 4);
lean_inc(x_66);
x_67 = lean_box(0);
x_68 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_66, x_67);
if (x_68 == 0)
{
x_51 = x_65;
goto block_58;
}
else
{
lean_object* x_69; 
x_69 = l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn(x_50, x_1, x_65);
x_51 = x_69;
goto block_58;
}
}
}
}
else
{
lean_object* x_87; lean_object* x_88; uint32_t x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; lean_object* x_97; lean_object* x_98; uint8_t x_99; 
x_87 = l_Lean_Parser_ParserState_next_x27___redArg(x_41, x_1, x_42);
lean_dec(x_42);
x_88 = l_Lake_Toml_numeralFn___lam__0___closed__8;
x_89 = 95;
x_90 = l_Lake_Toml_numeralFn___lam__0___closed__10;
x_91 = l_Lake_Toml_sepByChar1Fn(x_88, x_89, x_90, x_1, x_87);
x_97 = lean_ctor_get(x_91, 4);
lean_inc(x_97);
x_98 = lean_box(0);
x_99 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_97, x_98);
if (x_99 == 0)
{
x_92 = x_48;
goto block_96;
}
else
{
x_92 = x_46;
goto block_96;
}
block_96:
{
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = l_Lake_Toml_numeralFn___lam__0___closed__12;
x_94 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_95 = l_Lake_Toml_pushLit(x_93, x_3, x_94, x_1, x_91);
return x_95;
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_91;
}
}
}
}
else
{
lean_object* x_100; lean_object* x_101; uint32_t x_102; lean_object* x_103; lean_object* x_104; uint8_t x_105; lean_object* x_110; lean_object* x_111; uint8_t x_112; 
x_100 = l_Lean_Parser_ParserState_next_x27___redArg(x_41, x_1, x_42);
lean_dec(x_42);
x_101 = l_Lake_Toml_numeralFn___lam__0___closed__13;
x_102 = 95;
x_103 = l_Lake_Toml_numeralFn___lam__0___closed__15;
x_104 = l_Lake_Toml_sepByChar1Fn(x_101, x_102, x_103, x_1, x_100);
x_110 = lean_ctor_get(x_104, 4);
lean_inc(x_110);
x_111 = lean_box(0);
x_112 = l_Option_beqOption____x40_Init_Data_Option_Basic_3000094388____hygCtx___hyg_3____at___Lake_Toml_commentFn_spec__0(x_110, x_111);
if (x_112 == 0)
{
x_105 = x_46;
goto block_109;
}
else
{
x_105 = x_43;
goto block_109;
}
block_109:
{
if (x_105 == 0)
{
lean_object* x_106; lean_object* x_107; lean_object* x_108; 
x_106 = l_Lake_Toml_numeralFn___lam__0___closed__17;
x_107 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_108 = l_Lake_Toml_pushLit(x_106, x_3, x_107, x_1, x_104);
return x_108;
}
else
{
lean_dec(x_3);
lean_dec_ref(x_1);
return x_104;
}
}
}
}
else
{
lean_object* x_113; lean_object* x_114; lean_object* x_115; 
lean_dec(x_42);
x_113 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6;
x_114 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_115 = l_Lake_Toml_pushLit(x_113, x_3, x_114, x_1, x_41);
return x_115;
}
}
}
else
{
lean_object* x_116; 
lean_dec_ref(x_1);
x_116 = l_Lean_Parser_ParserState_mkEOIError(x_2, x_8);
return x_116;
}
block_6:
{
lean_object* x_4; lean_object* x_5; 
x_4 = l_Lean_Parser_ParserState_next_x27___redArg(x_2, x_1, x_3);
x_5 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decimalFn(x_3, x_1, x_4);
return x_5;
}
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_alloc_closure((void*)(l_Lake_Toml_numeralFn___lam__0), 2, 0);
x_4 = l_Lean_Parser_atomicFn(x_3, x_1, x_2);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_trailingWs___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_wsFn___boxed), 2, 0);
x_2 = l_Lake_Toml_trailing(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_trailingWs() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_trailingWs___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_trailingSep___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_trailingFn___boxed), 2, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_trailingSep___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_trailingSep___closed__0;
x_2 = l_Lake_Toml_trailing(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_trailingSep() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_trailingSep___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_unquotedKeyFn___lam__0(uint32_t x_1) {
_start:
{
uint8_t x_2; uint8_t x_8; uint8_t x_14; uint32_t x_20; uint8_t x_21; 
x_20 = 65;
x_21 = lean_uint32_dec_le(x_20, x_1);
if (x_21 == 0)
{
x_14 = x_21;
goto block_19;
}
else
{
uint32_t x_22; uint8_t x_23; 
x_22 = 90;
x_23 = lean_uint32_dec_le(x_1, x_22);
x_14 = x_23;
goto block_19;
}
block_7:
{
if (x_2 == 0)
{
uint32_t x_3; uint8_t x_4; 
x_3 = 95;
x_4 = lean_uint32_dec_eq(x_1, x_3);
if (x_4 == 0)
{
uint32_t x_5; uint8_t x_6; 
x_5 = 45;
x_6 = lean_uint32_dec_eq(x_1, x_5);
return x_6;
}
else
{
return x_4;
}
}
else
{
return x_2;
}
}
block_13:
{
if (x_8 == 0)
{
uint32_t x_9; uint8_t x_10; 
x_9 = 48;
x_10 = lean_uint32_dec_le(x_9, x_1);
if (x_10 == 0)
{
x_2 = x_10;
goto block_7;
}
else
{
uint32_t x_11; uint8_t x_12; 
x_11 = 57;
x_12 = lean_uint32_dec_le(x_1, x_11);
x_2 = x_12;
goto block_7;
}
}
else
{
return x_8;
}
}
block_19:
{
if (x_14 == 0)
{
uint32_t x_15; uint8_t x_16; 
x_15 = 97;
x_16 = lean_uint32_dec_le(x_15, x_1);
if (x_16 == 0)
{
x_8 = x_16;
goto block_13;
}
else
{
uint32_t x_17; uint8_t x_18; 
x_17 = 122;
x_18 = lean_uint32_dec_le(x_1, x_17);
x_8 = x_18;
goto block_13;
}
}
else
{
return x_14;
}
}
}
}
static lean_object* _init_l_Lake_Toml_unquotedKeyFn___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unquoted key", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_unquotedKeyFn___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_unquotedKeyFn___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_alloc_closure((void*)(l_Lake_Toml_unquotedKeyFn___lam__0___boxed), 1, 0);
x_4 = l_Lake_Toml_unquotedKeyFn___closed__1;
x_5 = l_Lake_Toml_takeWhile1Fn(x_3, x_4, x_1, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn___lam__0___boxed(lean_object* x_1) {
_start:
{
uint32_t x_2; uint8_t x_3; lean_object* x_4; 
x_2 = lean_unbox_uint32(x_1);
lean_dec(x_1);
x_3 = l_Lake_Toml_unquotedKeyFn___lam__0(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKeyFn___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lake_Toml_unquotedKeyFn(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_unquotedKey___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("unquotedKey", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_unquotedKey___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_unquotedKey___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_unquotedKey___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lake_Toml_unquotedKeyFn___boxed), 2, 0);
x_4 = l_Lake_Toml_unquotedKey___closed__1;
x_5 = l_Lake_Toml_unquotedKey___closed__0;
x_6 = l_Lake_Toml_litWithAntiquot(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_Toml_unquotedKey() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_unquotedKey___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_basicString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("basicString", 11, 11);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_basicString___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_basicString___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_basicString___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lake_Toml_basicStringFn), 2, 0);
x_4 = l_Lake_Toml_basicString___closed__1;
x_5 = l_Lake_Toml_basicString___closed__0;
x_6 = l_Lake_Toml_litWithAntiquot(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_Toml_basicString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_basicString___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_literalString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("literalString", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_literalString___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_literalString___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_literalString___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lake_Toml_literalStringFn___boxed), 2, 0);
x_4 = l_Lake_Toml_literalString___closed__1;
x_5 = l_Lake_Toml_literalString___closed__0;
x_6 = l_Lake_Toml_litWithAntiquot(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_Toml_literalString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_literalString___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_mlBasicString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mlBasicString", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_mlBasicString___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_mlBasicString___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_mlBasicString___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lake_Toml_mlBasicStringFn), 2, 0);
x_4 = l_Lake_Toml_mlBasicString___closed__1;
x_5 = l_Lake_Toml_mlBasicString___closed__0;
x_6 = l_Lake_Toml_litWithAntiquot(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_Toml_mlBasicString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_mlBasicString___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_mlLiteralString___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("mlLiteralString", 15, 15);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_mlLiteralString___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_mlLiteralString___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_mlLiteralString___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lake_Toml_mlLiteralStringFn), 2, 0);
x_4 = l_Lake_Toml_mlLiteralString___closed__1;
x_5 = l_Lake_Toml_mlLiteralString___closed__0;
x_6 = l_Lake_Toml_litWithAntiquot(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_Toml_mlLiteralString() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_mlLiteralString___closed__2;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_quotedKey___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_literalString;
x_2 = l_Lake_Toml_basicString;
x_3 = l_Lean_Parser_orelse(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_quotedKey() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_quotedKey___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("simpleKey", 9, 9);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_simpleKey___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_quotedKey;
x_2 = l_Lake_Toml_unquotedKey;
x_3 = l_Lean_Parser_orelse(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lake_Toml_simpleKey___closed__2;
x_3 = l_Lake_Toml_simpleKey___closed__1;
x_4 = l_Lake_Toml_simpleKey___closed__0;
x_5 = l_Lean_Parser_nodeWithAntiquot(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_simpleKey___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("key", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_key___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_key___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__3() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(".", 1, 1);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__4() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 46;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_key___closed__4;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
x_2 = l_Lake_Toml_key___closed__5;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_key___closed__6;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; uint32_t x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_2 = l_Lake_Toml_key___closed__7;
x_3 = 46;
x_4 = l_Lake_Toml_chAtom(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_trailingWs;
x_2 = l_Lake_Toml_key___closed__8;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_key___closed__9;
x_2 = l_Lake_Toml_trailingWs;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__11() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lake_Toml_key___closed__10;
x_3 = l_Lake_Toml_key___closed__3;
x_4 = l_Lake_Toml_simpleKey;
x_5 = l_Lean_Parser_sepBy1(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_key___closed__11;
x_2 = l_Lake_Toml_key___closed__2;
x_3 = l_Lean_Parser_setExpected(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_key___closed__13() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lake_Toml_key___closed__12;
x_3 = l_Lake_Toml_key___closed__1;
x_4 = l_Lake_Toml_key___closed__0;
x_5 = l_Lean_Parser_nodeWithAntiquot(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_Toml_key() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_key___closed__13;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("stdTable", 8, 8);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_stdTable___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("table", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_stdTable___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint32_t x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_2 = l_Lake_Toml_stdTable___closed__3;
x_3 = 91;
x_4 = l_Lake_Toml_chAtom(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__5() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 91;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_stdTable___closed__5;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
x_2 = l_Lake_Toml_stdTable___closed__6;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_stdTable___closed__7;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; uint32_t x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_2 = l_Lake_Toml_stdTable___closed__8;
x_3 = 91;
x_4 = l_Lake_Toml_chAtom(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__10() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'['", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_stdTable___closed__10;
x_2 = l_Lake_Toml_stdTable___closed__9;
x_3 = l_Lean_Parser_notFollowedBy(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_stdTable___closed__11;
x_2 = l_Lake_Toml_stdTable___closed__4;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_stdTable___closed__12;
x_2 = l_Lean_Parser_atomic(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__14() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 93;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_stdTable___closed__14;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__16() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
x_2 = l_Lake_Toml_stdTable___closed__15;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__17() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_stdTable___closed__16;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__18() {
_start:
{
lean_object* x_1; lean_object* x_2; uint32_t x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_2 = l_Lake_Toml_stdTable___closed__17;
x_3 = 93;
x_4 = l_Lake_Toml_chAtom(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__19() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_stdTable___closed__18;
x_2 = l_Lake_Toml_trailingWs;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__20() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_stdTable___closed__19;
x_2 = l_Lake_Toml_key;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__21() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_stdTable___closed__20;
x_2 = l_Lake_Toml_trailingWs;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__22() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_stdTable___closed__21;
x_2 = l_Lake_Toml_stdTable___closed__13;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_stdTable___closed__23() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lake_Toml_stdTable___closed__22;
x_3 = l_Lake_Toml_stdTable___closed__1;
x_4 = l_Lake_Toml_stdTable___closed__0;
x_5 = l_Lean_Parser_nodeWithAntiquot(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_Toml_stdTable() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_stdTable___closed__23;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("arrayTable", 10, 10);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_arrayTable___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_stdTable___closed__9;
x_2 = l_Lake_Toml_stdTable___closed__4;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_arrayTable___closed__2;
x_2 = l_Lean_Parser_atomic(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_stdTable___closed__18;
x_2 = l_Lean_Parser_andthen(x_1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_arrayTable___closed__4;
x_2 = l_Lake_Toml_trailingWs;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_arrayTable___closed__5;
x_2 = l_Lake_Toml_key;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_arrayTable___closed__6;
x_2 = l_Lake_Toml_trailingWs;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_arrayTable___closed__7;
x_2 = l_Lake_Toml_arrayTable___closed__3;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable___closed__9() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lake_Toml_arrayTable___closed__8;
x_3 = l_Lake_Toml_arrayTable___closed__1;
x_4 = l_Lake_Toml_arrayTable___closed__0;
x_5 = l_Lean_Parser_nodeWithAntiquot(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_arrayTable___closed__9;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_table___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_arrayTable;
x_2 = l_Lake_Toml_stdTable;
x_3 = l_Lean_Parser_orelse(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_table() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_table___closed__0;
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("keyval", 6, 6);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 61;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; uint32_t x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5;
x_3 = 61;
x_4 = l_Lake_Toml_chAtom(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; 
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1;
x_4 = l_Lake_Toml_key;
x_5 = l_Lake_Toml_trailingWs;
x_6 = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6;
x_7 = l_Lean_Parser_andthen(x_5, x_1);
x_8 = l_Lean_Parser_andthen(x_6, x_7);
x_9 = l_Lean_Parser_andthen(x_5, x_8);
x_10 = l_Lean_Parser_andthen(x_4, x_9);
x_11 = 1;
x_12 = l_Lean_Parser_nodeWithAntiquot(x_2, x_3, x_10, x_11);
return x_12;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("expression", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0;
x_4 = l_Lean_Parser_mkAntiquot(x_3, x_2, x_1, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(x_1);
x_4 = l_Lake_Toml_table;
x_5 = l_Lean_Parser_orelse(x_3, x_4);
x_6 = l_Lean_Parser_withAntiquot(x_2, x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_Toml_header___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("header", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_header___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_header___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_header___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = l_Lake_Toml_trailingSep___closed__0;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_4 = l_Lake_Toml_header___closed__1;
x_5 = l_Lake_Toml_header___closed__0;
x_6 = l_Lake_Toml_litWithAntiquot(x_5, x_4, x_3, x_2, x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_Toml_header() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_header___closed__2;
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("toml", 4, 4);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("sepBy", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__2;
x_2 = l_Lean_Name_mkStr1(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__4() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("*", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__4;
x_2 = l_Lean_Parser_symbol(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("line break", 10, 10);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__6;
x_2 = l_Lean_Parser_checkLinebreakBefore(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8() {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Parser_pushNone;
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7;
x_3 = l_Lean_Parser_andthen(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1;
x_4 = l_Lake_Toml_header;
x_5 = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(x_1);
x_6 = l_Lake_Toml_trailingSep;
x_7 = l_Lean_Parser_andthen(x_5, x_6);
x_8 = 1;
x_9 = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__3;
x_10 = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5;
x_11 = l_Lean_Parser_withAntiquotSpliceAndSuffix(x_9, x_7, x_10);
x_12 = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__9;
x_13 = l_Lean_Parser_sepByNoAntiquot(x_11, x_12, x_8);
x_14 = l_Lean_Parser_andthen(x_4, x_13);
x_15 = l_Lean_Parser_nodeWithAntiquot(x_2, x_3, x_14, x_8);
return x_15;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inlineTable", 11, 11);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("inline-table", 12, 12);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint32_t x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_trailingSep___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__3;
x_3 = 123;
x_4 = l_Lake_Toml_chAtom(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked(",", 1, 1);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 44;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; uint32_t x_3; lean_object* x_4; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_wsFn___boxed), 2, 0);
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9;
x_3 = 44;
x_4 = l_Lake_Toml_chAtom(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11() {
_start:
{
uint32_t x_1; lean_object* x_2; lean_object* x_3; 
x_1 = 125;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3;
x_3 = lean_string_push(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12;
x_3 = lean_string_append(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15() {
_start:
{
lean_object* x_1; lean_object* x_2; uint32_t x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14;
x_3 = 125;
x_4 = l_Lake_Toml_chAtom(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; uint8_t x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1;
x_4 = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4;
x_5 = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(x_1);
x_6 = l_Lake_Toml_trailingWs;
x_7 = l_Lean_Parser_andthen(x_5, x_6);
x_8 = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5;
x_9 = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10;
x_10 = 0;
x_11 = l_Lean_Parser_sepBy(x_7, x_8, x_9, x_10);
x_12 = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15;
x_13 = l_Lean_Parser_andthen(x_11, x_12);
x_14 = l_Lean_Parser_andthen(x_4, x_13);
x_15 = l_Lean_Parser_nodeWithAntiquot(x_2, x_3, x_14, x_10);
return x_15;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("array", 5, 5);
return x_1;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; uint32_t x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_trailingSep___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__2;
x_3 = 91;
x_4 = l_Lake_Toml_chAtom(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; uint32_t x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_trailingSep___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9;
x_3 = 44;
x_4 = l_Lake_Toml_chAtom(x_3, x_2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; uint8_t x_14; lean_object* x_15; 
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1;
x_4 = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3;
x_5 = l_Lake_Toml_trailingSep;
x_6 = l_Lean_Parser_andthen(x_1, x_5);
x_7 = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5;
x_8 = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4;
x_9 = 1;
x_10 = l_Lean_Parser_sepBy(x_6, x_7, x_8, x_9);
x_11 = l_Lake_Toml_stdTable___closed__18;
x_12 = l_Lean_Parser_andthen(x_10, x_11);
x_13 = l_Lean_Parser_andthen(x_4, x_12);
x_14 = 0;
x_15 = l_Lean_Parser_nodeWithAntiquot(x_2, x_3, x_13, x_14);
return x_15;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("string", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_string___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_string___closed__0;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_literalString;
x_2 = l_Lake_Toml_mlLiteralString;
x_3 = l_Lean_Parser_orelse(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_string___closed__3;
x_2 = l_Lake_Toml_basicString;
x_3 = l_Lean_Parser_orelse(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_string___closed__4;
x_2 = l_Lake_Toml_mlBasicString;
x_3 = l_Lean_Parser_orelse(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_string___closed__5;
x_2 = l_Lake_Toml_string___closed__2;
x_3 = l_Lean_Parser_setExpected(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_string___closed__7() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lake_Toml_string___closed__6;
x_3 = l_Lake_Toml_string___closed__1;
x_4 = l_Lake_Toml_string___closed__0;
x_5 = l_Lean_Parser_nodeWithAntiquot(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_Toml_string() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_string___closed__7;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_true___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("true", 4, 4);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_true___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_true___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_true___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'true'", 6, 6);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_true___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_true___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_true___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_true___closed__3;
x_2 = l_Lake_Toml_true___closed__0;
x_3 = lean_alloc_closure((void*)(l_Lake_Toml_strFn), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_true___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_2 = l_Lake_Toml_true___closed__4;
x_3 = l_Lake_Toml_true___closed__1;
x_4 = l_Lake_Toml_lit(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_true() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_true___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_false___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("false", 5, 5);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_false___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_false___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_false___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("'false'", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_false___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lake_Toml_false___closed__2;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_false___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_false___closed__3;
x_2 = l_Lake_Toml_false___closed__0;
x_3 = lean_alloc_closure((void*)(l_Lake_Toml_strFn), 4, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_false___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_2 = l_Lake_Toml_false___closed__4;
x_3 = l_Lake_Toml_false___closed__1;
x_4 = l_Lake_Toml_lit(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_false() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_false___closed__5;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_boolean___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("boolean", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_boolean___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_boolean___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_boolean___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_false;
x_2 = l_Lake_Toml_true;
x_3 = l_Lean_Parser_orelse(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_boolean___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 0;
x_2 = l_Lake_Toml_boolean___closed__2;
x_3 = l_Lake_Toml_boolean___closed__1;
x_4 = l_Lake_Toml_boolean___closed__0;
x_5 = l_Lean_Parser_nodeWithAntiquot(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_Toml_boolean() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_boolean___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2;
x_4 = l_Lean_Parser_mkAntiquot(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__1() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5;
x_4 = l_Lean_Parser_mkAntiquot(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__2() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lake_Toml_numeralFn___lam__0___closed__17;
x_3 = l_Lake_Toml_numeralFn___lam__0___closed__16;
x_4 = l_Lean_Parser_mkAntiquot(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lake_Toml_numeralFn___lam__0___closed__12;
x_3 = l_Lake_Toml_numeralFn___lam__0___closed__11;
x_4 = l_Lean_Parser_mkAntiquot(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__4() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l_Lake_Toml_numeralFn___lam__0___closed__7;
x_3 = l_Lake_Toml_numeralFn___lam__0___closed__6;
x_4 = l_Lean_Parser_mkAntiquot(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__5() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0;
x_4 = l_Lean_Parser_mkAntiquot(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__6() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("numeral", 7, 7);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_numeralAntiquot___closed__6;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__8() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = 1;
x_2 = l_Lake_Toml_numeralAntiquot___closed__7;
x_3 = l_Lake_Toml_numeralAntiquot___closed__6;
x_4 = l_Lean_Parser_mkAntiquot(x_3, x_2, x_1, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_numeralAntiquot___closed__8;
x_2 = l_Lake_Toml_numeralAntiquot___closed__5;
x_3 = l_Lean_Parser_orelse(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__10() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_numeralAntiquot___closed__9;
x_2 = l_Lake_Toml_numeralAntiquot___closed__4;
x_3 = l_Lean_Parser_orelse(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__11() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_numeralAntiquot___closed__10;
x_2 = l_Lake_Toml_numeralAntiquot___closed__3;
x_3 = l_Lean_Parser_orelse(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__12() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_numeralAntiquot___closed__11;
x_2 = l_Lake_Toml_numeralAntiquot___closed__2;
x_3 = l_Lean_Parser_orelse(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__13() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_numeralAntiquot___closed__12;
x_2 = l_Lake_Toml_numeralAntiquot___closed__1;
x_3 = l_Lean_Parser_orelse(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot___closed__14() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_numeralAntiquot___closed__13;
x_2 = l_Lake_Toml_numeralAntiquot___closed__0;
x_3 = l_Lean_Parser_orelse(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_numeralAntiquot() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_numeralAntiquot___closed__14;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_numeral___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_numeralFn), 2, 0);
x_2 = l_Lake_Toml_dynamicNode(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_numeral___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_numeral___closed__0;
x_2 = l_Lake_Toml_numeralAntiquot;
x_3 = l_Lean_Parser_withAntiquot(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_numeral() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_numeral___closed__1;
return x_1;
}
}
LEAN_EXPORT uint8_t l_Lake_Toml_numeralOfKind___lam__0(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; 
x_3 = l_Lean_Syntax_isOfKind(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_numeralOfKind___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("illegal numeral kind", 20, 20);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralOfKind(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_3 = lean_alloc_closure((void*)(l_Lake_Toml_numeralOfKind___lam__0___boxed), 2, 1);
lean_closure_set(x_3, 0, x_2);
x_4 = l_Lake_Toml_numeral;
x_5 = lean_box(0);
x_6 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_6, 0, x_1);
lean_ctor_set(x_6, 1, x_5);
x_7 = l_Lake_Toml_numeralOfKind___closed__0;
x_8 = l_Lean_Parser_checkStackTop(x_3, x_7);
x_9 = l_Lean_Parser_setExpected(x_6, x_8);
x_10 = l_Lean_Parser_andthen(x_4, x_9);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_numeralOfKind___lam__0___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lake_Toml_numeralOfKind___lam__0(x_1, x_2);
lean_dec(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_float___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2;
x_3 = l_Lake_Toml_numeralOfKind(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_float() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_float___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_decInt___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0;
x_3 = l_Lake_Toml_numeralOfKind(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_decInt() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_decInt___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_binNum___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("binary number", 13, 13);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_binNum___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_numeralFn___lam__0___closed__17;
x_2 = l_Lake_Toml_binNum___closed__0;
x_3 = l_Lake_Toml_numeralOfKind(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_binNum() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_binNum___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_octNum___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("octal number", 12, 12);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_octNum___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_numeralFn___lam__0___closed__12;
x_2 = l_Lake_Toml_octNum___closed__0;
x_3 = l_Lake_Toml_numeralOfKind(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_octNum() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_octNum___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_hexNum___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("hexadecimal number", 18, 18);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_hexNum___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_numeralFn___lam__0___closed__7;
x_2 = l_Lake_Toml_hexNum___closed__0;
x_3 = l_Lake_Toml_numeralOfKind(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_hexNum() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_hexNum___closed__1;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_dateTime___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2;
x_3 = l_Lake_Toml_numeralOfKind(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_dateTime() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_dateTime___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_valCore(lean_object* x_1) {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; 
x_2 = l_Lake_Toml_string;
x_3 = l_Lake_Toml_boolean;
x_4 = l_Lake_Toml_numeral;
lean_inc_ref(x_1);
x_5 = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(x_1);
x_6 = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(x_1);
x_7 = l_Lean_Parser_orelse(x_5, x_6);
x_8 = l_Lean_Parser_orelse(x_4, x_7);
x_9 = l_Lean_Parser_orelse(x_3, x_8);
x_10 = l_Lean_Parser_orelse(x_2, x_9);
return x_10;
}
}
static lean_object* _init_l_Lake_Toml_val___closed__0() {
_start:
{
lean_object* x_1; 
x_1 = lean_mk_string_unchecked("val", 3, 3);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_val___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l_Lake_Toml_val___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0;
x_4 = l_Lean_Name_mkStr3(x_3, x_2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_val___closed__2() {
_start:
{
lean_object* x_1; 
x_1 = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_valCore), 1, 0);
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_val___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_1 = 1;
x_2 = l_Lake_Toml_val___closed__2;
x_3 = l_Lake_Toml_val___closed__1;
x_4 = l_Lake_Toml_val___closed__0;
x_5 = l_Lake_Toml_recNodeWithAntiquot(x_4, x_3, x_2, x_1);
return x_5;
}
}
static lean_object* _init_l_Lake_Toml_val() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_val___closed__3;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_array___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_val;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_array() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_array___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_inlineTable___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_val;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_inlineTable() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_inlineTable___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_keyval___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_val;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_keyval() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_keyval___closed__0;
return x_1;
}
}
static lean_object* _init_l_Lake_Toml_expression___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_val;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_expression() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_expression___closed__0;
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_header_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = l_Lake_Toml_header___closed__0;
x_7 = l_Lake_Toml_header___closed__1;
x_8 = 0;
x_9 = l_Lake_Toml_litWithAntiquot_formatter___redArg(x_6, x_7, x_8, x_1, x_2, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = l_Lake_Toml_unquotedKey___closed__0;
x_7 = l_Lake_Toml_unquotedKey___closed__1;
x_8 = 0;
x_9 = l_Lake_Toml_litWithAntiquot_formatter___redArg(x_6, x_7, x_8, x_1, x_2, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = l_Lake_Toml_basicString___closed__0;
x_7 = l_Lake_Toml_basicString___closed__1;
x_8 = 0;
x_9 = l_Lake_Toml_litWithAntiquot_formatter___redArg(x_6, x_7, x_8, x_1, x_2, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = l_Lake_Toml_literalString___closed__0;
x_7 = l_Lake_Toml_literalString___closed__1;
x_8 = 0;
x_9 = l_Lake_Toml_litWithAntiquot_formatter___redArg(x_6, x_7, x_8, x_1, x_2, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lake_Toml_basicString_formatter), 5, 0);
x_7 = lean_alloc_closure((void*)(l_Lake_Toml_literalString_formatter), 5, 0);
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey_formatter___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_quotedKey_formatter), 5, 0);
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_unquotedKey_formatter), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_6 = l_Lake_Toml_simpleKey___closed__0;
x_7 = l_Lake_Toml_simpleKey___closed__1;
x_8 = l_Lake_Toml_simpleKey_formatter___closed__0;
x_9 = 1;
x_10 = l_Lean_Parser_nodeWithAntiquot_formatter(x_6, x_7, x_8, x_9, x_1, x_2, x_3, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_epsilon_formatter___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Toml_epsilon_formatter___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Toml_trailingWs_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__0___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 46;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_2 = l_Lake_Toml_key___closed__7;
x_3 = l_Lake_Toml_key_formatter___closed__0___boxed__const__1;
x_4 = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
x_2 = l_Lake_Toml_key_formatter___closed__0;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_key_formatter___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = l_Lake_Toml_key_formatter___closed__2;
x_3 = l_Lake_Toml_key___closed__3;
x_4 = lean_alloc_closure((void*)(l_Lake_Toml_simpleKey_formatter), 5, 0);
x_5 = lean_box(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_formatter___boxed), 9, 4);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_Toml_key_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_key_formatter___closed__3;
x_2 = l_Lake_Toml_key___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_setExpected_formatter___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_key_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_6 = l_Lake_Toml_key___closed__0;
x_7 = l_Lake_Toml_key___closed__1;
x_8 = l_Lake_Toml_key_formatter___closed__4;
x_9 = 1;
x_10 = l_Lean_Parser_nodeWithAntiquot_formatter(x_6, x_7, x_8, x_9, x_1, x_2, x_3, x_4, x_5);
return x_10;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 61;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1;
x_4 = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_7 = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0;
x_8 = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1;
x_9 = lean_alloc_closure((void*)(l_Lake_Toml_key_formatter), 5, 0);
x_10 = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
x_11 = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0;
lean_inc_ref(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_15, 0, x_9);
lean_closure_set(x_15, 1, x_14);
x_16 = 1;
x_17 = l_Lean_Parser_nodeWithAntiquot_formatter(x_7, x_8, x_15, x_16, x_2, x_3, x_4, x_5, x_6);
return x_17;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 91;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_2 = l_Lake_Toml_stdTable___closed__3;
x_3 = l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1;
x_4 = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 91;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_2 = l_Lake_Toml_stdTable___closed__8;
x_3 = l_Lake_Toml_stdTable_formatter___closed__1___boxed__const__1;
x_4 = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_stdTable_formatter___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_notFollowedBy_formatter___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_stdTable_formatter___closed__2;
x_2 = l_Lake_Toml_stdTable_formatter___closed__0;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_stdTable_formatter___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 93;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_2 = l_Lake_Toml_stdTable___closed__17;
x_3 = l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1;
x_4 = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_formatter___boxed), 8, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_stdTable_formatter___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__7() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_stdTable_formatter___closed__6;
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_key_formatter), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__8() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_stdTable_formatter___closed__7;
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_formatter___closed__9() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_stdTable_formatter___closed__8;
x_2 = l_Lake_Toml_stdTable_formatter___closed__4;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_6 = l_Lake_Toml_stdTable___closed__0;
x_7 = l_Lake_Toml_stdTable___closed__1;
x_8 = l_Lake_Toml_stdTable_formatter___closed__9;
x_9 = 0;
x_10 = l_Lean_Parser_nodeWithAntiquot_formatter(x_6, x_7, x_8, x_9, x_1, x_2, x_3, x_4, x_5);
return x_10;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_stdTable_formatter___closed__1;
x_2 = l_Lake_Toml_stdTable_formatter___closed__0;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_arrayTable_formatter___closed__0;
x_2 = lean_alloc_closure((void*)(l_Lean_Parser_atomic_formatter), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_stdTable_formatter___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_arrayTable_formatter___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_arrayTable_formatter___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_key_formatter), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_arrayTable_formatter___closed__4;
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_formatter___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_formatter___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_arrayTable_formatter___closed__5;
x_2 = l_Lake_Toml_arrayTable_formatter___closed__1;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_6 = l_Lake_Toml_arrayTable___closed__0;
x_7 = l_Lake_Toml_arrayTable___closed__1;
x_8 = l_Lake_Toml_arrayTable_formatter___closed__6;
x_9 = 0;
x_10 = l_Lean_Parser_nodeWithAntiquot_formatter(x_6, x_7, x_8, x_9, x_1, x_2, x_3, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_table_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_formatter), 5, 0);
x_7 = lean_alloc_closure((void*)(l_Lake_Toml_arrayTable_formatter), 5, 0);
x_8 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 1;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0;
x_4 = lean_box(x_1);
x_5 = lean_box(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_formatter___boxed), 9, 4);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_4);
lean_closure_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___closed__0;
x_8 = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter), 6, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_alloc_closure((void*)(l_Lake_Toml_table_formatter), 5, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_orelse_formatter), 7, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_PrettyPrinter_Formatter_orelse_formatter(x_7, x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_epsilon_formatter___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Toml_epsilon_formatter___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_formatter___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Toml_trailingSep_formatter(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0;
x_8 = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1;
x_9 = lean_alloc_closure((void*)(l_Lake_Toml_header_formatter), 5, 0);
x_10 = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter), 6, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_alloc_closure((void*)(l_Lake_Toml_trailingSep_formatter___boxed), 5, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_closure((void*)(l_Lake_Toml_sepByLinebreak_formatter___boxed), 7, 2);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Formatter_andthen_formatter), 7, 2);
lean_closure_set(x_16, 0, x_9);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Lean_Parser_nodeWithAntiquot_formatter(x_7, x_8, x_16, x_13, x_2, x_3, x_4, x_5, x_6);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_val_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_6 = l_Lake_Toml_val___closed__0;
x_7 = l_Lake_Toml_val___closed__1;
x_8 = l_Lake_Toml_val___closed__2;
x_9 = 1;
x_10 = l_Lake_Toml_recNodeWithAntiquot_formatter(x_6, x_7, x_8, x_9, x_1, x_2, x_3, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_toml_formatter(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lake_Toml_val_formatter), 5, 0);
x_7 = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_formatter(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_header_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = l_Lake_Toml_header___closed__0;
x_7 = l_Lake_Toml_header___closed__1;
x_8 = 0;
x_9 = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(x_6, x_7, x_8, x_1, x_2, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_unquotedKey_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = l_Lake_Toml_unquotedKey___closed__0;
x_7 = l_Lake_Toml_unquotedKey___closed__1;
x_8 = 0;
x_9 = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(x_6, x_7, x_8, x_1, x_2, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_basicString_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = l_Lake_Toml_basicString___closed__0;
x_7 = l_Lake_Toml_basicString___closed__1;
x_8 = 0;
x_9 = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(x_6, x_7, x_8, x_1, x_2, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_literalString_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; lean_object* x_9; 
x_6 = l_Lake_Toml_literalString___closed__0;
x_7 = l_Lake_Toml_literalString___closed__1;
x_8 = 0;
x_9 = l_Lake_Toml_litWithAntiquot_parenthesizer___redArg(x_6, x_7, x_8, x_1, x_2, x_3, x_4, x_5);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_quotedKey_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lake_Toml_basicString_parenthesizer), 5, 0);
x_7 = lean_alloc_closure((void*)(l_Lake_Toml_literalString_parenthesizer), 5, 0);
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l_Lake_Toml_simpleKey_parenthesizer___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_quotedKey_parenthesizer), 5, 0);
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_unquotedKey_parenthesizer), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_simpleKey_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_6 = l_Lake_Toml_simpleKey___closed__0;
x_7 = l_Lake_Toml_simpleKey___closed__1;
x_8 = l_Lake_Toml_simpleKey_parenthesizer___closed__0;
x_9 = 1;
x_10 = l_Lean_Parser_nodeWithAntiquot_parenthesizer(x_6, x_7, x_8, x_9, x_1, x_2, x_3, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_epsilon_parenthesizer___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Toml_epsilon_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingWs_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Toml_trailingWs_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__0___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 46;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_2 = l_Lake_Toml_key___closed__7;
x_3 = l_Lake_Toml_key_parenthesizer___closed__0___boxed__const__1;
x_4 = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
x_2 = l_Lake_Toml_key_parenthesizer___closed__0;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_key_parenthesizer___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__3() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 0;
x_2 = l_Lake_Toml_key_parenthesizer___closed__2;
x_3 = l_Lake_Toml_key___closed__3;
x_4 = lean_alloc_closure((void*)(l_Lake_Toml_simpleKey_parenthesizer), 5, 0);
x_5 = lean_box(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_sepBy1_parenthesizer___boxed), 9, 4);
lean_closure_set(x_6, 0, x_4);
lean_closure_set(x_6, 1, x_3);
lean_closure_set(x_6, 2, x_2);
lean_closure_set(x_6, 3, x_5);
return x_6;
}
}
static lean_object* _init_l_Lake_Toml_key_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_key_parenthesizer___closed__3;
x_2 = l_Lake_Toml_key___closed__2;
x_3 = lean_alloc_closure((void*)(l_Lean_Parser_setExpected_parenthesizer___boxed), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_key_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_6 = l_Lake_Toml_key___closed__0;
x_7 = l_Lake_Toml_key___closed__1;
x_8 = l_Lake_Toml_key_parenthesizer___closed__4;
x_9 = 1;
x_10 = l_Lean_Parser_nodeWithAntiquot_parenthesizer(x_6, x_7, x_8, x_9, x_1, x_2, x_3, x_4, x_5);
return x_10;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 61;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0___boxed__const__1;
x_4 = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_1);
return x_4;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; 
x_7 = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0;
x_8 = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1;
x_9 = lean_alloc_closure((void*)(l_Lake_Toml_key_parenthesizer), 5, 0);
x_10 = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
x_11 = l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0;
lean_inc_ref(x_10);
x_12 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_1);
x_13 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_13, 0, x_11);
lean_closure_set(x_13, 1, x_12);
x_14 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_14, 0, x_10);
lean_closure_set(x_14, 1, x_13);
x_15 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_15, 0, x_9);
lean_closure_set(x_15, 1, x_14);
x_16 = 1;
x_17 = l_Lean_Parser_nodeWithAntiquot_parenthesizer(x_7, x_8, x_15, x_16, x_2, x_3, x_4, x_5, x_6);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_8;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__0___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 91;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_2 = l_Lake_Toml_stdTable___closed__3;
x_3 = l_Lake_Toml_stdTable_parenthesizer___closed__0___boxed__const__1;
x_4 = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__1___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 91;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_2 = l_Lake_Toml_stdTable___closed__8;
x_3 = l_Lake_Toml_stdTable_parenthesizer___closed__1___boxed__const__1;
x_4 = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_stdTable_parenthesizer___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_notFollowedBy_parenthesizer___boxed), 6, 1);
lean_closure_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__3___boxed__const__1() {
_start:
{
uint32_t x_1; lean_object* x_2; 
x_1 = 93;
x_2 = lean_box_uint32(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_1 = l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4;
x_2 = l_Lake_Toml_stdTable___closed__17;
x_3 = l_Lake_Toml_stdTable_parenthesizer___closed__3___boxed__const__1;
x_4 = lean_alloc_closure((void*)(l_Lake_Toml_chAtom_parenthesizer___boxed), 8, 3);
lean_closure_set(x_4, 0, x_3);
lean_closure_set(x_4, 1, x_2);
lean_closure_set(x_4, 2, x_1);
return x_4;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_stdTable_parenthesizer___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_stdTable_parenthesizer___closed__4;
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_key_parenthesizer), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_stdTable_parenthesizer___closed__6() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_stdTable_parenthesizer___closed__5;
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_stdTable_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_6 = l_Lake_Toml_stdTable___closed__0;
x_7 = l_Lake_Toml_stdTable___closed__1;
x_8 = l_Lake_Toml_stdTable_parenthesizer___closed__0;
x_9 = l_Lake_Toml_stdTable_parenthesizer___closed__2;
x_10 = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_parenthesizer___lam__0), 7, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lake_Toml_stdTable_parenthesizer___closed__6;
x_12 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
x_13 = 0;
x_14 = l_Lean_Parser_nodeWithAntiquot_parenthesizer(x_6, x_7, x_12, x_13, x_1, x_2, x_3, x_4, x_5);
return x_14;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_stdTable_parenthesizer___closed__1;
x_2 = l_Lake_Toml_stdTable_parenthesizer___closed__0;
x_3 = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_parenthesizer___lam__0), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_stdTable_parenthesizer___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_2, 0, x_1);
lean_closure_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__2() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_arrayTable_parenthesizer___closed__1;
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__3() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_arrayTable_parenthesizer___closed__2;
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_key_parenthesizer), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__4() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_arrayTable_parenthesizer___closed__3;
x_2 = lean_alloc_closure((void*)(l_Lake_Toml_trailingWs_parenthesizer___boxed), 5, 0);
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_arrayTable_parenthesizer___closed__5() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_arrayTable_parenthesizer___closed__4;
x_2 = l_Lake_Toml_arrayTable_parenthesizer___closed__0;
x_3 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_3, 0, x_2);
lean_closure_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_arrayTable_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_6 = l_Lake_Toml_arrayTable___closed__0;
x_7 = l_Lake_Toml_arrayTable___closed__1;
x_8 = l_Lake_Toml_arrayTable_parenthesizer___closed__5;
x_9 = 0;
x_10 = l_Lean_Parser_nodeWithAntiquot_parenthesizer(x_6, x_7, x_8, x_9, x_1, x_2, x_3, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_table_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_alloc_closure((void*)(l_Lake_Toml_stdTable_parenthesizer), 5, 0);
x_7 = lean_alloc_closure((void*)(l_Lake_Toml_arrayTable_parenthesizer), 5, 0);
x_8 = l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer(x_6, x_7, x_1, x_2, x_3, x_4, x_5);
return x_8;
}
}
static lean_object* _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___closed__0() {
_start:
{
uint8_t x_1; lean_object* x_2; lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_1 = 1;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1;
x_3 = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0;
x_4 = lean_box(x_1);
x_5 = lean_box(x_1);
x_6 = lean_alloc_closure((void*)(l_Lean_Parser_mkAntiquot_parenthesizer___boxed), 9, 4);
lean_closure_set(x_6, 0, x_3);
lean_closure_set(x_6, 1, x_2);
lean_closure_set(x_6, 2, x_4);
lean_closure_set(x_6, 3, x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; 
x_7 = l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___closed__0;
x_8 = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer), 6, 1);
lean_closure_set(x_8, 0, x_1);
x_9 = lean_alloc_closure((void*)(l_Lake_Toml_table_parenthesizer), 5, 0);
x_10 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_orelse_parenthesizer), 7, 2);
lean_closure_set(x_10, 0, x_8);
lean_closure_set(x_10, 1, x_9);
x_11 = l_Lean_PrettyPrinter_Parenthesizer_withAntiquot_parenthesizer(x_7, x_10, x_2, x_3, x_4, x_5, x_6);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer___redArg(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lake_Toml_epsilon_parenthesizer___redArg(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Toml_epsilon_parenthesizer___redArg(x_5);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_trailingSep_parenthesizer___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lake_Toml_trailingSep_parenthesizer(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_7 = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0;
x_8 = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1;
x_9 = lean_alloc_closure((void*)(l_Lake_Toml_header_parenthesizer), 5, 0);
x_10 = lean_alloc_closure((void*)(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer), 6, 1);
lean_closure_set(x_10, 0, x_1);
x_11 = lean_alloc_closure((void*)(l_Lake_Toml_trailingSep_parenthesizer___boxed), 5, 0);
x_12 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_12, 0, x_10);
lean_closure_set(x_12, 1, x_11);
x_13 = 1;
x_14 = lean_box(x_13);
x_15 = lean_alloc_closure((void*)(l_Lake_Toml_sepByLinebreak_parenthesizer___boxed), 7, 2);
lean_closure_set(x_15, 0, x_12);
lean_closure_set(x_15, 1, x_14);
x_16 = lean_alloc_closure((void*)(l_Lean_PrettyPrinter_Parenthesizer_andthen_parenthesizer), 7, 2);
lean_closure_set(x_16, 0, x_9);
lean_closure_set(x_16, 1, x_15);
x_17 = l_Lean_Parser_nodeWithAntiquot_parenthesizer(x_7, x_8, x_16, x_13, x_2, x_3, x_4, x_5, x_6);
return x_17;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_val_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; uint8_t x_9; lean_object* x_10; 
x_6 = l_Lake_Toml_val___closed__0;
x_7 = l_Lake_Toml_val___closed__1;
x_8 = l_Lake_Toml_val___closed__2;
x_9 = 1;
x_10 = l_Lake_Toml_recNodeWithAntiquot_parenthesizer(x_6, x_7, x_8, x_9, x_1, x_2, x_3, x_4, x_5);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lake_Toml_toml_parenthesizer(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; lean_object* x_7; 
x_6 = lean_alloc_closure((void*)(l_Lake_Toml_val_parenthesizer), 5, 0);
x_7 = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore_parenthesizer(x_6, x_1, x_2, x_3, x_4, x_5);
return x_7;
}
}
static lean_object* _init_l_Lake_Toml_toml___closed__0() {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lake_Toml_val;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore(x_1);
return x_2;
}
}
static lean_object* _init_l_Lake_Toml_toml___closed__1() {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = l_Lake_Toml_toml___closed__0;
x_2 = l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1;
x_3 = l_Lean_Parser_withCache(x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lake_Toml_toml() {
_start:
{
lean_object* x_1; 
x_1 = l_Lake_Toml_toml___closed__1;
return x_1;
}
}
lean_object* initialize_Lean_Parser_Types(uint8_t builtin, lean_object*);
lean_object* initialize_Lake_Toml_ParserUtil(uint8_t builtin, lean_object*);
lean_object* initialize_Lean_Parser(uint8_t builtin, lean_object*);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lake_Toml_Grammar(uint8_t builtin, lean_object* w) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Parser_Types(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lake_Toml_ParserUtil(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser(builtin, lean_io_mk_world());
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_crlfAuxFn___closed__0);
l_Lake_Toml_newlineFn___closed__0 = _init_l_Lake_Toml_newlineFn___closed__0();
lean_mark_persistent(l_Lake_Toml_newlineFn___closed__0);
l_Lake_Toml_newlineFn___closed__1 = _init_l_Lake_Toml_newlineFn___closed__1();
lean_mark_persistent(l_Lake_Toml_newlineFn___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_commentBodyFn___closed__0);
l_Lake_Toml_commentFn___closed__0 = _init_l_Lake_Toml_commentFn___closed__0();
lean_mark_persistent(l_Lake_Toml_commentFn___closed__0);
l_Lake_Toml_commentFn___closed__1 = _init_l_Lake_Toml_commentFn___closed__1();
lean_mark_persistent(l_Lake_Toml_commentFn___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__0);
l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__1 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__1();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__2 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__2();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__2);
l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__3 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__3();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__3);
l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__4 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__4();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_escapeSeqFn___closed__4);
l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_basicStringAuxFn___closed__0);
l_Lake_Toml_basicStringFn___closed__0 = _init_l_Lake_Toml_basicStringFn___closed__0();
lean_mark_persistent(l_Lake_Toml_basicStringFn___closed__0);
l_Lake_Toml_basicStringFn___closed__1 = _init_l_Lake_Toml_basicStringFn___closed__1();
lean_mark_persistent(l_Lake_Toml_basicStringFn___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_literalStringAuxFn___closed__0);
l_Lake_Toml_literalStringFn___closed__0 = _init_l_Lake_Toml_literalStringFn___closed__0();
lean_mark_persistent(l_Lake_Toml_literalStringFn___closed__0);
l_Lake_Toml_literalStringFn___closed__1 = _init_l_Lake_Toml_literalStringFn___closed__1();
lean_mark_persistent(l_Lake_Toml_literalStringFn___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__0);
l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__1 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__1();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_mlLiteralStringAuxFn___closed__1);
l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlLiteralStringFn_spec__0___closed__0 = _init_l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlLiteralStringFn_spec__0___closed__0();
lean_mark_persistent(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlLiteralStringFn_spec__0___closed__0);
l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlLiteralStringFn_spec__0___closed__1 = _init_l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlLiteralStringFn_spec__0___closed__1();
lean_mark_persistent(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlLiteralStringFn_spec__0___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_mlBasicStringAuxFn___closed__0);
l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlBasicStringFn_spec__0___closed__0 = _init_l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlBasicStringFn_spec__0___closed__0();
lean_mark_persistent(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlBasicStringFn_spec__0___closed__0);
l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlBasicStringFn_spec__0___closed__1 = _init_l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlBasicStringFn_spec__0___closed__1();
lean_mark_persistent(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_mlBasicStringFn_spec__0___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__0);
l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__1 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__1();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__2);
l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__3);
l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__4);
l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__5);
l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__6);
l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__7);
l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__8 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__8();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__8);
l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_hourMinFn___closed__9);
l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn_timeOffsetFn___closed__0);
l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__0);
l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__1 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__1();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeTailFn___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__0);
l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__1 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__1();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_timeAuxFn___closed__1);
l_Lake_Toml_timeFn___closed__0 = _init_l_Lake_Toml_timeFn___closed__0();
lean_mark_persistent(l_Lake_Toml_timeFn___closed__0);
l_Lake_Toml_timeFn___closed__1 = _init_l_Lake_Toml_timeFn___closed__1();
lean_mark_persistent(l_Lake_Toml_timeFn___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__0);
l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__1 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__1();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__2);
l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__3);
l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__4);
l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__5);
l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__6 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__6();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__6);
l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__7 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__7();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_dateTimeAuxFn___closed__7);
l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_dateTimeFn_spec__0___closed__0 = _init_l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_dateTimeFn_spec__0___closed__0();
lean_mark_persistent(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_dateTimeFn_spec__0___closed__0);
l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_dateTimeFn_spec__0___closed__1 = _init_l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_dateTimeFn_spec__0___closed__1();
lean_mark_persistent(l___private_Lake_Toml_ParserUtil_0__Lake_Toml_repeatFn_loop___at___Lake_Toml_dateTimeFn_spec__0___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__0);
l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__1 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__1();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__2 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__2();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_decExpFn___closed__2);
l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__0);
l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__2);
l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__3);
l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__4);
l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__5);
l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__6);
l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__7 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__7();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__7);
l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__8 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__8();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberTailAuxFn___closed__8);
l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__0);
l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__1 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__1();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumberFn___closed__2);
l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__0);
l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__1 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__1();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__2 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__2();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_infAuxFn___closed__2);
l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__0);
l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__1 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__1();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__2 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__2();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_nanAuxFn___closed__2);
l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__0);
l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__2);
l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__3 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__3();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__3);
l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__4 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__4();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__4);
l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__5 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__5();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_decNumeralAuxFn___closed__5);
l_Lake_Toml_numeralFn___lam__0___closed__0 = _init_l_Lake_Toml_numeralFn___lam__0___closed__0();
lean_mark_persistent(l_Lake_Toml_numeralFn___lam__0___closed__0);
l_Lake_Toml_numeralFn___lam__0___closed__1 = _init_l_Lake_Toml_numeralFn___lam__0___closed__1();
lean_mark_persistent(l_Lake_Toml_numeralFn___lam__0___closed__1);
l_Lake_Toml_numeralFn___lam__0___closed__2 = _init_l_Lake_Toml_numeralFn___lam__0___closed__2();
lean_mark_persistent(l_Lake_Toml_numeralFn___lam__0___closed__2);
l_Lake_Toml_numeralFn___lam__0___closed__3 = _init_l_Lake_Toml_numeralFn___lam__0___closed__3();
lean_mark_persistent(l_Lake_Toml_numeralFn___lam__0___closed__3);
l_Lake_Toml_numeralFn___lam__0___closed__4 = _init_l_Lake_Toml_numeralFn___lam__0___closed__4();
lean_mark_persistent(l_Lake_Toml_numeralFn___lam__0___closed__4);
l_Lake_Toml_numeralFn___lam__0___closed__5 = _init_l_Lake_Toml_numeralFn___lam__0___closed__5();
lean_mark_persistent(l_Lake_Toml_numeralFn___lam__0___closed__5);
l_Lake_Toml_numeralFn___lam__0___closed__6 = _init_l_Lake_Toml_numeralFn___lam__0___closed__6();
lean_mark_persistent(l_Lake_Toml_numeralFn___lam__0___closed__6);
l_Lake_Toml_numeralFn___lam__0___closed__7 = _init_l_Lake_Toml_numeralFn___lam__0___closed__7();
lean_mark_persistent(l_Lake_Toml_numeralFn___lam__0___closed__7);
l_Lake_Toml_numeralFn___lam__0___closed__8 = _init_l_Lake_Toml_numeralFn___lam__0___closed__8();
lean_mark_persistent(l_Lake_Toml_numeralFn___lam__0___closed__8);
l_Lake_Toml_numeralFn___lam__0___closed__9 = _init_l_Lake_Toml_numeralFn___lam__0___closed__9();
lean_mark_persistent(l_Lake_Toml_numeralFn___lam__0___closed__9);
l_Lake_Toml_numeralFn___lam__0___closed__10 = _init_l_Lake_Toml_numeralFn___lam__0___closed__10();
lean_mark_persistent(l_Lake_Toml_numeralFn___lam__0___closed__10);
l_Lake_Toml_numeralFn___lam__0___closed__11 = _init_l_Lake_Toml_numeralFn___lam__0___closed__11();
lean_mark_persistent(l_Lake_Toml_numeralFn___lam__0___closed__11);
l_Lake_Toml_numeralFn___lam__0___closed__12 = _init_l_Lake_Toml_numeralFn___lam__0___closed__12();
lean_mark_persistent(l_Lake_Toml_numeralFn___lam__0___closed__12);
l_Lake_Toml_numeralFn___lam__0___closed__13 = _init_l_Lake_Toml_numeralFn___lam__0___closed__13();
lean_mark_persistent(l_Lake_Toml_numeralFn___lam__0___closed__13);
l_Lake_Toml_numeralFn___lam__0___closed__14 = _init_l_Lake_Toml_numeralFn___lam__0___closed__14();
lean_mark_persistent(l_Lake_Toml_numeralFn___lam__0___closed__14);
l_Lake_Toml_numeralFn___lam__0___closed__15 = _init_l_Lake_Toml_numeralFn___lam__0___closed__15();
lean_mark_persistent(l_Lake_Toml_numeralFn___lam__0___closed__15);
l_Lake_Toml_numeralFn___lam__0___closed__16 = _init_l_Lake_Toml_numeralFn___lam__0___closed__16();
lean_mark_persistent(l_Lake_Toml_numeralFn___lam__0___closed__16);
l_Lake_Toml_numeralFn___lam__0___closed__17 = _init_l_Lake_Toml_numeralFn___lam__0___closed__17();
lean_mark_persistent(l_Lake_Toml_numeralFn___lam__0___closed__17);
l_Lake_Toml_trailingWs___closed__0 = _init_l_Lake_Toml_trailingWs___closed__0();
lean_mark_persistent(l_Lake_Toml_trailingWs___closed__0);
l_Lake_Toml_trailingWs = _init_l_Lake_Toml_trailingWs();
lean_mark_persistent(l_Lake_Toml_trailingWs);
l_Lake_Toml_trailingSep___closed__0 = _init_l_Lake_Toml_trailingSep___closed__0();
lean_mark_persistent(l_Lake_Toml_trailingSep___closed__0);
l_Lake_Toml_trailingSep___closed__1 = _init_l_Lake_Toml_trailingSep___closed__1();
lean_mark_persistent(l_Lake_Toml_trailingSep___closed__1);
l_Lake_Toml_trailingSep = _init_l_Lake_Toml_trailingSep();
lean_mark_persistent(l_Lake_Toml_trailingSep);
l_Lake_Toml_unquotedKeyFn___closed__0 = _init_l_Lake_Toml_unquotedKeyFn___closed__0();
lean_mark_persistent(l_Lake_Toml_unquotedKeyFn___closed__0);
l_Lake_Toml_unquotedKeyFn___closed__1 = _init_l_Lake_Toml_unquotedKeyFn___closed__1();
lean_mark_persistent(l_Lake_Toml_unquotedKeyFn___closed__1);
l_Lake_Toml_unquotedKey___closed__0 = _init_l_Lake_Toml_unquotedKey___closed__0();
lean_mark_persistent(l_Lake_Toml_unquotedKey___closed__0);
l_Lake_Toml_unquotedKey___closed__1 = _init_l_Lake_Toml_unquotedKey___closed__1();
lean_mark_persistent(l_Lake_Toml_unquotedKey___closed__1);
l_Lake_Toml_unquotedKey___closed__2 = _init_l_Lake_Toml_unquotedKey___closed__2();
lean_mark_persistent(l_Lake_Toml_unquotedKey___closed__2);
l_Lake_Toml_unquotedKey = _init_l_Lake_Toml_unquotedKey();
lean_mark_persistent(l_Lake_Toml_unquotedKey);
l_Lake_Toml_basicString___closed__0 = _init_l_Lake_Toml_basicString___closed__0();
lean_mark_persistent(l_Lake_Toml_basicString___closed__0);
l_Lake_Toml_basicString___closed__1 = _init_l_Lake_Toml_basicString___closed__1();
lean_mark_persistent(l_Lake_Toml_basicString___closed__1);
l_Lake_Toml_basicString___closed__2 = _init_l_Lake_Toml_basicString___closed__2();
lean_mark_persistent(l_Lake_Toml_basicString___closed__2);
l_Lake_Toml_basicString = _init_l_Lake_Toml_basicString();
lean_mark_persistent(l_Lake_Toml_basicString);
l_Lake_Toml_literalString___closed__0 = _init_l_Lake_Toml_literalString___closed__0();
lean_mark_persistent(l_Lake_Toml_literalString___closed__0);
l_Lake_Toml_literalString___closed__1 = _init_l_Lake_Toml_literalString___closed__1();
lean_mark_persistent(l_Lake_Toml_literalString___closed__1);
l_Lake_Toml_literalString___closed__2 = _init_l_Lake_Toml_literalString___closed__2();
lean_mark_persistent(l_Lake_Toml_literalString___closed__2);
l_Lake_Toml_literalString = _init_l_Lake_Toml_literalString();
lean_mark_persistent(l_Lake_Toml_literalString);
l_Lake_Toml_mlBasicString___closed__0 = _init_l_Lake_Toml_mlBasicString___closed__0();
lean_mark_persistent(l_Lake_Toml_mlBasicString___closed__0);
l_Lake_Toml_mlBasicString___closed__1 = _init_l_Lake_Toml_mlBasicString___closed__1();
lean_mark_persistent(l_Lake_Toml_mlBasicString___closed__1);
l_Lake_Toml_mlBasicString___closed__2 = _init_l_Lake_Toml_mlBasicString___closed__2();
lean_mark_persistent(l_Lake_Toml_mlBasicString___closed__2);
l_Lake_Toml_mlBasicString = _init_l_Lake_Toml_mlBasicString();
lean_mark_persistent(l_Lake_Toml_mlBasicString);
l_Lake_Toml_mlLiteralString___closed__0 = _init_l_Lake_Toml_mlLiteralString___closed__0();
lean_mark_persistent(l_Lake_Toml_mlLiteralString___closed__0);
l_Lake_Toml_mlLiteralString___closed__1 = _init_l_Lake_Toml_mlLiteralString___closed__1();
lean_mark_persistent(l_Lake_Toml_mlLiteralString___closed__1);
l_Lake_Toml_mlLiteralString___closed__2 = _init_l_Lake_Toml_mlLiteralString___closed__2();
lean_mark_persistent(l_Lake_Toml_mlLiteralString___closed__2);
l_Lake_Toml_mlLiteralString = _init_l_Lake_Toml_mlLiteralString();
lean_mark_persistent(l_Lake_Toml_mlLiteralString);
l_Lake_Toml_quotedKey___closed__0 = _init_l_Lake_Toml_quotedKey___closed__0();
lean_mark_persistent(l_Lake_Toml_quotedKey___closed__0);
l_Lake_Toml_quotedKey = _init_l_Lake_Toml_quotedKey();
lean_mark_persistent(l_Lake_Toml_quotedKey);
l_Lake_Toml_simpleKey___closed__0 = _init_l_Lake_Toml_simpleKey___closed__0();
lean_mark_persistent(l_Lake_Toml_simpleKey___closed__0);
l_Lake_Toml_simpleKey___closed__1 = _init_l_Lake_Toml_simpleKey___closed__1();
lean_mark_persistent(l_Lake_Toml_simpleKey___closed__1);
l_Lake_Toml_simpleKey___closed__2 = _init_l_Lake_Toml_simpleKey___closed__2();
lean_mark_persistent(l_Lake_Toml_simpleKey___closed__2);
l_Lake_Toml_simpleKey___closed__3 = _init_l_Lake_Toml_simpleKey___closed__3();
lean_mark_persistent(l_Lake_Toml_simpleKey___closed__3);
l_Lake_Toml_simpleKey = _init_l_Lake_Toml_simpleKey();
lean_mark_persistent(l_Lake_Toml_simpleKey);
l_Lake_Toml_key___closed__0 = _init_l_Lake_Toml_key___closed__0();
lean_mark_persistent(l_Lake_Toml_key___closed__0);
l_Lake_Toml_key___closed__1 = _init_l_Lake_Toml_key___closed__1();
lean_mark_persistent(l_Lake_Toml_key___closed__1);
l_Lake_Toml_key___closed__2 = _init_l_Lake_Toml_key___closed__2();
lean_mark_persistent(l_Lake_Toml_key___closed__2);
l_Lake_Toml_key___closed__3 = _init_l_Lake_Toml_key___closed__3();
lean_mark_persistent(l_Lake_Toml_key___closed__3);
l_Lake_Toml_key___closed__4 = _init_l_Lake_Toml_key___closed__4();
lean_mark_persistent(l_Lake_Toml_key___closed__4);
l_Lake_Toml_key___closed__5 = _init_l_Lake_Toml_key___closed__5();
lean_mark_persistent(l_Lake_Toml_key___closed__5);
l_Lake_Toml_key___closed__6 = _init_l_Lake_Toml_key___closed__6();
lean_mark_persistent(l_Lake_Toml_key___closed__6);
l_Lake_Toml_key___closed__7 = _init_l_Lake_Toml_key___closed__7();
lean_mark_persistent(l_Lake_Toml_key___closed__7);
l_Lake_Toml_key___closed__8 = _init_l_Lake_Toml_key___closed__8();
lean_mark_persistent(l_Lake_Toml_key___closed__8);
l_Lake_Toml_key___closed__9 = _init_l_Lake_Toml_key___closed__9();
lean_mark_persistent(l_Lake_Toml_key___closed__9);
l_Lake_Toml_key___closed__10 = _init_l_Lake_Toml_key___closed__10();
lean_mark_persistent(l_Lake_Toml_key___closed__10);
l_Lake_Toml_key___closed__11 = _init_l_Lake_Toml_key___closed__11();
lean_mark_persistent(l_Lake_Toml_key___closed__11);
l_Lake_Toml_key___closed__12 = _init_l_Lake_Toml_key___closed__12();
lean_mark_persistent(l_Lake_Toml_key___closed__12);
l_Lake_Toml_key___closed__13 = _init_l_Lake_Toml_key___closed__13();
lean_mark_persistent(l_Lake_Toml_key___closed__13);
l_Lake_Toml_key = _init_l_Lake_Toml_key();
lean_mark_persistent(l_Lake_Toml_key);
l_Lake_Toml_stdTable___closed__0 = _init_l_Lake_Toml_stdTable___closed__0();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__0);
l_Lake_Toml_stdTable___closed__1 = _init_l_Lake_Toml_stdTable___closed__1();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__1);
l_Lake_Toml_stdTable___closed__2 = _init_l_Lake_Toml_stdTable___closed__2();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__2);
l_Lake_Toml_stdTable___closed__3 = _init_l_Lake_Toml_stdTable___closed__3();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__3);
l_Lake_Toml_stdTable___closed__4 = _init_l_Lake_Toml_stdTable___closed__4();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__4);
l_Lake_Toml_stdTable___closed__5 = _init_l_Lake_Toml_stdTable___closed__5();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__5);
l_Lake_Toml_stdTable___closed__6 = _init_l_Lake_Toml_stdTable___closed__6();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__6);
l_Lake_Toml_stdTable___closed__7 = _init_l_Lake_Toml_stdTable___closed__7();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__7);
l_Lake_Toml_stdTable___closed__8 = _init_l_Lake_Toml_stdTable___closed__8();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__8);
l_Lake_Toml_stdTable___closed__9 = _init_l_Lake_Toml_stdTable___closed__9();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__9);
l_Lake_Toml_stdTable___closed__10 = _init_l_Lake_Toml_stdTable___closed__10();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__10);
l_Lake_Toml_stdTable___closed__11 = _init_l_Lake_Toml_stdTable___closed__11();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__11);
l_Lake_Toml_stdTable___closed__12 = _init_l_Lake_Toml_stdTable___closed__12();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__12);
l_Lake_Toml_stdTable___closed__13 = _init_l_Lake_Toml_stdTable___closed__13();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__13);
l_Lake_Toml_stdTable___closed__14 = _init_l_Lake_Toml_stdTable___closed__14();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__14);
l_Lake_Toml_stdTable___closed__15 = _init_l_Lake_Toml_stdTable___closed__15();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__15);
l_Lake_Toml_stdTable___closed__16 = _init_l_Lake_Toml_stdTable___closed__16();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__16);
l_Lake_Toml_stdTable___closed__17 = _init_l_Lake_Toml_stdTable___closed__17();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__17);
l_Lake_Toml_stdTable___closed__18 = _init_l_Lake_Toml_stdTable___closed__18();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__18);
l_Lake_Toml_stdTable___closed__19 = _init_l_Lake_Toml_stdTable___closed__19();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__19);
l_Lake_Toml_stdTable___closed__20 = _init_l_Lake_Toml_stdTable___closed__20();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__20);
l_Lake_Toml_stdTable___closed__21 = _init_l_Lake_Toml_stdTable___closed__21();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__21);
l_Lake_Toml_stdTable___closed__22 = _init_l_Lake_Toml_stdTable___closed__22();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__22);
l_Lake_Toml_stdTable___closed__23 = _init_l_Lake_Toml_stdTable___closed__23();
lean_mark_persistent(l_Lake_Toml_stdTable___closed__23);
l_Lake_Toml_stdTable = _init_l_Lake_Toml_stdTable();
lean_mark_persistent(l_Lake_Toml_stdTable);
l_Lake_Toml_arrayTable___closed__0 = _init_l_Lake_Toml_arrayTable___closed__0();
lean_mark_persistent(l_Lake_Toml_arrayTable___closed__0);
l_Lake_Toml_arrayTable___closed__1 = _init_l_Lake_Toml_arrayTable___closed__1();
lean_mark_persistent(l_Lake_Toml_arrayTable___closed__1);
l_Lake_Toml_arrayTable___closed__2 = _init_l_Lake_Toml_arrayTable___closed__2();
lean_mark_persistent(l_Lake_Toml_arrayTable___closed__2);
l_Lake_Toml_arrayTable___closed__3 = _init_l_Lake_Toml_arrayTable___closed__3();
lean_mark_persistent(l_Lake_Toml_arrayTable___closed__3);
l_Lake_Toml_arrayTable___closed__4 = _init_l_Lake_Toml_arrayTable___closed__4();
lean_mark_persistent(l_Lake_Toml_arrayTable___closed__4);
l_Lake_Toml_arrayTable___closed__5 = _init_l_Lake_Toml_arrayTable___closed__5();
lean_mark_persistent(l_Lake_Toml_arrayTable___closed__5);
l_Lake_Toml_arrayTable___closed__6 = _init_l_Lake_Toml_arrayTable___closed__6();
lean_mark_persistent(l_Lake_Toml_arrayTable___closed__6);
l_Lake_Toml_arrayTable___closed__7 = _init_l_Lake_Toml_arrayTable___closed__7();
lean_mark_persistent(l_Lake_Toml_arrayTable___closed__7);
l_Lake_Toml_arrayTable___closed__8 = _init_l_Lake_Toml_arrayTable___closed__8();
lean_mark_persistent(l_Lake_Toml_arrayTable___closed__8);
l_Lake_Toml_arrayTable___closed__9 = _init_l_Lake_Toml_arrayTable___closed__9();
lean_mark_persistent(l_Lake_Toml_arrayTable___closed__9);
l_Lake_Toml_arrayTable = _init_l_Lake_Toml_arrayTable();
lean_mark_persistent(l_Lake_Toml_arrayTable);
l_Lake_Toml_table___closed__0 = _init_l_Lake_Toml_table___closed__0();
lean_mark_persistent(l_Lake_Toml_table___closed__0);
l_Lake_Toml_table = _init_l_Lake_Toml_table();
lean_mark_persistent(l_Lake_Toml_table);
l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__0);
l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__2);
l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__3);
l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__4);
l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__5);
l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore___closed__6);
l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__0);
l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore___closed__2);
l_Lake_Toml_header___closed__0 = _init_l_Lake_Toml_header___closed__0();
lean_mark_persistent(l_Lake_Toml_header___closed__0);
l_Lake_Toml_header___closed__1 = _init_l_Lake_Toml_header___closed__1();
lean_mark_persistent(l_Lake_Toml_header___closed__1);
l_Lake_Toml_header___closed__2 = _init_l_Lake_Toml_header___closed__2();
lean_mark_persistent(l_Lake_Toml_header___closed__2);
l_Lake_Toml_header = _init_l_Lake_Toml_header();
lean_mark_persistent(l_Lake_Toml_header);
l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__0);
l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__2 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__2();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__2);
l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__3 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__3();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__3);
l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__4 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__4();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__4);
l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__5);
l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__6 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__6();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__6);
l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__7);
l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__8);
l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__9 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__9();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_tomlCore___closed__9);
l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__0);
l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__2 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__2();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__2);
l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__3 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__3();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__3);
l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__4);
l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__5);
l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__6);
l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__7);
l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__8);
l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__9);
l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__10);
l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__11);
l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__12);
l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__13);
l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__14);
l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_inlineTableCore___closed__15);
l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__0);
l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__2 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__2();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__2);
l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__3);
l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_arrayCore___closed__4);
l_Lake_Toml_string___closed__0 = _init_l_Lake_Toml_string___closed__0();
lean_mark_persistent(l_Lake_Toml_string___closed__0);
l_Lake_Toml_string___closed__1 = _init_l_Lake_Toml_string___closed__1();
lean_mark_persistent(l_Lake_Toml_string___closed__1);
l_Lake_Toml_string___closed__2 = _init_l_Lake_Toml_string___closed__2();
lean_mark_persistent(l_Lake_Toml_string___closed__2);
l_Lake_Toml_string___closed__3 = _init_l_Lake_Toml_string___closed__3();
lean_mark_persistent(l_Lake_Toml_string___closed__3);
l_Lake_Toml_string___closed__4 = _init_l_Lake_Toml_string___closed__4();
lean_mark_persistent(l_Lake_Toml_string___closed__4);
l_Lake_Toml_string___closed__5 = _init_l_Lake_Toml_string___closed__5();
lean_mark_persistent(l_Lake_Toml_string___closed__5);
l_Lake_Toml_string___closed__6 = _init_l_Lake_Toml_string___closed__6();
lean_mark_persistent(l_Lake_Toml_string___closed__6);
l_Lake_Toml_string___closed__7 = _init_l_Lake_Toml_string___closed__7();
lean_mark_persistent(l_Lake_Toml_string___closed__7);
l_Lake_Toml_string = _init_l_Lake_Toml_string();
lean_mark_persistent(l_Lake_Toml_string);
l_Lake_Toml_true___closed__0 = _init_l_Lake_Toml_true___closed__0();
lean_mark_persistent(l_Lake_Toml_true___closed__0);
l_Lake_Toml_true___closed__1 = _init_l_Lake_Toml_true___closed__1();
lean_mark_persistent(l_Lake_Toml_true___closed__1);
l_Lake_Toml_true___closed__2 = _init_l_Lake_Toml_true___closed__2();
lean_mark_persistent(l_Lake_Toml_true___closed__2);
l_Lake_Toml_true___closed__3 = _init_l_Lake_Toml_true___closed__3();
lean_mark_persistent(l_Lake_Toml_true___closed__3);
l_Lake_Toml_true___closed__4 = _init_l_Lake_Toml_true___closed__4();
lean_mark_persistent(l_Lake_Toml_true___closed__4);
l_Lake_Toml_true___closed__5 = _init_l_Lake_Toml_true___closed__5();
lean_mark_persistent(l_Lake_Toml_true___closed__5);
l_Lake_Toml_true = _init_l_Lake_Toml_true();
lean_mark_persistent(l_Lake_Toml_true);
l_Lake_Toml_false___closed__0 = _init_l_Lake_Toml_false___closed__0();
lean_mark_persistent(l_Lake_Toml_false___closed__0);
l_Lake_Toml_false___closed__1 = _init_l_Lake_Toml_false___closed__1();
lean_mark_persistent(l_Lake_Toml_false___closed__1);
l_Lake_Toml_false___closed__2 = _init_l_Lake_Toml_false___closed__2();
lean_mark_persistent(l_Lake_Toml_false___closed__2);
l_Lake_Toml_false___closed__3 = _init_l_Lake_Toml_false___closed__3();
lean_mark_persistent(l_Lake_Toml_false___closed__3);
l_Lake_Toml_false___closed__4 = _init_l_Lake_Toml_false___closed__4();
lean_mark_persistent(l_Lake_Toml_false___closed__4);
l_Lake_Toml_false___closed__5 = _init_l_Lake_Toml_false___closed__5();
lean_mark_persistent(l_Lake_Toml_false___closed__5);
l_Lake_Toml_false = _init_l_Lake_Toml_false();
lean_mark_persistent(l_Lake_Toml_false);
l_Lake_Toml_boolean___closed__0 = _init_l_Lake_Toml_boolean___closed__0();
lean_mark_persistent(l_Lake_Toml_boolean___closed__0);
l_Lake_Toml_boolean___closed__1 = _init_l_Lake_Toml_boolean___closed__1();
lean_mark_persistent(l_Lake_Toml_boolean___closed__1);
l_Lake_Toml_boolean___closed__2 = _init_l_Lake_Toml_boolean___closed__2();
lean_mark_persistent(l_Lake_Toml_boolean___closed__2);
l_Lake_Toml_boolean___closed__3 = _init_l_Lake_Toml_boolean___closed__3();
lean_mark_persistent(l_Lake_Toml_boolean___closed__3);
l_Lake_Toml_boolean = _init_l_Lake_Toml_boolean();
lean_mark_persistent(l_Lake_Toml_boolean);
l_Lake_Toml_numeralAntiquot___closed__0 = _init_l_Lake_Toml_numeralAntiquot___closed__0();
lean_mark_persistent(l_Lake_Toml_numeralAntiquot___closed__0);
l_Lake_Toml_numeralAntiquot___closed__1 = _init_l_Lake_Toml_numeralAntiquot___closed__1();
lean_mark_persistent(l_Lake_Toml_numeralAntiquot___closed__1);
l_Lake_Toml_numeralAntiquot___closed__2 = _init_l_Lake_Toml_numeralAntiquot___closed__2();
lean_mark_persistent(l_Lake_Toml_numeralAntiquot___closed__2);
l_Lake_Toml_numeralAntiquot___closed__3 = _init_l_Lake_Toml_numeralAntiquot___closed__3();
lean_mark_persistent(l_Lake_Toml_numeralAntiquot___closed__3);
l_Lake_Toml_numeralAntiquot___closed__4 = _init_l_Lake_Toml_numeralAntiquot___closed__4();
lean_mark_persistent(l_Lake_Toml_numeralAntiquot___closed__4);
l_Lake_Toml_numeralAntiquot___closed__5 = _init_l_Lake_Toml_numeralAntiquot___closed__5();
lean_mark_persistent(l_Lake_Toml_numeralAntiquot___closed__5);
l_Lake_Toml_numeralAntiquot___closed__6 = _init_l_Lake_Toml_numeralAntiquot___closed__6();
lean_mark_persistent(l_Lake_Toml_numeralAntiquot___closed__6);
l_Lake_Toml_numeralAntiquot___closed__7 = _init_l_Lake_Toml_numeralAntiquot___closed__7();
lean_mark_persistent(l_Lake_Toml_numeralAntiquot___closed__7);
l_Lake_Toml_numeralAntiquot___closed__8 = _init_l_Lake_Toml_numeralAntiquot___closed__8();
lean_mark_persistent(l_Lake_Toml_numeralAntiquot___closed__8);
l_Lake_Toml_numeralAntiquot___closed__9 = _init_l_Lake_Toml_numeralAntiquot___closed__9();
lean_mark_persistent(l_Lake_Toml_numeralAntiquot___closed__9);
l_Lake_Toml_numeralAntiquot___closed__10 = _init_l_Lake_Toml_numeralAntiquot___closed__10();
lean_mark_persistent(l_Lake_Toml_numeralAntiquot___closed__10);
l_Lake_Toml_numeralAntiquot___closed__11 = _init_l_Lake_Toml_numeralAntiquot___closed__11();
lean_mark_persistent(l_Lake_Toml_numeralAntiquot___closed__11);
l_Lake_Toml_numeralAntiquot___closed__12 = _init_l_Lake_Toml_numeralAntiquot___closed__12();
lean_mark_persistent(l_Lake_Toml_numeralAntiquot___closed__12);
l_Lake_Toml_numeralAntiquot___closed__13 = _init_l_Lake_Toml_numeralAntiquot___closed__13();
lean_mark_persistent(l_Lake_Toml_numeralAntiquot___closed__13);
l_Lake_Toml_numeralAntiquot___closed__14 = _init_l_Lake_Toml_numeralAntiquot___closed__14();
lean_mark_persistent(l_Lake_Toml_numeralAntiquot___closed__14);
l_Lake_Toml_numeralAntiquot = _init_l_Lake_Toml_numeralAntiquot();
lean_mark_persistent(l_Lake_Toml_numeralAntiquot);
l_Lake_Toml_numeral___closed__0 = _init_l_Lake_Toml_numeral___closed__0();
lean_mark_persistent(l_Lake_Toml_numeral___closed__0);
l_Lake_Toml_numeral___closed__1 = _init_l_Lake_Toml_numeral___closed__1();
lean_mark_persistent(l_Lake_Toml_numeral___closed__1);
l_Lake_Toml_numeral = _init_l_Lake_Toml_numeral();
lean_mark_persistent(l_Lake_Toml_numeral);
l_Lake_Toml_numeralOfKind___closed__0 = _init_l_Lake_Toml_numeralOfKind___closed__0();
lean_mark_persistent(l_Lake_Toml_numeralOfKind___closed__0);
l_Lake_Toml_float___closed__0 = _init_l_Lake_Toml_float___closed__0();
lean_mark_persistent(l_Lake_Toml_float___closed__0);
l_Lake_Toml_float = _init_l_Lake_Toml_float();
lean_mark_persistent(l_Lake_Toml_float);
l_Lake_Toml_decInt___closed__0 = _init_l_Lake_Toml_decInt___closed__0();
lean_mark_persistent(l_Lake_Toml_decInt___closed__0);
l_Lake_Toml_decInt = _init_l_Lake_Toml_decInt();
lean_mark_persistent(l_Lake_Toml_decInt);
l_Lake_Toml_binNum___closed__0 = _init_l_Lake_Toml_binNum___closed__0();
lean_mark_persistent(l_Lake_Toml_binNum___closed__0);
l_Lake_Toml_binNum___closed__1 = _init_l_Lake_Toml_binNum___closed__1();
lean_mark_persistent(l_Lake_Toml_binNum___closed__1);
l_Lake_Toml_binNum = _init_l_Lake_Toml_binNum();
lean_mark_persistent(l_Lake_Toml_binNum);
l_Lake_Toml_octNum___closed__0 = _init_l_Lake_Toml_octNum___closed__0();
lean_mark_persistent(l_Lake_Toml_octNum___closed__0);
l_Lake_Toml_octNum___closed__1 = _init_l_Lake_Toml_octNum___closed__1();
lean_mark_persistent(l_Lake_Toml_octNum___closed__1);
l_Lake_Toml_octNum = _init_l_Lake_Toml_octNum();
lean_mark_persistent(l_Lake_Toml_octNum);
l_Lake_Toml_hexNum___closed__0 = _init_l_Lake_Toml_hexNum___closed__0();
lean_mark_persistent(l_Lake_Toml_hexNum___closed__0);
l_Lake_Toml_hexNum___closed__1 = _init_l_Lake_Toml_hexNum___closed__1();
lean_mark_persistent(l_Lake_Toml_hexNum___closed__1);
l_Lake_Toml_hexNum = _init_l_Lake_Toml_hexNum();
lean_mark_persistent(l_Lake_Toml_hexNum);
l_Lake_Toml_dateTime___closed__0 = _init_l_Lake_Toml_dateTime___closed__0();
lean_mark_persistent(l_Lake_Toml_dateTime___closed__0);
l_Lake_Toml_dateTime = _init_l_Lake_Toml_dateTime();
lean_mark_persistent(l_Lake_Toml_dateTime);
l_Lake_Toml_val___closed__0 = _init_l_Lake_Toml_val___closed__0();
lean_mark_persistent(l_Lake_Toml_val___closed__0);
l_Lake_Toml_val___closed__1 = _init_l_Lake_Toml_val___closed__1();
lean_mark_persistent(l_Lake_Toml_val___closed__1);
l_Lake_Toml_val___closed__2 = _init_l_Lake_Toml_val___closed__2();
lean_mark_persistent(l_Lake_Toml_val___closed__2);
l_Lake_Toml_val___closed__3 = _init_l_Lake_Toml_val___closed__3();
lean_mark_persistent(l_Lake_Toml_val___closed__3);
l_Lake_Toml_val = _init_l_Lake_Toml_val();
lean_mark_persistent(l_Lake_Toml_val);
l_Lake_Toml_array___closed__0 = _init_l_Lake_Toml_array___closed__0();
lean_mark_persistent(l_Lake_Toml_array___closed__0);
l_Lake_Toml_array = _init_l_Lake_Toml_array();
lean_mark_persistent(l_Lake_Toml_array);
l_Lake_Toml_inlineTable___closed__0 = _init_l_Lake_Toml_inlineTable___closed__0();
lean_mark_persistent(l_Lake_Toml_inlineTable___closed__0);
l_Lake_Toml_inlineTable = _init_l_Lake_Toml_inlineTable();
lean_mark_persistent(l_Lake_Toml_inlineTable);
l_Lake_Toml_keyval___closed__0 = _init_l_Lake_Toml_keyval___closed__0();
lean_mark_persistent(l_Lake_Toml_keyval___closed__0);
l_Lake_Toml_keyval = _init_l_Lake_Toml_keyval();
lean_mark_persistent(l_Lake_Toml_keyval);
l_Lake_Toml_expression___closed__0 = _init_l_Lake_Toml_expression___closed__0();
lean_mark_persistent(l_Lake_Toml_expression___closed__0);
l_Lake_Toml_expression = _init_l_Lake_Toml_expression();
lean_mark_persistent(l_Lake_Toml_expression);
l_Lake_Toml_simpleKey_formatter___closed__0 = _init_l_Lake_Toml_simpleKey_formatter___closed__0();
lean_mark_persistent(l_Lake_Toml_simpleKey_formatter___closed__0);
l_Lake_Toml_key_formatter___closed__0___boxed__const__1 = _init_l_Lake_Toml_key_formatter___closed__0___boxed__const__1();
lean_mark_persistent(l_Lake_Toml_key_formatter___closed__0___boxed__const__1);
l_Lake_Toml_key_formatter___closed__0 = _init_l_Lake_Toml_key_formatter___closed__0();
lean_mark_persistent(l_Lake_Toml_key_formatter___closed__0);
l_Lake_Toml_key_formatter___closed__1 = _init_l_Lake_Toml_key_formatter___closed__1();
lean_mark_persistent(l_Lake_Toml_key_formatter___closed__1);
l_Lake_Toml_key_formatter___closed__2 = _init_l_Lake_Toml_key_formatter___closed__2();
lean_mark_persistent(l_Lake_Toml_key_formatter___closed__2);
l_Lake_Toml_key_formatter___closed__3 = _init_l_Lake_Toml_key_formatter___closed__3();
lean_mark_persistent(l_Lake_Toml_key_formatter___closed__3);
l_Lake_Toml_key_formatter___closed__4 = _init_l_Lake_Toml_key_formatter___closed__4();
lean_mark_persistent(l_Lake_Toml_key_formatter___closed__4);
l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0___boxed__const__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_formatter___closed__0);
l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1 = _init_l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1();
lean_mark_persistent(l_Lake_Toml_stdTable_formatter___closed__0___boxed__const__1);
l_Lake_Toml_stdTable_formatter___closed__0 = _init_l_Lake_Toml_stdTable_formatter___closed__0();
lean_mark_persistent(l_Lake_Toml_stdTable_formatter___closed__0);
l_Lake_Toml_stdTable_formatter___closed__1___boxed__const__1 = _init_l_Lake_Toml_stdTable_formatter___closed__1___boxed__const__1();
lean_mark_persistent(l_Lake_Toml_stdTable_formatter___closed__1___boxed__const__1);
l_Lake_Toml_stdTable_formatter___closed__1 = _init_l_Lake_Toml_stdTable_formatter___closed__1();
lean_mark_persistent(l_Lake_Toml_stdTable_formatter___closed__1);
l_Lake_Toml_stdTable_formatter___closed__2 = _init_l_Lake_Toml_stdTable_formatter___closed__2();
lean_mark_persistent(l_Lake_Toml_stdTable_formatter___closed__2);
l_Lake_Toml_stdTable_formatter___closed__3 = _init_l_Lake_Toml_stdTable_formatter___closed__3();
lean_mark_persistent(l_Lake_Toml_stdTable_formatter___closed__3);
l_Lake_Toml_stdTable_formatter___closed__4 = _init_l_Lake_Toml_stdTable_formatter___closed__4();
lean_mark_persistent(l_Lake_Toml_stdTable_formatter___closed__4);
l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1 = _init_l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1();
lean_mark_persistent(l_Lake_Toml_stdTable_formatter___closed__5___boxed__const__1);
l_Lake_Toml_stdTable_formatter___closed__5 = _init_l_Lake_Toml_stdTable_formatter___closed__5();
lean_mark_persistent(l_Lake_Toml_stdTable_formatter___closed__5);
l_Lake_Toml_stdTable_formatter___closed__6 = _init_l_Lake_Toml_stdTable_formatter___closed__6();
lean_mark_persistent(l_Lake_Toml_stdTable_formatter___closed__6);
l_Lake_Toml_stdTable_formatter___closed__7 = _init_l_Lake_Toml_stdTable_formatter___closed__7();
lean_mark_persistent(l_Lake_Toml_stdTable_formatter___closed__7);
l_Lake_Toml_stdTable_formatter___closed__8 = _init_l_Lake_Toml_stdTable_formatter___closed__8();
lean_mark_persistent(l_Lake_Toml_stdTable_formatter___closed__8);
l_Lake_Toml_stdTable_formatter___closed__9 = _init_l_Lake_Toml_stdTable_formatter___closed__9();
lean_mark_persistent(l_Lake_Toml_stdTable_formatter___closed__9);
l_Lake_Toml_arrayTable_formatter___closed__0 = _init_l_Lake_Toml_arrayTable_formatter___closed__0();
lean_mark_persistent(l_Lake_Toml_arrayTable_formatter___closed__0);
l_Lake_Toml_arrayTable_formatter___closed__1 = _init_l_Lake_Toml_arrayTable_formatter___closed__1();
lean_mark_persistent(l_Lake_Toml_arrayTable_formatter___closed__1);
l_Lake_Toml_arrayTable_formatter___closed__2 = _init_l_Lake_Toml_arrayTable_formatter___closed__2();
lean_mark_persistent(l_Lake_Toml_arrayTable_formatter___closed__2);
l_Lake_Toml_arrayTable_formatter___closed__3 = _init_l_Lake_Toml_arrayTable_formatter___closed__3();
lean_mark_persistent(l_Lake_Toml_arrayTable_formatter___closed__3);
l_Lake_Toml_arrayTable_formatter___closed__4 = _init_l_Lake_Toml_arrayTable_formatter___closed__4();
lean_mark_persistent(l_Lake_Toml_arrayTable_formatter___closed__4);
l_Lake_Toml_arrayTable_formatter___closed__5 = _init_l_Lake_Toml_arrayTable_formatter___closed__5();
lean_mark_persistent(l_Lake_Toml_arrayTable_formatter___closed__5);
l_Lake_Toml_arrayTable_formatter___closed__6 = _init_l_Lake_Toml_arrayTable_formatter___closed__6();
lean_mark_persistent(l_Lake_Toml_arrayTable_formatter___closed__6);
l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_formatter___closed__0);
l_Lake_Toml_simpleKey_parenthesizer___closed__0 = _init_l_Lake_Toml_simpleKey_parenthesizer___closed__0();
lean_mark_persistent(l_Lake_Toml_simpleKey_parenthesizer___closed__0);
l_Lake_Toml_key_parenthesizer___closed__0___boxed__const__1 = _init_l_Lake_Toml_key_parenthesizer___closed__0___boxed__const__1();
lean_mark_persistent(l_Lake_Toml_key_parenthesizer___closed__0___boxed__const__1);
l_Lake_Toml_key_parenthesizer___closed__0 = _init_l_Lake_Toml_key_parenthesizer___closed__0();
lean_mark_persistent(l_Lake_Toml_key_parenthesizer___closed__0);
l_Lake_Toml_key_parenthesizer___closed__1 = _init_l_Lake_Toml_key_parenthesizer___closed__1();
lean_mark_persistent(l_Lake_Toml_key_parenthesizer___closed__1);
l_Lake_Toml_key_parenthesizer___closed__2 = _init_l_Lake_Toml_key_parenthesizer___closed__2();
lean_mark_persistent(l_Lake_Toml_key_parenthesizer___closed__2);
l_Lake_Toml_key_parenthesizer___closed__3 = _init_l_Lake_Toml_key_parenthesizer___closed__3();
lean_mark_persistent(l_Lake_Toml_key_parenthesizer___closed__3);
l_Lake_Toml_key_parenthesizer___closed__4 = _init_l_Lake_Toml_key_parenthesizer___closed__4();
lean_mark_persistent(l_Lake_Toml_key_parenthesizer___closed__4);
l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0___boxed__const__1 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0___boxed__const__1();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0___boxed__const__1);
l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_keyvalCore_parenthesizer___closed__0);
l_Lake_Toml_stdTable_parenthesizer___closed__0___boxed__const__1 = _init_l_Lake_Toml_stdTable_parenthesizer___closed__0___boxed__const__1();
lean_mark_persistent(l_Lake_Toml_stdTable_parenthesizer___closed__0___boxed__const__1);
l_Lake_Toml_stdTable_parenthesizer___closed__0 = _init_l_Lake_Toml_stdTable_parenthesizer___closed__0();
lean_mark_persistent(l_Lake_Toml_stdTable_parenthesizer___closed__0);
l_Lake_Toml_stdTable_parenthesizer___closed__1___boxed__const__1 = _init_l_Lake_Toml_stdTable_parenthesizer___closed__1___boxed__const__1();
lean_mark_persistent(l_Lake_Toml_stdTable_parenthesizer___closed__1___boxed__const__1);
l_Lake_Toml_stdTable_parenthesizer___closed__1 = _init_l_Lake_Toml_stdTable_parenthesizer___closed__1();
lean_mark_persistent(l_Lake_Toml_stdTable_parenthesizer___closed__1);
l_Lake_Toml_stdTable_parenthesizer___closed__2 = _init_l_Lake_Toml_stdTable_parenthesizer___closed__2();
lean_mark_persistent(l_Lake_Toml_stdTable_parenthesizer___closed__2);
l_Lake_Toml_stdTable_parenthesizer___closed__3___boxed__const__1 = _init_l_Lake_Toml_stdTable_parenthesizer___closed__3___boxed__const__1();
lean_mark_persistent(l_Lake_Toml_stdTable_parenthesizer___closed__3___boxed__const__1);
l_Lake_Toml_stdTable_parenthesizer___closed__3 = _init_l_Lake_Toml_stdTable_parenthesizer___closed__3();
lean_mark_persistent(l_Lake_Toml_stdTable_parenthesizer___closed__3);
l_Lake_Toml_stdTable_parenthesizer___closed__4 = _init_l_Lake_Toml_stdTable_parenthesizer___closed__4();
lean_mark_persistent(l_Lake_Toml_stdTable_parenthesizer___closed__4);
l_Lake_Toml_stdTable_parenthesizer___closed__5 = _init_l_Lake_Toml_stdTable_parenthesizer___closed__5();
lean_mark_persistent(l_Lake_Toml_stdTable_parenthesizer___closed__5);
l_Lake_Toml_stdTable_parenthesizer___closed__6 = _init_l_Lake_Toml_stdTable_parenthesizer___closed__6();
lean_mark_persistent(l_Lake_Toml_stdTable_parenthesizer___closed__6);
l_Lake_Toml_arrayTable_parenthesizer___closed__0 = _init_l_Lake_Toml_arrayTable_parenthesizer___closed__0();
lean_mark_persistent(l_Lake_Toml_arrayTable_parenthesizer___closed__0);
l_Lake_Toml_arrayTable_parenthesizer___closed__1 = _init_l_Lake_Toml_arrayTable_parenthesizer___closed__1();
lean_mark_persistent(l_Lake_Toml_arrayTable_parenthesizer___closed__1);
l_Lake_Toml_arrayTable_parenthesizer___closed__2 = _init_l_Lake_Toml_arrayTable_parenthesizer___closed__2();
lean_mark_persistent(l_Lake_Toml_arrayTable_parenthesizer___closed__2);
l_Lake_Toml_arrayTable_parenthesizer___closed__3 = _init_l_Lake_Toml_arrayTable_parenthesizer___closed__3();
lean_mark_persistent(l_Lake_Toml_arrayTable_parenthesizer___closed__3);
l_Lake_Toml_arrayTable_parenthesizer___closed__4 = _init_l_Lake_Toml_arrayTable_parenthesizer___closed__4();
lean_mark_persistent(l_Lake_Toml_arrayTable_parenthesizer___closed__4);
l_Lake_Toml_arrayTable_parenthesizer___closed__5 = _init_l_Lake_Toml_arrayTable_parenthesizer___closed__5();
lean_mark_persistent(l_Lake_Toml_arrayTable_parenthesizer___closed__5);
l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___closed__0 = _init_l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___closed__0();
lean_mark_persistent(l___private_Lake_Toml_Grammar_0__Lake_Toml_expressionCore_parenthesizer___closed__0);
l_Lake_Toml_toml___closed__0 = _init_l_Lake_Toml_toml___closed__0();
lean_mark_persistent(l_Lake_Toml_toml___closed__0);
l_Lake_Toml_toml___closed__1 = _init_l_Lake_Toml_toml___closed__1();
lean_mark_persistent(l_Lake_Toml_toml___closed__1);
l_Lake_Toml_toml = _init_l_Lake_Toml_toml();
lean_mark_persistent(l_Lake_Toml_toml);
return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
