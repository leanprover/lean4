// Lean compiler output
// Module: init.lean.parser.token
// Imports: init.lean.parser.combinators init.lean.parser.stringliteral
#include "runtime/object.h"
#include "runtime/apply.h"
typedef lean::object obj;    typedef lean::usize  usize;
typedef lean::uint8  uint8;  typedef lean::uint16 uint16;
typedef lean::uint32 uint32; typedef lean::uint64 uint64;
#if defined(__clang__)
#pragma clang diagnostic ignored "-Wunused-parameter"
#pragma clang diagnostic ignored "-Wunused-label"
#elif defined(__GNUC__) && !defined(__CLANG__)
#pragma GCC diagnostic ignored "-Wunused-parameter"
#pragma GCC diagnostic ignored "-Wunused-label"
#pragma GCC diagnostic ignored "-Wunused-but-set-variable"
#endif
obj* l_Lean_Parser_ParsecT_failure___at_Lean_Parser_token___spec__4(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__23___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_number_x_27___spec__12___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__4___rarg(obj*, obj*);
extern obj* l_Lean_Parser_parseHexDigit___rarg___lambda__5___closed__1;
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_withTrailing___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_rawStr_Lean_Parser_HasTokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_Parser_view___rarg___closed__2;
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__17___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___boxed(obj*);
obj* l___private_init_lean_parser_parsec_4__mkStringResult___rarg(obj*, obj*);
obj* l_Lean_Parser_indexed___rarg___closed__1;
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__20(obj*, obj*, obj*);
obj* l_Lean_Parser_raw_view___rarg(obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_Parser___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser___spec__13(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__13(obj*, obj*, obj*);
obj* l_Lean_Parser_rawStr_Lean_Parser_HasView___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_String_foldlAux___main___at_String_toNat___spec__1___closed__1;
obj* l_Lean_Parser_stringLit;
obj* l_fixCore___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__12___boxed(obj*);
obj* l_Lean_Parser_raw_view___rarg___closed__1;
obj* l_Lean_Parser_stringLit_View_value(obj*);
obj* l_Lean_Parser_finishCommentBlock(obj*, obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2(obj*);
obj* l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_View_value___spec__8(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__11(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ident_Parser_View___rarg___lambda__2(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__15___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
extern obj* l_Lean_Parser_BasicParserM_Alternative;
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser___spec__5(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x_27___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolOrIdent_View___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at___private_init_lean_parser_token_4__ident_x_27___spec__12___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_raw___boxed(obj*);
obj* l_Lean_Parser_symbol_tokens(obj*, obj*);
obj* l_Lean_Parser_ident_Parser_tokens(obj*, obj*);
obj* l_Lean_Parser_symbolOrIdent___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_rawIdent_Parser_View___boxed(obj*);
obj* l_Lean_Parser_detailIdent_x_27___closed__1;
obj* l_Lean_Parser_MonadParsec_foldl___at___private_init_lean_parser_token_4__ident_x_27___spec__20(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_4__ident_x_27___lambda__2(uint32, uint32, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__6(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbol_tokens___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__25___boxed(obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__9(obj*, obj*, obj*);
obj* l_String_toNat(obj*);
uint8 l_Lean_isIdRest(uint32);
obj* l___private_init_lean_parser_token_4__ident_x_27___closed__1;
obj* l_Lean_Parser_detailIdent_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__27___rarg(obj*, obj*);
obj* l___private_init_lean_parser_token_4__ident_x_27(obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_4__ident_x_27___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27___main___at_Lean_Parser_parseBinLit___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__9(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(uint32, obj*, obj*, obj*);
obj* l_Lean_Parser_rawStr(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__19___boxed(obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__16(obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_3__updateTrailingLst___main(obj*, obj*);
uint8 l_Lean_isIdEndEscape(uint32);
obj* l_Lean_Parser_stringLit_Parser_tokens(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2___rarg(obj*, obj*);
obj* l_Lean_Parser_detailIdentSuffix_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolOrIdent_View___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___boxed(obj*, obj*);
uint8 l_String_isEmpty(obj*);
obj* l_Lean_Parser_detailIdent_HasView_x_27___lambda__1___closed__1;
obj* l___private_init_lean_parser_token_2__whitespaceAux___main___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_7__toNatCore___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_parseHexDigit___rarg___lambda__3___closed__1;
obj* l_Lean_Parser_stringLit_Parser___rarg(obj*);
extern obj* l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1;
obj* l_ReaderT_bind___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__6(obj*, obj*);
extern usize l_String_toSubstring___closed__1;
obj* l_Lean_Parser_symbolOrIdent___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__8___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseQuotedChar___at_Lean_Parser_stringLit_x_27___spec__3(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbol_viewDefault(obj*);
obj* l_Lean_Parser_number_Parser_view(obj*);
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x_27___spec__4___boxed(obj*);
obj* l_Lean_Parser_rawStr_viewDefault___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__3___rarg(obj*, obj*);
obj* l_Lean_Parser_parseStringLiteral___at_Lean_Parser_stringLit_x_27___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView;
obj* l___private_init_lean_parser_parsec_7__takeWhileAux_x_27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__6___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__5(obj*, obj*, obj*);
obj* l_Lean_Parser_raw_view(obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseHexLit___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_detailIdentPartEscaped_HasView;
obj* l_Lean_Parser_indexed___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbol___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbol_View___rarg(obj*, obj*, obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser___spec__6(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_asSubstring___boxed(obj*);
obj* l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView;
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__14(obj*, obj*, obj*);
obj* l_Lean_Parser_asSubstring___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_failure___at_Lean_Parser_token___spec__4___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_raw_view___rarg___closed__2;
extern obj* l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
obj* l_Lean_Parser_number_Parser___rarg___closed__1;
obj* l___private_init_lean_parser_token_2__whitespaceAux___main(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3(obj*);
obj* l_Lean_Parser_finishCommentBlock___closed__2;
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__5(obj*);
obj* l_Lean_Parser_numberOrStringLit(obj*, obj*, obj*);
obj* l_Lean_Parser_raw___rarg___lambda__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_BasicParserM_Monad;
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux___main(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_withTrailing___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_rawStr_Lean_Parser_HasView___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__11___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser___spec__1___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_2__whitespaceAux(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_stringLit_x_27___closed__1;
obj* l_Lean_Parser_number_Parser_tokens(obj*, obj*);
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__3___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_number_HasView_x_27___lambda__2(obj*);
uint8 l_Char_isAlpha(uint32);
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__1(obj*);
obj* l_Lean_Parser_rawIdent_Parser___rarg___closed__1;
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_View_value___spec__7___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_stringLit_HasView_x_27___lambda__1(obj*);
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__21(obj*);
obj* l_Lean_Parser_ParsecT_labelsMkRes___rarg(obj*, obj*);
obj* l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__2;
uint32 l_String_OldIterator_curr___main(obj*);
obj* l_List_reverse___rarg(obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__11(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__13___boxed(obj*, obj*, obj*, obj*);
obj* l_ReaderT_bind___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__10___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseOctLit___spec__1(uint32, obj*, obj*, obj*);
obj* l_Lean_Parser_token___closed__1;
obj* l_Lean_Parser_ident_Parser_View___rarg___closed__1;
obj* l___private_init_lean_parser_token_5__mkConsumeToken___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_indexed___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_raw___rarg___lambda__2(obj*, uint8, obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_Lean_Parser_Syntax_isOfKind___main(obj*, obj*);
obj* l_ReaderT_orelse___at_Lean_Parser_parseBinLit___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdent_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_stringLit_Parser_View___boxed(obj*);
obj* l_Lean_Parser_rawStr_viewDefault___boxed(obj*);
obj* l_Lean_Parser_number_x_27___closed__1;
obj* l_id___rarg___boxed(obj*);
obj* l_Lean_Parser_asSubstring___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_digit___at_Lean_Parser_stringLit_View_value___spec__9(obj*);
obj* l___private_init_lean_parser_parsec_7__takeWhileAux_x_27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__6(obj*, uint8, obj*);
obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x_27;
obj* l_String_OldIterator_remaining___main(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x_27___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_x_27___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4___boxed(obj*);
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__3___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__23(obj*);
obj* l___private_init_lean_parser_token_2__whitespaceAux___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__12(obj*);
obj* l_Lean_Parser_number_x_27___lambda__4___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_withTrailing___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__8___rarg(obj*, obj*);
obj* l_Lean_Parser_raw_view___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__10___boxed(obj*);
obj* l_Lean_Parser_number_HasView;
obj* l_Lean_Parser_number_HasView_x_27___lambda__1___closed__2;
obj* l_Option_get___main___at_Lean_Parser_run___spec__2(obj*);
obj* l_Lean_Parser_unicodeSymbol___boxed(obj*);
obj* l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_View_value___spec__4___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__10___boxed(obj*);
obj* l_Lean_Parser_unicodeSymbol_viewDefault___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_rawIdent_Parser_tokens___boxed(obj*, obj*);
obj* l_Lean_Parser_Substring_toString(obj*);
obj* l_Lean_Parser_rawStr_Lean_Parser_HasView(obj*);
obj* l_Lean_Parser_detailIdentPart_Parser(obj*, obj*, obj*);
obj* l_Lean_Parser_indexed___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseStringLiteral___at_Lean_Parser_stringLit_x_27___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2(obj*);
obj* l_Lean_Parser_MonadParsec_digit___at_Lean_Parser_stringLit_x_27___spec__6___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_asSubstring___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseQuotedChar___at_Lean_Parser_stringLit_x_27___spec__3___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_withTrailing___at_Lean_Parser_token___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_raw(obj*);
obj* l_String_OldIterator_nextn___main(obj*, obj*);
extern obj* l_Lean_Parser_RecT_runParsec___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_indexed___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseHexLit___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_number_HasView_x_27___lambda__2___closed__2;
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__19(obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__26(obj*, obj*, obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_Lean_Parser_stringLit_HasView_x_27___lambda__2(obj*);
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__3(obj*);
obj* l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__9___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__10(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdent_x_27(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_whitespace(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdent_HasView_x_27___lambda__2___closed__1;
obj* l_Lean_Parser_Syntax_asNode___main(obj*);
obj* l_Lean_Parser_MonadParsec_whitespace___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_number_x_27___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_number_Parser_view___rarg___boxed(obj*);
obj* l_Lean_Parser_symbolOrIdent(obj*);
obj* l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_View_value___spec__4(obj*, obj*, obj*);
obj* l_Lean_Parser_matchToken(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x_27___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_finishCommentBlock___boxed(obj*, obj*, obj*, obj*);
obj* l_Nat_repr(obj*);
obj* l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2(obj*);
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__8___rarg(obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__7(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentSuffix_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_tokenCont(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_mkRawRes(obj*, obj*);
obj* l_Lean_Parser_withTrailing___rarg___lambda__3(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_stringLit_Parser_View___rarg___closed__2;
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_number_x_27___spec__12(obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_4__ident_x_27___spec__19(obj*, obj*, uint32, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__1(obj*);
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__5___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_failure___at_Lean_Parser_token___spec__4___rarg(obj*, obj*);
extern obj* l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
obj* l_Lean_Parser_number_HasView_x_27___lambda__2___closed__1;
obj* l_Lean_Parser_symbol_View___boxed(obj*);
obj* l_Lean_Parser_symbol_viewDefault___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__2___boxed(obj*);
obj* l_Lean_Parser_raw_view___rarg___lambda__2(obj*);
obj* l_Lean_Parser_unicodeSymbol___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_stringLit_View_value___spec__2(uint32, obj*);
obj* l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5___closed__1;
extern obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__7___closed__1;
obj* l___private_init_lean_parser_token_4__ident_x_27___lambda__1(obj*, uint32, obj*, obj*, obj*);
obj* l_List_enumFrom___main___rarg(obj*, obj*);
obj* l_Lean_Parser_idPartDefault___at___private_init_lean_parser_token_4__ident_x_27___spec__3(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_2__strAux___main(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ident_Parser___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__2(obj*);
obj* l_ReaderT_Monad___rarg(obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_number_x_27___spec__3(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__12___rarg(obj*, obj*);
obj* l_Lean_Parser_Combinators_anyOf_view___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_anyOf___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__2(obj*, obj*, obj*, obj*);
obj* l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___boxed(obj*);
obj* l_Lean_Parser_symbolCore___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_stringLit_Parser(obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_number_x_27___spec__12___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_rawIdent_Parser_tokens(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__17___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_stringLit_x_27(obj*, obj*, obj*);
obj* l_Lean_Parser_symbol_viewDefault___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_RecT_Lean_Parser_MonadParsec___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_monadLift_view___rarg(obj*, obj*, obj*);
uint8 l_Lean_isIdBeginEscape(uint32);
obj* l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_observing___at_Lean_Parser_peekToken___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__10(obj*);
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__15(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__12___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseOctLit___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_tryView___at_Lean_Parser_number_Parser___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_ident_Parser(obj*);
obj* l_RBNode_find___main___at_Lean_NameMap_contains___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_x_27___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number;
obj* l_Lean_Parser_symbolCore___boxed(obj*);
obj* l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__2;
obj* l___private_init_lean_parser_token_3__updateTrailing(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__4(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__10(obj*);
obj* l_Lean_Parser_stringLit_Parser_View___rarg___boxed(obj*);
obj* l_Lean_Parser_tryView___at_Lean_Parser_stringLit_Parser___spec__1(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_Parser_rawStr_viewDefault(obj*);
obj* l_String_OldIterator_next___main(obj*);
obj* l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__4___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_unicodeSymbol(obj*);
obj* l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__1;
obj* l_Lean_Parser_rawIdent_Parser_View___rarg___boxed(obj*);
obj* l___private_init_lean_parser_token_5__mkConsumeToken(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_stringLit_x_27___lambda__1___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Combinators_anyOf___rarg___closed__1;
obj* l_Lean_Parser_stringLit_Parser_View___rarg(obj*);
obj* l_Lean_Parser_raw___rarg___lambda__1(obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_raw_view___rarg___lambda__1(obj*);
obj* l_Lean_Parser_Syntax_mkNode(obj*, obj*);
obj* l_Lean_Parser_symbolCore(obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__18(obj*, obj*, obj*);
obj* l_Lean_Parser_raw_view___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Option_getOrElse___main___rarg(obj*, obj*);
obj* l___private_init_lean_parser_token_7__toNatCore(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ident_Parser___rarg(obj*);
obj* l_Lean_Parser_stringLit_Parser_View(obj*);
obj* l_List_mfoldr___main___at_Lean_Parser_number_x_27___spec__13___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_asSubstring(obj*);
obj* l_Lean_Parser_RecT_recurse___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__7(obj*, obj*, obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_Parser_parseOctLit___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasView___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_whitespace___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens(obj*, obj*);
obj* l_Lean_Parser_asSubstring___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__12(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj*);
extern obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
uint32 l_Char_ofNat(obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_parseOctLit___spec__3(uint32, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdent_Parser___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ident_Parser___rarg___closed__1;
extern obj* l_Char_HasRepr___closed__1;
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x_27___spec__6(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser___spec__1(obj*, obj*, uint32, obj*, obj*);
extern obj* l_Lean_Parser_noKind;
obj* l_Lean_Parser_ident_Parser_View___boxed(obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__18(obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Parser_number_x_27___spec__9(obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_parseOctLit___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbol_View___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__5(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_matchToken___closed__1;
obj* l_Lean_Parser_whitespace___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__17(obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__24(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__17(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_rawIdent_Parser(obj*);
extern uint32 l_Lean_idBeginEscape;
obj* l_Lean_Parser_symbolOrIdent_tokens___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_HasView_x_27;
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser___spec__3(obj*, obj*, obj*);
obj* l_Lean_Parser_rawIdent_Parser_View(obj*);
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__5___boxed(obj*);
obj* l_Char_quoteCore(uint32);
obj* l_Lean_Parser_ParsecT_orelseMkRes___rarg(obj*, obj*);
uint8 l_String_OldIterator_hasNext___main(obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__3(uint32, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens;
obj* l___private_init_lean_parser_token_4__ident_x_27___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_2__whitespaceAux___main___closed__1;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__15(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseBinLit___closed__1;
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__9(obj*, obj*, obj*, obj*);
obj* l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2(obj*, obj*);
obj* l_Lean_Parser_detailIdentPart;
obj* l___private_init_lean_parser_token_8__toNatBase(obj*, obj*);
obj* l_Lean_Parser_idPartEscaped___at___private_init_lean_parser_token_4__ident_x_27___spec__10___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_Trie_matchPrefix___rarg(obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_HasView_x_27___lambda__2___closed__4;
obj* l_Lean_Parser_symbolCore___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_tokens___rarg(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__12(obj*);
obj* l_Lean_Parser_raw___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_4__ident_x_27___spec__19___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_ident_Parser_tokens___boxed(obj*, obj*);
obj* l_Lean_Parser_symbol_tokens___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__23___rarg(obj*, obj*);
obj* l_Lean_Parser_peekToken___closed__1;
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__25(obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_token___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbol___boxed(obj*);
obj* l_Lean_Parser_ParsecT_tryMkRes___rarg(obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___boxed(obj*);
obj* l_Lean_Parser_ident_Parser_View___rarg(obj*);
obj* l_Lean_Parser_idPart___at___private_init_lean_parser_token_4__ident_x_27___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_3__updateTrailingLst(obj*, obj*);
obj* l_Lean_Parser_number_Parser_view___rarg(obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__22(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_6__mkConsumedResult___rarg(uint8, obj*);
obj* l_Lean_Parser_detailIdent;
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasView___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__8(obj*);
obj* l_Lean_Parser_symbol___rarg(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__14(obj*, obj*, obj*);
obj* l_Lean_Parser_parseHexLit(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x_27___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__5___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__5___boxed(obj*);
obj* l_Lean_Parser_detailIdent_HasView;
obj* l___private_init_lean_parser_token_3__updateTrailing___main(obj*, obj*);
obj* l_Lean_Parser_detailIdent_Parser___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolCore___rarg(obj*, obj*, obj*, obj*);
obj* l_ReaderT_orelse___at_Lean_Parser_parseBinLit___spec__1___boxed(obj*);
obj* l_Lean_Parser_tryView___at_Lean_Parser_number_Parser___spec__1(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__25___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_number_x_27___spec__12___boxed(obj*);
obj* l_Lean_Parser_detailIdentPart_Parser___closed__1;
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__5(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4(obj*);
obj* l_Lean_Parser_detailIdentPartEscaped;
obj* l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_List_mfoldl___main___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__9(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentSuffix_HasView;
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_peekToken___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_symbolOrIdent_View(obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__3(obj*, obj*, obj*);
obj* l_Lean_Parser_number_Parser_view___rarg___closed__1;
obj* l_Lean_Parser_Combinators_seqRight_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__21___rarg(obj*, obj*);
obj* l_Lean_Parser_indexed___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasView(obj*);
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
obj* l_Lean_Parser_rawIdent_Parser_View___rarg(obj*);
obj* l_Lean_Parser_finishCommentBlock___closed__1;
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__1___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27___main___at_Lean_Parser_parseBinLit___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_Parsec_parse___spec__1___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_x_27___lambda__1(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_number_x_27___spec__7(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__5(obj*, obj*, obj*);
obj* l_Lean_Parser_raw_tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_Parser___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__4___boxed(obj*);
obj* l_Lean_Parser_stringLit_View_value___closed__1;
obj* l_Lean_Parser_symbol_View(obj*);
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux(obj*, obj*, obj*, obj*, obj*);
uint8 l_Char_isDigit(uint32);
obj* l_Lean_Parser_number_Parser_view___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__2___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_stringLit_Parser_tokens___boxed(obj*, obj*);
obj* l_Lean_Parser_idPart___at___private_init_lean_parser_token_4__ident_x_27___spec__1___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_7__toNatCore___main(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_8__toNatBase___boxed(obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__3(obj*, obj*, obj*);
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__5___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_ident_Parser_View___rarg___boxed(obj*);
obj* l_Lean_Parser_stringLit_Parser___boxed(obj*);
obj* l_Lean_Parser_parseOctLit(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__3;
obj* l_Lean_Parser_withTrailing___rarg___lambda__2(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__7(obj*, obj*, obj*);
obj* l_Lean_Parser_number_Parser___rarg(obj*);
obj* l_Lean_Parser_number_HasView_x_27___lambda__1___closed__5;
obj* l_Lean_Parser_detailIdent_Parser___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_String_trim(obj*);
obj* l_Lean_Parser_stringLit_x_27___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_Parser(obj*);
obj* l_Lean_Parser_ParsecT_bindMkRes___rarg(obj*, obj*);
obj* l_Lean_Parser_peekToken___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdent_Parser___closed__1;
obj* l_Lean_Parser_number_HasView_x_27___lambda__1___closed__4;
obj* l_Lean_Parser_ident_Parser___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolOrIdent___rarg(obj*, obj*);
obj* l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__1(uint32, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_rawStr_Lean_Parser_HasView___rarg(obj*, obj*, obj*, obj*, uint8);
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__8(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2___boxed(obj*);
obj* l_Lean_Parser_number_x_27___lambda__3(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_MonadParsec_longestMatch___rarg___lambda__2___closed__1;
obj* l_Lean_Parser_symbol___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentSuffix_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_symbol_viewDefault___boxed(obj*);
obj* l___private_init_lean_parser_parsec_7__takeWhileAux_x_27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__3___boxed(obj*, obj*, obj*);
obj* l_List_mfoldr___main___at_Lean_Parser_number_x_27___spec__13(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_ReaderT_MonadExcept___rarg(obj*);
obj* l_Lean_Parser_ident_Parser_View(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__27(obj*);
obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__2;
obj* l_Lean_Parser_raw___rarg(obj*, obj*, obj*, obj*, obj*, uint8);
extern obj* l_Int_repr___main___closed__2;
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__27___boxed(obj*);
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_Lean_Parser_detailIdent_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_MonadParsec_longestMatch___at_Lean_Parser_number_x_27___spec__10(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__2___rarg(obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_parseHexLit___spec__3(obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasView___boxed(obj*);
extern obj* l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
obj* l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__3;
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__8(obj*, obj*, obj*);
obj* l_Lean_Parser_ident_Parser_View___rarg___lambda__1(obj*);
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x_27___spec__4___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_token(obj*, obj*, obj*);
obj* l_Lean_Parser_rawStr___rarg(obj*, obj*, obj*, obj*, uint8);
obj* l_Lean_Parser_rawStr___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__2(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_2__whitespaceAux___main___closed__2;
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseHexLit___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_stringLit_Parser___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_longestChoice___at_Lean_Parser_number_x_27___spec__8(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser___spec__4(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_List_cons_tokens___rarg(obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser___spec__7(obj*, obj*, obj*);
obj* l_Lean_Parser_raw___rarg___lambda__3(uint8, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x_27___spec__4(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_number_x_27___spec__11(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_withTrailing___at_Lean_Parser_token___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser___spec__11(obj*, obj*, obj*);
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__4(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__10___rarg(obj*, obj*);
obj* l_Lean_Parser_number_View_ofNat(obj*);
uint8 l_Char_isWhitespace(uint32);
obj* l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2(obj*);
obj* l_Lean_Parser_number_x_27(obj*, obj*, obj*);
obj* l_DList_singleton___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1(uint32, obj*, obj*, obj*, obj*);
obj* l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___boxed(obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__2;
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__13___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__4;
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__28(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdent_Parser(obj*, obj*, obj*);
obj* l_Lean_Parser_peekToken(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__13(obj*, obj*, obj*, obj*);
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__1___boxed(obj*);
obj* l_List_mfoldl___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__16(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__4(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1(obj*);
obj* l_Lean_Parser_detailIdentSuffix_Parser___closed__1;
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__8(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_number_x_27___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_number_HasView_x_27;
obj* l_Lean_Parser_MonadParsec_takeWhile1___at___private_init_lean_parser_token_4__ident_x_27___spec__12(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_strCore___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolCore___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x_27___spec__4(obj*);
obj* l_Lean_Parser_rawStr___boxed(obj*);
obj* l_Lean_Parser_symbolOrIdent_View___rarg(obj*, obj*);
obj* l_Lean_Parser_withTrailing___boxed(obj*);
obj* l_Lean_Parser_number_HasView_x_27___lambda__1___closed__6;
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__5___rarg(obj*, obj*);
obj* l_Lean_Parser_number_HasView_x_27___lambda__2___closed__3;
obj* l_Lean_Parser_idPartEscaped___at___private_init_lean_parser_token_4__ident_x_27___spec__10(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__1___closed__1;
obj* l_Lean_Parser_detailIdentPart_HasView;
obj* l_Lean_Parser_number_x_27___lambda__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseQuotedChar___at_Lean_Parser_stringLit_View_value___spec__6(obj*);
extern uint8 l_True_Decidable;
obj* l_Lean_Parser_stringLit_HasView_x_27___lambda__2___closed__1;
obj* l_Lean_Parser_MonadParsec_observing___at_Lean_Parser_token___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_indexed(obj*);
obj* l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5(obj*, obj*, obj*);
obj* l_ReaderT_orelse___at_Lean_Parser_parseBinLit___spec__1(obj*);
obj* l_Lean_Parser_number_HasView_x_27___lambda__2___closed__6;
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser___spec__2(obj*, obj*, obj*, obj*);
namespace lean {
uint32 uint32_of_nat(obj*);
}
obj* l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__1;
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_Parser___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_HasView_x_27___lambda__1___closed__3;
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2___boxed(obj*);
obj* l___private_init_lean_parser_token_2__whitespaceAux___main___closed__3;
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_ReaderT_Alternative___rarg(obj*, obj*);
obj* l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__6(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__2(obj*, obj*, obj*);
obj* l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_number_x_27___spec__11___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x_27___spec__4___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__19___rarg(obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser___spec__9(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_7__takeWhileAux_x_27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__3(obj*, uint8, obj*);
obj* l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__29(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_raw___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentSuffix_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_detailIdent_Parser___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__3;
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__1___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_detailIdent_x_27___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_rawIdent_Parser___boxed(obj*);
obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__1;
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l_Lean_Parser_tryView___at_Lean_Parser_stringLit_Parser___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__21___boxed(obj*);
obj* l_Lean_Parser_number_Parser___boxed(obj*);
obj* l_Lean_Parser_raw_tokens(obj*, obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_token___closed__2;
obj* l_Lean_Parser_ident_Parser_View___rarg___lambda__1___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_rawStr_viewDefault___rarg(obj*, obj*, obj*, obj*, uint8);
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__3(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbol_viewDefault(obj*);
obj* l_Lean_Parser_unicodeSymbol_viewDefault___boxed(obj*);
obj* l_Lean_Parser_ident_Parser_View___rarg___closed__2;
obj* l_Lean_Parser_stringLit_HasView;
obj* l_Lean_Parser_detailIdentSuffix_HasView_x_27;
obj* l_Lean_Parser_detailIdentPart_Parser___lambda__2(obj*, obj*, obj*, obj*);
extern uint32 l_Lean_idEndEscape;
obj* l_Lean_Parser_number_x_27___lambda__4(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_View_value___spec__7___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentSuffix;
obj* l_Lean_Parser_asSubstring___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_idPartDefault___at___private_init_lean_parser_token_4__ident_x_27___spec__3___boxed(obj*, obj*, obj*);
obj* l_String_quote(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__8___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_number_x_27___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__13(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_7__toNatCore___main___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_withTrailing___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbol_tokens___boxed(obj*, obj*);
obj* l_Lean_Parser_detailIdent_HasView_x_27;
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_View_value___spec__7(obj*);
obj* l_Lean_Parser_parseHexLit___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_withTrailing___rarg___closed__1;
obj* l_Lean_Parser_tokenCont___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__17___rarg(obj*, obj*);
obj* l_Lean_Parser_ParsecT_merge___rarg(obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__4(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_indexed___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__8(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__5(obj*);
obj* l_Lean_Parser_number_HasView_x_27___lambda__2___closed__5;
obj* l_Lean_Parser_Substring_ofString(obj*);
obj* l_Lean_Parser_stringLit_HasView_x_27;
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolOrIdent_tokens(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseHexLit___spec__2(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_BasicParserM_MonadExcept;
obj* l_Lean_Parser_asSubstring___rarg___lambda__1(obj*, obj*, obj*);
obj* l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_ParsecT_failure___rarg___closed__1;
uint8 l_Lean_isIdFirst(uint32);
namespace lean {
obj* nat_mul(obj*, obj*);
}
extern obj* l_Lean_Parser_Combinators_many___rarg___closed__1;
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseOctLit___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_Parser_tokens___boxed(obj*, obj*);
obj* l_Lean_Parser_symbol(obj*);
obj* l_Lean_Parser_unicodeSymbol_viewDefault___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_View_value___spec__7___boxed(obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___spec__1(uint32, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_rawIdent_Parser___rarg(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseOctLit___spec__2(uint32, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_stringLit_Parser_View___rarg___closed__1;
obj* l___private_init_lean_parser_token_2__whitespaceAux___main___closed__4;
obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__3;
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_detailIdent_x_27___spec__1(obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_ReaderT_bind___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__6___boxed(obj*, obj*);
obj* l_Lean_Parser_raw___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_HasView_x_27___lambda__1(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_withTrailing(obj*);
obj* l_Lean_Parser_rawStr_Lean_Parser_HasTokens(obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_Lean_Parser_parseStringLiteral___at_Lean_Parser_stringLit_View_value___spec__1(obj*);
obj* l_List_map___main___at_Lean_Parser_number_x_27___spec__9___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_digit___at_Lean_Parser_stringLit_x_27___spec__6(obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__2;
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__12___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_stringLit_View_value___spec__2___boxed(obj*, obj*);
obj* l_Lean_Parser_number_View_toNat___main(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__8___boxed(obj*);
obj* l_Lean_Parser_number_View_toNat(obj*);
obj* l_Lean_Parser_number_x_27___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_token___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__7(obj*, obj*, obj*);
obj* l_Lean_Parser_number_Parser___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseBinLit(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_number_x_27___spec__5(obj*, obj*, obj*);
obj* l_Lean_Parser_stringLit_Parser___rarg___closed__1;
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__8___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__6(obj*, obj*, obj*, obj*);
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_any___at_Lean_Parser_stringLit_View_value___spec__5(obj*);
namespace lean {
obj* string_length(obj*);
}
obj* l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1(obj*);
obj* _init_l_Lean_Parser_matchToken___closed__1() {
_start:
{
obj* x_0; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
lean::inc(x_0);
lean::inc(x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_3, 0, x_0);
lean::closure_set(x_3, 1, x_0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_4, 0, x_0);
lean::closure_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_Lean_Parser_matchToken(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_7; 
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
lean::inc(x_1);
x_7 = l_Lean_Parser_Trie_matchPrefix___rarg(x_3, x_1);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::box(0);
x_9 = l_Lean_Parser_matchToken___closed__1;
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_1);
lean::cnstr_set(x_10, 2, x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_12 = lean::cnstr_get(x_7, 0);
if (lean::is_exclusive(x_7)) {
 x_14 = x_7;
} else {
 lean::inc(x_12);
 lean::dec(x_7);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_12, 1);
lean::inc(x_15);
lean::dec(x_12);
if (lean::is_scalar(x_14)) {
 x_18 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_18 = x_14;
}
lean::cnstr_set(x_18, 0, x_15);
x_19 = l_Lean_Parser_matchToken___closed__1;
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_1);
lean::cnstr_set(x_20, 2, x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_2);
return x_21;
}
}
}
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_12; 
x_7 = l_Option_getOrElse___main___rarg(x_2, x_5);
x_8 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_0);
lean::cnstr_set(x_8, 2, x_1);
lean::cnstr_set(x_8, 3, x_3);
x_9 = 0;
x_10 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set_scalar(x_10, sizeof(void*)*1, x_9);
x_11 = x_10;
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_6);
return x_12;
}
}
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg___boxed), 7, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__2(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_String_OldIterator_hasNext___main(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_4 = lean::box(0);
x_5 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 x_13 = x_7;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_9);
if (lean::is_scalar(x_13)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_13;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_11);
return x_16;
}
else
{
uint32 x_17; uint8 x_18; 
x_17 = l_String_OldIterator_curr___main(x_1);
x_18 = l_True_Decidable;
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_19 = l_Char_quoteCore(x_17);
x_20 = l_Char_HasRepr___closed__1;
x_21 = lean::string_append(x_20, x_19);
lean::dec(x_19);
x_23 = lean::string_append(x_21, x_20);
x_24 = lean::box(0);
x_25 = l_mjoin___rarg___closed__1;
x_26 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_23, x_25, x_24, x_24, x_0, x_1, x_2);
lean::dec(x_1);
x_28 = lean::cnstr_get(x_26, 0);
x_30 = lean::cnstr_get(x_26, 1);
if (lean::is_exclusive(x_26)) {
 x_32 = x_26;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::dec(x_26);
 x_32 = lean::box(0);
}
x_33 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_34 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_33, x_28);
if (lean::is_scalar(x_32)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_32;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_30);
return x_35;
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_36 = l_String_OldIterator_next___main(x_1);
x_37 = lean::box(0);
x_38 = lean::box_uint32(x_17);
x_39 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_36);
lean::cnstr_set(x_39, 2, x_37);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_2);
return x_40;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = l_String_isEmpty(x_0);
if (x_5 == 0)
{
obj* x_6; obj* x_7; usize x_8; obj* x_10; obj* x_11; obj* x_13; 
x_6 = lean::string_length(x_0);
x_7 = lean::mk_nat_obj(0u);
x_8 = l_String_toSubstring___closed__1;
lean::inc(x_0);
x_10 = lean::alloc_cnstr(0, 2, sizeof(size_t)*1);
lean::cnstr_set(x_10, 0, x_0);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set_scalar(x_10, sizeof(void*)*2, x_8);
x_11 = x_10;
lean::inc(x_3);
x_13 = l___private_init_lean_parser_parsec_2__strAux___main(x_6, x_11, x_3);
if (lean::obj_tag(x_13) == 0)
{
obj* x_15; obj* x_16; obj* x_17; uint8 x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_0);
x_15 = lean::box(0);
x_16 = l_String_splitAux___main___closed__1;
x_17 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_17, 0, x_3);
lean::cnstr_set(x_17, 1, x_16);
lean::cnstr_set(x_17, 2, x_1);
lean::cnstr_set(x_17, 3, x_15);
x_18 = 0;
x_19 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set_scalar(x_19, sizeof(void*)*1, x_18);
x_20 = x_19;
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_4);
return x_21;
}
else
{
obj* x_24; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_1);
lean::dec(x_3);
x_24 = lean::cnstr_get(x_13, 0);
lean::inc(x_24);
lean::dec(x_13);
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_28, 0, x_0);
lean::cnstr_set(x_28, 1, x_24);
lean::cnstr_set(x_28, 2, x_27);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_4);
return x_29;
}
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
lean::dec(x_1);
lean::dec(x_0);
x_32 = l_String_splitAux___main___closed__1;
x_33 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_34 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_3);
lean::cnstr_set(x_34, 2, x_33);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_4);
return x_35;
}
}
}
obj* _init_l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("-/");
return x_0;
}
}
obj* _init_l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("-/");
x_1 = l_String_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("/-");
return x_0;
}
}
obj* _init_l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("/-");
x_1 = l_String_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; uint8 x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_17; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_1, x_7);
x_9 = lean::nat_dec_eq(x_0, x_7);
x_13 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__3;
x_14 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__4;
lean::inc(x_3);
x_16 = l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3(x_13, x_14, x_2, x_3, x_4);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_19; obj* x_22; obj* x_24; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_35; 
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
x_22 = lean::cnstr_get(x_17, 1);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_17, 2);
lean::inc(x_24);
lean::dec(x_17);
x_27 = lean::nat_add(x_0, x_7);
x_28 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main(x_27, x_8, x_2, x_22, x_19);
lean::dec(x_27);
x_30 = lean::cnstr_get(x_28, 0);
lean::inc(x_30);
x_32 = lean::cnstr_get(x_28, 1);
lean::inc(x_32);
lean::dec(x_28);
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_30);
x_10 = x_35;
x_11 = x_32;
goto lbl_12;
}
else
{
obj* x_36; obj* x_39; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; 
x_36 = lean::cnstr_get(x_16, 1);
lean::inc(x_36);
lean::dec(x_16);
x_39 = lean::cnstr_get(x_17, 0);
x_41 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*1);
if (lean::is_exclusive(x_17)) {
 x_42 = x_17;
} else {
 lean::inc(x_39);
 lean::dec(x_17);
 x_42 = lean::box(0);
}
if (lean::is_scalar(x_42)) {
 x_43 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_43 = x_42;
}
lean::cnstr_set(x_43, 0, x_39);
lean::cnstr_set_scalar(x_43, sizeof(void*)*1, x_41);
x_44 = x_43;
x_10 = x_44;
x_11 = x_36;
goto lbl_12;
}
lbl_12:
{
if (lean::obj_tag(x_10) == 0)
{
obj* x_47; 
lean::dec(x_8);
lean::dec(x_3);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_10);
lean::cnstr_set(x_47, 1, x_11);
return x_47;
}
else
{
obj* x_48; uint8 x_50; obj* x_51; obj* x_52; 
x_48 = lean::cnstr_get(x_10, 0);
lean::inc(x_48);
x_50 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (x_50 == 0)
{
obj* x_55; obj* x_56; obj* x_58; obj* x_59; 
lean::dec(x_10);
x_55 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__1;
x_56 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__2;
lean::inc(x_3);
x_58 = l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3(x_55, x_56, x_2, x_3, x_11);
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
if (lean::obj_tag(x_59) == 0)
{
if (x_9 == 0)
{
obj* x_61; obj* x_64; obj* x_66; obj* x_69; obj* x_70; obj* x_72; obj* x_74; obj* x_77; 
x_61 = lean::cnstr_get(x_58, 1);
lean::inc(x_61);
lean::dec(x_58);
x_64 = lean::cnstr_get(x_59, 1);
lean::inc(x_64);
x_66 = lean::cnstr_get(x_59, 2);
lean::inc(x_66);
lean::dec(x_59);
x_69 = lean::nat_sub(x_0, x_7);
x_70 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main(x_69, x_8, x_2, x_64, x_61);
lean::dec(x_69);
x_72 = lean::cnstr_get(x_70, 0);
lean::inc(x_72);
x_74 = lean::cnstr_get(x_70, 1);
lean::inc(x_74);
lean::dec(x_70);
x_77 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_66, x_72);
x_51 = x_77;
x_52 = x_74;
goto lbl_53;
}
else
{
obj* x_78; obj* x_81; obj* x_83; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_78 = lean::cnstr_get(x_58, 1);
lean::inc(x_78);
lean::dec(x_58);
x_81 = lean::cnstr_get(x_59, 1);
x_83 = lean::cnstr_get(x_59, 2);
if (lean::is_exclusive(x_59)) {
 lean::cnstr_release(x_59, 0);
 x_85 = x_59;
} else {
 lean::inc(x_81);
 lean::inc(x_83);
 lean::dec(x_59);
 x_85 = lean::box(0);
}
x_86 = lean::box(0);
x_87 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_85)) {
 x_88 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_88 = x_85;
}
lean::cnstr_set(x_88, 0, x_86);
lean::cnstr_set(x_88, 1, x_81);
lean::cnstr_set(x_88, 2, x_87);
x_89 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_83, x_88);
x_51 = x_89;
x_52 = x_78;
goto lbl_53;
}
}
else
{
obj* x_90; obj* x_93; uint8 x_95; obj* x_96; obj* x_97; obj* x_98; 
x_90 = lean::cnstr_get(x_58, 1);
lean::inc(x_90);
lean::dec(x_58);
x_93 = lean::cnstr_get(x_59, 0);
x_95 = lean::cnstr_get_scalar<uint8>(x_59, sizeof(void*)*1);
if (lean::is_exclusive(x_59)) {
 x_96 = x_59;
} else {
 lean::inc(x_93);
 lean::dec(x_59);
 x_96 = lean::box(0);
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_93);
lean::cnstr_set_scalar(x_97, sizeof(void*)*1, x_95);
x_98 = x_97;
x_51 = x_98;
x_52 = x_90;
goto lbl_53;
}
}
else
{
obj* x_102; 
lean::dec(x_8);
lean::dec(x_3);
lean::dec(x_48);
x_102 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_102, 0, x_10);
lean::cnstr_set(x_102, 1, x_11);
return x_102;
}
lbl_53:
{
if (lean::obj_tag(x_51) == 0)
{
obj* x_105; obj* x_106; 
lean::dec(x_8);
lean::dec(x_3);
x_105 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_48, x_51);
x_106 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_106, 0, x_105);
lean::cnstr_set(x_106, 1, x_52);
return x_106;
}
else
{
uint8 x_107; 
x_107 = lean::cnstr_get_scalar<uint8>(x_51, sizeof(void*)*1);
if (x_107 == 0)
{
obj* x_108; obj* x_111; obj* x_112; 
x_108 = lean::cnstr_get(x_51, 0);
lean::inc(x_108);
lean::dec(x_51);
x_111 = l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__2(x_2, x_3, x_52);
x_112 = lean::cnstr_get(x_111, 0);
lean::inc(x_112);
if (lean::obj_tag(x_112) == 0)
{
obj* x_114; obj* x_117; obj* x_119; obj* x_122; obj* x_124; obj* x_126; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; 
x_114 = lean::cnstr_get(x_111, 1);
lean::inc(x_114);
lean::dec(x_111);
x_117 = lean::cnstr_get(x_112, 1);
lean::inc(x_117);
x_119 = lean::cnstr_get(x_112, 2);
lean::inc(x_119);
lean::dec(x_112);
x_122 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main(x_0, x_8, x_2, x_117, x_114);
lean::dec(x_8);
x_124 = lean::cnstr_get(x_122, 0);
x_126 = lean::cnstr_get(x_122, 1);
if (lean::is_exclusive(x_122)) {
 x_128 = x_122;
} else {
 lean::inc(x_124);
 lean::inc(x_126);
 lean::dec(x_122);
 x_128 = lean::box(0);
}
x_129 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_119, x_124);
x_130 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_108, x_129);
x_131 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_48, x_130);
if (lean::is_scalar(x_128)) {
 x_132 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_132 = x_128;
}
lean::cnstr_set(x_132, 0, x_131);
lean::cnstr_set(x_132, 1, x_126);
return x_132;
}
else
{
obj* x_134; obj* x_136; obj* x_137; uint8 x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
lean::dec(x_8);
x_134 = lean::cnstr_get(x_111, 1);
if (lean::is_exclusive(x_111)) {
 lean::cnstr_release(x_111, 0);
 x_136 = x_111;
} else {
 lean::inc(x_134);
 lean::dec(x_111);
 x_136 = lean::box(0);
}
x_137 = lean::cnstr_get(x_112, 0);
x_139 = lean::cnstr_get_scalar<uint8>(x_112, sizeof(void*)*1);
if (lean::is_exclusive(x_112)) {
 x_140 = x_112;
} else {
 lean::inc(x_137);
 lean::dec(x_112);
 x_140 = lean::box(0);
}
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_137);
lean::cnstr_set_scalar(x_141, sizeof(void*)*1, x_139);
x_142 = x_141;
x_143 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_108, x_142);
x_144 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_48, x_143);
if (lean::is_scalar(x_136)) {
 x_145 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_145 = x_136;
}
lean::cnstr_set(x_145, 0, x_144);
lean::cnstr_set(x_145, 1, x_134);
return x_145;
}
}
else
{
obj* x_148; obj* x_149; 
lean::dec(x_8);
lean::dec(x_3);
x_148 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_48, x_51);
x_149 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_149, 0, x_148);
lean::cnstr_set(x_149, 1, x_52);
return x_149;
}
}
}
}
}
}
else
{
obj* x_150; obj* x_151; obj* x_152; obj* x_153; 
x_150 = lean::box(0);
x_151 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
x_152 = l_mjoin___rarg___closed__1;
x_153 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_151, x_152, x_150, x_150, x_2, x_3, x_4);
lean::dec(x_3);
return x_153;
}
}
}
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
lean::dec(x_4);
lean::dec(x_5);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__2(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main(x_0, x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_token_1__finishCommentBlockAux(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_Lean_Parser_finishCommentBlock___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("end of comment block");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_finishCommentBlock___closed__2() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
lean::inc(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_0);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_Lean_Parser_finishCommentBlock(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_add(x_4, x_5);
lean::dec(x_4);
x_8 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main(x_0, x_6, x_1, x_2, x_3);
lean::dec(x_6);
x_10 = lean::cnstr_get(x_8, 0);
x_12 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 x_14 = x_8;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_8);
 x_14 = lean::box(0);
}
x_15 = l_Lean_Parser_finishCommentBlock___closed__1;
x_16 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_10, x_15);
x_17 = l_Lean_Parser_finishCommentBlock___closed__2;
x_18 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_16);
if (lean::is_scalar(x_14)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_14;
}
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_12);
return x_19;
}
}
obj* l_Lean_Parser_finishCommentBlock___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_finishCommentBlock(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_parser_parsec_7__takeWhileAux_x_27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__3(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_6__mkConsumedResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Char_isWhitespace(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_6__mkConsumedResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; uint8 x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = l_String_OldIterator_next___main(x_2);
x_16 = 1;
x_0 = x_13;
x_1 = x_16;
x_2 = x_15;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_6__mkConsumedResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; obj* x_4; obj* x_5; 
x_2 = l_String_OldIterator_remaining___main(x_0);
x_3 = 0;
x_4 = l___private_init_lean_parser_parsec_7__takeWhileAux_x_27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__3(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile_x_27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__2___rarg), 2, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_whitespace___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhile_x_27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__2___rarg(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; 
x_4 = l_Int_repr___main___closed__2;
lean::inc(x_2);
x_6 = l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3(x_4, x_1, x_0, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_set(x_6, 1, lean::box(0));
 x_11 = x_6;
} else {
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_7, 1);
x_14 = lean::cnstr_get(x_7, 2);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_16 = x_7;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_7);
 x_16 = lean::box(0);
}
x_17 = 0;
x_18 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_19 = lean::box(x_17);
if (lean::is_scalar(x_16)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_16;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_12);
lean::cnstr_set(x_20, 2, x_18);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_20);
if (lean::obj_tag(x_21) == 0)
{
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
x_22 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_release(x_21, 1);
 lean::cnstr_release(x_21, 2);
 x_24 = x_21;
} else {
 lean::inc(x_22);
 lean::dec(x_21);
 x_24 = lean::box(0);
}
if (lean::is_scalar(x_24)) {
 x_25 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_25 = x_24;
}
lean::cnstr_set(x_25, 0, x_22);
lean::cnstr_set(x_25, 1, x_2);
lean::cnstr_set(x_25, 2, x_18);
if (lean::is_scalar(x_11)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_11;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_9);
return x_26;
}
else
{
obj* x_28; 
lean::dec(x_2);
if (lean::is_scalar(x_11)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_11;
}
lean::cnstr_set(x_28, 0, x_21);
lean::cnstr_set(x_28, 1, x_9);
return x_28;
}
}
else
{
uint8 x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_21);
x_30 = 1;
x_31 = lean::box(x_30);
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_2);
lean::cnstr_set(x_32, 2, x_18);
if (lean::is_scalar(x_11)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_11;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_9);
return x_33;
}
}
else
{
obj* x_35; obj* x_37; uint8 x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_7);
x_35 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_37 = x_6;
} else {
 lean::inc(x_35);
 lean::dec(x_6);
 x_37 = lean::box(0);
}
x_38 = 1;
x_39 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_40 = lean::box(x_38);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_2);
lean::cnstr_set(x_41, 2, x_39);
if (lean::is_scalar(x_37)) {
 x_42 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_42 = x_37;
}
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_35);
return x_42;
}
}
}
obj* l___private_init_lean_parser_parsec_7__takeWhileAux_x_27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__6(obj* x_0, uint8 x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_6__mkConsumedResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint32 x_9; uint8 x_10; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = 10;
x_10 = x_8 == x_9;
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_14; uint8 x_15; 
x_11 = lean::mk_nat_obj(1u);
x_12 = lean::nat_sub(x_0, x_11);
lean::dec(x_0);
x_14 = l_String_OldIterator_next___main(x_2);
x_15 = 1;
x_0 = x_12;
x_1 = x_15;
x_2 = x_14;
goto _start;
}
else
{
obj* x_18; 
lean::dec(x_0);
x_18 = l___private_init_lean_parser_parsec_6__mkConsumedResult___rarg(x_1, x_2);
return x_18;
}
}
}
else
{
obj* x_20; 
lean::dec(x_0);
x_20 = l___private_init_lean_parser_parsec_6__mkConsumedResult___rarg(x_1, x_2);
return x_20;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__5___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; uint8 x_3; obj* x_4; obj* x_5; 
x_2 = l_String_OldIterator_remaining___main(x_0);
x_3 = 0;
x_4 = l___private_init_lean_parser_parsec_7__takeWhileAux_x_27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__6(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__5(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile_x_27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__5___rarg), 2, 0);
return x_1;
}
}
obj* _init_l___private_init_lean_parser_token_2__whitespaceAux___main___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("-");
x_1 = l_String_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l___private_init_lean_parser_token_2__whitespaceAux___main___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("input");
return x_0;
}
}
obj* _init_l___private_init_lean_parser_token_2__whitespaceAux___main___closed__3() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("--");
return x_0;
}
}
obj* _init_l___private_init_lean_parser_token_2__whitespaceAux___main___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("--");
x_1 = l_String_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_token_2__whitespaceAux___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_0, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = l_Lean_Parser_MonadParsec_whitespace___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__1(x_1, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_25; obj* x_26; 
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_set(x_6, 1, lean::box(0));
 x_11 = x_6;
} else {
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_7, 1);
x_14 = lean::cnstr_get(x_7, 2);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_set(x_7, 1, lean::box(0));
 lean::cnstr_set(x_7, 2, lean::box(0));
 x_16 = x_7;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_7);
 x_16 = lean::box(0);
}
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_sub(x_0, x_17);
x_22 = l___private_init_lean_parser_token_2__whitespaceAux___main___closed__3;
x_23 = l___private_init_lean_parser_token_2__whitespaceAux___main___closed__4;
lean::inc(x_12);
x_25 = l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3(x_22, x_23, x_1, x_12, x_9);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
if (lean::obj_tag(x_26) == 0)
{
obj* x_28; obj* x_31; obj* x_33; obj* x_36; obj* x_37; obj* x_39; obj* x_42; 
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
x_31 = lean::cnstr_get(x_26, 1);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_26, 2);
lean::inc(x_33);
lean::dec(x_26);
x_36 = l_Lean_Parser_MonadParsec_takeWhile_x_27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__5___rarg(x_31, x_28);
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
lean::dec(x_36);
x_42 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_33, x_37);
if (lean::obj_tag(x_42) == 0)
{
obj* x_43; obj* x_45; obj* x_48; obj* x_49; obj* x_51; obj* x_54; 
x_43 = lean::cnstr_get(x_42, 1);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_42, 2);
lean::inc(x_45);
lean::dec(x_42);
x_48 = l___private_init_lean_parser_token_2__whitespaceAux___main(x_18, x_1, x_43, x_39);
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
lean::dec(x_48);
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_45, x_49);
x_19 = x_54;
x_20 = x_51;
goto lbl_21;
}
else
{
obj* x_55; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; 
x_55 = lean::cnstr_get(x_42, 0);
x_57 = lean::cnstr_get_scalar<uint8>(x_42, sizeof(void*)*1);
if (lean::is_exclusive(x_42)) {
 x_58 = x_42;
} else {
 lean::inc(x_55);
 lean::dec(x_42);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_55);
lean::cnstr_set_scalar(x_59, sizeof(void*)*1, x_57);
x_60 = x_59;
x_19 = x_60;
x_20 = x_39;
goto lbl_21;
}
}
else
{
obj* x_61; obj* x_64; uint8 x_66; obj* x_67; obj* x_68; obj* x_69; 
x_61 = lean::cnstr_get(x_25, 1);
lean::inc(x_61);
lean::dec(x_25);
x_64 = lean::cnstr_get(x_26, 0);
x_66 = lean::cnstr_get_scalar<uint8>(x_26, sizeof(void*)*1);
if (lean::is_exclusive(x_26)) {
 x_67 = x_26;
} else {
 lean::inc(x_64);
 lean::dec(x_26);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_64);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_66);
x_69 = x_68;
x_19 = x_69;
x_20 = x_61;
goto lbl_21;
}
lbl_21:
{
if (lean::obj_tag(x_19) == 0)
{
obj* x_73; obj* x_74; 
lean::dec(x_18);
lean::dec(x_12);
lean::dec(x_16);
x_73 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_19);
if (lean::is_scalar(x_11)) {
 x_74 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_74 = x_11;
}
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_20);
return x_74;
}
else
{
obj* x_75; uint8 x_77; obj* x_78; obj* x_79; 
x_75 = lean::cnstr_get(x_19, 0);
lean::inc(x_75);
x_77 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
if (x_77 == 0)
{
obj* x_82; obj* x_83; obj* x_85; obj* x_86; 
lean::dec(x_19);
x_82 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__3;
x_83 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__4;
lean::inc(x_12);
x_85 = l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3(x_82, x_83, x_1, x_12, x_20);
x_86 = lean::cnstr_get(x_85, 0);
lean::inc(x_86);
if (lean::obj_tag(x_86) == 0)
{
obj* x_88; obj* x_91; obj* x_93; obj* x_96; obj* x_98; obj* x_99; 
x_88 = lean::cnstr_get(x_85, 1);
lean::inc(x_88);
lean::dec(x_85);
x_91 = lean::cnstr_get(x_86, 1);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_86, 2);
lean::inc(x_93);
lean::dec(x_86);
x_96 = l___private_init_lean_parser_token_2__whitespaceAux___main___closed__1;
lean::inc(x_91);
x_98 = l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__4(x_1, x_96, x_91, x_88);
x_99 = lean::cnstr_get(x_98, 0);
lean::inc(x_99);
if (lean::obj_tag(x_99) == 0)
{
obj* x_101; uint8 x_103; 
x_101 = lean::cnstr_get(x_99, 0);
lean::inc(x_101);
x_103 = lean::unbox(x_101);
if (x_103 == 0)
{
obj* x_104; obj* x_107; obj* x_109; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_119; obj* x_121; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
x_104 = lean::cnstr_get(x_98, 1);
lean::inc(x_104);
lean::dec(x_98);
x_107 = lean::cnstr_get(x_99, 1);
lean::inc(x_107);
x_109 = lean::cnstr_get(x_99, 2);
lean::inc(x_109);
lean::dec(x_99);
x_112 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_112, 0, x_91);
x_113 = lean::box(0);
x_114 = l___private_init_lean_parser_token_2__whitespaceAux___main___closed__2;
x_115 = l_mjoin___rarg___closed__1;
x_116 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_114, x_115, x_112, x_113, x_1, x_107, x_104);
lean::dec(x_107);
lean::dec(x_112);
x_119 = lean::cnstr_get(x_116, 0);
lean::inc(x_119);
x_121 = lean::cnstr_get(x_116, 1);
lean::inc(x_121);
lean::dec(x_116);
x_124 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_109, x_119);
x_125 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_126 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_125, x_124);
x_127 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_93, x_126);
x_128 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_127);
x_78 = x_128;
x_79 = x_121;
goto lbl_80;
}
else
{
obj* x_130; obj* x_133; obj* x_135; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; 
lean::dec(x_91);
x_130 = lean::cnstr_get(x_98, 1);
lean::inc(x_130);
lean::dec(x_98);
x_133 = lean::cnstr_get(x_99, 1);
x_135 = lean::cnstr_get(x_99, 2);
if (lean::is_exclusive(x_99)) {
 lean::cnstr_release(x_99, 0);
 x_137 = x_99;
} else {
 lean::inc(x_133);
 lean::inc(x_135);
 lean::dec(x_99);
 x_137 = lean::box(0);
}
x_138 = lean::box(0);
x_139 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_137)) {
 x_140 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_140 = x_137;
}
lean::cnstr_set(x_140, 0, x_138);
lean::cnstr_set(x_140, 1, x_133);
lean::cnstr_set(x_140, 2, x_139);
x_141 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_135, x_140);
x_142 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_139, x_141);
x_143 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_93, x_142);
x_144 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_143);
x_78 = x_144;
x_79 = x_130;
goto lbl_80;
}
}
else
{
obj* x_146; obj* x_149; uint8 x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
lean::dec(x_91);
x_146 = lean::cnstr_get(x_98, 1);
lean::inc(x_146);
lean::dec(x_98);
x_149 = lean::cnstr_get(x_99, 0);
x_151 = lean::cnstr_get_scalar<uint8>(x_99, sizeof(void*)*1);
if (lean::is_exclusive(x_99)) {
 x_152 = x_99;
} else {
 lean::inc(x_149);
 lean::dec(x_99);
 x_152 = lean::box(0);
}
if (lean::is_scalar(x_152)) {
 x_153 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_153 = x_152;
}
lean::cnstr_set(x_153, 0, x_149);
lean::cnstr_set_scalar(x_153, sizeof(void*)*1, x_151);
x_154 = x_153;
x_155 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_156 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_155, x_154);
x_157 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_93, x_156);
x_158 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_157);
x_78 = x_158;
x_79 = x_146;
goto lbl_80;
}
}
else
{
obj* x_159; obj* x_162; obj* x_164; uint8 x_165; obj* x_166; obj* x_167; 
x_159 = lean::cnstr_get(x_85, 1);
lean::inc(x_159);
lean::dec(x_85);
x_162 = lean::cnstr_get(x_86, 0);
if (lean::is_exclusive(x_86)) {
 x_164 = x_86;
} else {
 lean::inc(x_162);
 lean::dec(x_86);
 x_164 = lean::box(0);
}
x_165 = 0;
if (lean::is_scalar(x_164)) {
 x_166 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_166 = x_164;
}
lean::cnstr_set(x_166, 0, x_162);
lean::cnstr_set_scalar(x_166, sizeof(void*)*1, x_165);
x_167 = x_166;
x_78 = x_167;
x_79 = x_159;
goto lbl_80;
}
}
else
{
obj* x_173; obj* x_174; 
lean::dec(x_18);
lean::dec(x_11);
lean::dec(x_12);
lean::dec(x_16);
lean::dec(x_75);
x_173 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_19);
x_174 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_174, 0, x_173);
lean::cnstr_set(x_174, 1, x_20);
return x_174;
}
lbl_80:
{
if (lean::obj_tag(x_78) == 0)
{
obj* x_177; obj* x_179; obj* x_181; obj* x_182; obj* x_183; obj* x_185; obj* x_187; obj* x_188; 
lean::dec(x_11);
lean::dec(x_16);
x_177 = lean::cnstr_get(x_78, 1);
x_179 = lean::cnstr_get(x_78, 2);
if (lean::is_exclusive(x_78)) {
 lean::cnstr_release(x_78, 0);
 lean::cnstr_set(x_78, 1, lean::box(0));
 lean::cnstr_set(x_78, 2, lean::box(0));
 x_181 = x_78;
} else {
 lean::inc(x_177);
 lean::inc(x_179);
 lean::dec(x_78);
 x_181 = lean::box(0);
}
x_182 = l_Lean_Parser_finishCommentBlock(x_17, x_1, x_177, x_79);
x_183 = lean::cnstr_get(x_182, 0);
x_185 = lean::cnstr_get(x_182, 1);
if (lean::is_exclusive(x_182)) {
 lean::cnstr_set(x_182, 0, lean::box(0));
 lean::cnstr_set(x_182, 1, lean::box(0));
 x_187 = x_182;
} else {
 lean::inc(x_183);
 lean::inc(x_185);
 lean::dec(x_182);
 x_187 = lean::box(0);
}
x_188 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_179, x_183);
if (lean::obj_tag(x_188) == 0)
{
obj* x_191; obj* x_193; obj* x_195; obj* x_196; obj* x_198; obj* x_200; obj* x_202; obj* x_203; 
lean::dec(x_187);
lean::dec(x_181);
x_191 = lean::cnstr_get(x_188, 1);
x_193 = lean::cnstr_get(x_188, 2);
if (lean::is_exclusive(x_188)) {
 lean::cnstr_release(x_188, 0);
 lean::cnstr_set(x_188, 1, lean::box(0));
 lean::cnstr_set(x_188, 2, lean::box(0));
 x_195 = x_188;
} else {
 lean::inc(x_191);
 lean::inc(x_193);
 lean::dec(x_188);
 x_195 = lean::box(0);
}
x_196 = l___private_init_lean_parser_token_2__whitespaceAux___main(x_18, x_1, x_191, x_185);
lean::dec(x_18);
x_198 = lean::cnstr_get(x_196, 0);
x_200 = lean::cnstr_get(x_196, 1);
if (lean::is_exclusive(x_196)) {
 lean::cnstr_set(x_196, 0, lean::box(0));
 lean::cnstr_set(x_196, 1, lean::box(0));
 x_202 = x_196;
} else {
 lean::inc(x_198);
 lean::inc(x_200);
 lean::dec(x_196);
 x_202 = lean::box(0);
}
x_203 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_193, x_198);
if (lean::obj_tag(x_203) == 0)
{
obj* x_206; obj* x_207; obj* x_208; 
lean::dec(x_195);
lean::dec(x_12);
x_206 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_75, x_203);
x_207 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_206);
if (lean::is_scalar(x_202)) {
 x_208 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_208 = x_202;
}
lean::cnstr_set(x_208, 0, x_207);
lean::cnstr_set(x_208, 1, x_200);
return x_208;
}
else
{
uint8 x_209; 
x_209 = lean::cnstr_get_scalar<uint8>(x_203, sizeof(void*)*1);
if (x_209 == 0)
{
obj* x_210; obj* x_213; obj* x_216; obj* x_217; obj* x_218; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; 
x_210 = lean::cnstr_get(x_203, 0);
lean::inc(x_210);
lean::dec(x_203);
x_213 = lean::cnstr_get(x_210, 2);
lean::inc(x_213);
lean::dec(x_210);
x_216 = l_mjoin___rarg___closed__1;
x_217 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_217, 0, x_213);
lean::closure_set(x_217, 1, x_216);
x_218 = lean::cnstr_get(x_75, 2);
lean::inc(x_218);
lean::dec(x_75);
x_221 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_221, 0, x_218);
lean::closure_set(x_221, 1, x_217);
x_222 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_222, 0, x_221);
x_223 = lean::box(0);
if (lean::is_scalar(x_195)) {
 x_224 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_224 = x_195;
}
lean::cnstr_set(x_224, 0, x_223);
lean::cnstr_set(x_224, 1, x_12);
lean::cnstr_set(x_224, 2, x_222);
x_225 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_224);
if (lean::is_scalar(x_202)) {
 x_226 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_226 = x_202;
}
lean::cnstr_set(x_226, 0, x_225);
lean::cnstr_set(x_226, 1, x_200);
return x_226;
}
else
{
obj* x_229; obj* x_230; obj* x_231; 
lean::dec(x_195);
lean::dec(x_12);
x_229 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_75, x_203);
x_230 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_229);
if (lean::is_scalar(x_202)) {
 x_231 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_231 = x_202;
}
lean::cnstr_set(x_231, 0, x_230);
lean::cnstr_set(x_231, 1, x_200);
return x_231;
}
}
}
else
{
uint8 x_233; 
lean::dec(x_18);
x_233 = lean::cnstr_get_scalar<uint8>(x_188, sizeof(void*)*1);
if (x_233 == 0)
{
obj* x_234; obj* x_237; obj* x_240; obj* x_241; obj* x_242; obj* x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_250; 
x_234 = lean::cnstr_get(x_188, 0);
lean::inc(x_234);
lean::dec(x_188);
x_237 = lean::cnstr_get(x_234, 2);
lean::inc(x_237);
lean::dec(x_234);
x_240 = l_mjoin___rarg___closed__1;
x_241 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_241, 0, x_237);
lean::closure_set(x_241, 1, x_240);
x_242 = lean::cnstr_get(x_75, 2);
lean::inc(x_242);
lean::dec(x_75);
x_245 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_245, 0, x_242);
lean::closure_set(x_245, 1, x_241);
x_246 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_246, 0, x_245);
x_247 = lean::box(0);
if (lean::is_scalar(x_181)) {
 x_248 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_248 = x_181;
}
lean::cnstr_set(x_248, 0, x_247);
lean::cnstr_set(x_248, 1, x_12);
lean::cnstr_set(x_248, 2, x_246);
x_249 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_248);
if (lean::is_scalar(x_187)) {
 x_250 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_250 = x_187;
}
lean::cnstr_set(x_250, 0, x_249);
lean::cnstr_set(x_250, 1, x_185);
return x_250;
}
else
{
obj* x_253; obj* x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; obj* x_260; 
lean::dec(x_181);
lean::dec(x_12);
x_253 = lean::cnstr_get(x_188, 0);
if (lean::is_exclusive(x_188)) {
 x_255 = x_188;
} else {
 lean::inc(x_253);
 lean::dec(x_188);
 x_255 = lean::box(0);
}
if (lean::is_scalar(x_255)) {
 x_256 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_256 = x_255;
}
lean::cnstr_set(x_256, 0, x_253);
lean::cnstr_set_scalar(x_256, sizeof(void*)*1, x_233);
x_257 = x_256;
x_258 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_75, x_257);
x_259 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_258);
if (lean::is_scalar(x_187)) {
 x_260 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_260 = x_187;
}
lean::cnstr_set(x_260, 0, x_259);
lean::cnstr_set(x_260, 1, x_185);
return x_260;
}
}
}
else
{
uint8 x_262; 
lean::dec(x_18);
x_262 = lean::cnstr_get_scalar<uint8>(x_78, sizeof(void*)*1);
if (x_262 == 0)
{
obj* x_263; obj* x_266; obj* x_269; obj* x_270; obj* x_271; obj* x_274; obj* x_275; obj* x_276; obj* x_277; obj* x_278; obj* x_279; 
x_263 = lean::cnstr_get(x_78, 0);
lean::inc(x_263);
lean::dec(x_78);
x_266 = lean::cnstr_get(x_263, 2);
lean::inc(x_266);
lean::dec(x_263);
x_269 = l_mjoin___rarg___closed__1;
x_270 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_270, 0, x_266);
lean::closure_set(x_270, 1, x_269);
x_271 = lean::cnstr_get(x_75, 2);
lean::inc(x_271);
lean::dec(x_75);
x_274 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_274, 0, x_271);
lean::closure_set(x_274, 1, x_270);
x_275 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_275, 0, x_274);
x_276 = lean::box(0);
if (lean::is_scalar(x_16)) {
 x_277 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_277 = x_16;
}
lean::cnstr_set(x_277, 0, x_276);
lean::cnstr_set(x_277, 1, x_12);
lean::cnstr_set(x_277, 2, x_275);
x_278 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_277);
if (lean::is_scalar(x_11)) {
 x_279 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_279 = x_11;
}
lean::cnstr_set(x_279, 0, x_278);
lean::cnstr_set(x_279, 1, x_79);
return x_279;
}
else
{
obj* x_282; obj* x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; 
lean::dec(x_12);
lean::dec(x_16);
x_282 = lean::cnstr_get(x_78, 0);
if (lean::is_exclusive(x_78)) {
 x_284 = x_78;
} else {
 lean::inc(x_282);
 lean::dec(x_78);
 x_284 = lean::box(0);
}
if (lean::is_scalar(x_284)) {
 x_285 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_285 = x_284;
}
lean::cnstr_set(x_285, 0, x_282);
lean::cnstr_set_scalar(x_285, sizeof(void*)*1, x_262);
x_286 = x_285;
x_287 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_75, x_286);
x_288 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_287);
if (lean::is_scalar(x_11)) {
 x_289 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_289 = x_11;
}
lean::cnstr_set(x_289, 0, x_288);
lean::cnstr_set(x_289, 1, x_79);
return x_289;
}
}
}
}
}
}
else
{
obj* x_290; obj* x_292; obj* x_293; uint8 x_295; obj* x_296; obj* x_297; obj* x_298; obj* x_299; 
x_290 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_292 = x_6;
} else {
 lean::inc(x_290);
 lean::dec(x_6);
 x_292 = lean::box(0);
}
x_293 = lean::cnstr_get(x_7, 0);
x_295 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_296 = x_7;
} else {
 lean::inc(x_293);
 lean::dec(x_7);
 x_296 = lean::box(0);
}
if (lean::is_scalar(x_296)) {
 x_297 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_297 = x_296;
}
lean::cnstr_set(x_297, 0, x_293);
lean::cnstr_set_scalar(x_297, sizeof(void*)*1, x_295);
x_298 = x_297;
if (lean::is_scalar(x_292)) {
 x_299 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_299 = x_292;
}
lean::cnstr_set(x_299, 0, x_298);
lean::cnstr_set(x_299, 1, x_290);
return x_299;
}
}
else
{
obj* x_300; obj* x_301; obj* x_302; obj* x_303; 
x_300 = lean::box(0);
x_301 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
x_302 = l_mjoin___rarg___closed__1;
x_303 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_301, x_302, x_300, x_300, x_1, x_2, x_3);
lean::dec(x_2);
return x_303;
}
}
}
obj* l___private_init_lean_parser_parsec_7__takeWhileAux_x_27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l___private_init_lean_parser_parsec_7__takeWhileAux_x_27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__3(x_0, x_3, x_2);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_takeWhile_x_27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_whitespace___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_whitespace___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l___private_init_lean_parser_parsec_7__takeWhileAux_x_27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; obj* x_4; 
x_3 = lean::unbox(x_1);
x_4 = l___private_init_lean_parser_parsec_7__takeWhileAux_x_27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__6(x_0, x_3, x_2);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile_x_27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__5___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_takeWhile_x_27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__5(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_token_2__whitespaceAux___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_token_2__whitespaceAux___main(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_parser_token_2__whitespaceAux(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_token_2__whitespaceAux___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_parser_token_2__whitespaceAux___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_token_2__whitespaceAux(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_whitespace(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_3 = l_String_OldIterator_remaining___main(x_1);
x_4 = lean::mk_nat_obj(1u);
x_5 = lean::nat_add(x_3, x_4);
lean::dec(x_3);
x_7 = l___private_init_lean_parser_token_2__whitespaceAux___main(x_5, x_0, x_1, x_2);
lean::dec(x_5);
x_9 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 x_13 = x_7;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_9);
x_16 = l_mjoin___rarg___closed__1;
x_17 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_15, x_16);
if (lean::is_scalar(x_13)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_13;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_11);
return x_18;
}
}
obj* l_Lean_Parser_whitespace___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_whitespace(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Parser_asSubstring___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_2);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* l_Lean_Parser_asSubstring___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_asSubstring___rarg___lambda__1), 3, 2);
lean::closure_set(x_5, 0, x_0);
lean::closure_set(x_5, 1, x_1);
x_6 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_3, x_5);
return x_6;
}
}
obj* l_Lean_Parser_asSubstring___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_asSubstring___rarg___lambda__2___boxed), 5, 4);
lean::closure_set(x_6, 0, x_0);
lean::closure_set(x_6, 1, x_4);
lean::closure_set(x_6, 2, x_1);
lean::closure_set(x_6, 3, x_2);
x_7 = lean::apply_4(x_1, lean::box(0), lean::box(0), x_3, x_6);
return x_7;
}
}
obj* l_Lean_Parser_asSubstring___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; obj* x_13; obj* x_14; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
lean::dec(x_1);
x_9 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
lean::inc(x_10);
lean::inc(x_4);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_asSubstring___rarg___lambda__3), 5, 4);
lean::closure_set(x_13, 0, x_0);
lean::closure_set(x_13, 1, x_4);
lean::closure_set(x_13, 2, x_10);
lean::closure_set(x_13, 3, x_3);
x_14 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_10, x_13);
return x_14;
}
}
obj* l_Lean_Parser_asSubstring(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_asSubstring___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_Lean_Parser_asSubstring___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_asSubstring___rarg___lambda__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_asSubstring___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_asSubstring___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_asSubstring___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_asSubstring(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_token_3__updateTrailing___main(obj* x_0, obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; obj* x_4; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
lean::dec(x_2);
lean::dec(x_0);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_8 = x_1;
} else {
 lean::dec(x_1);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_11 = x_2;
} else {
 lean::inc(x_9);
 lean::dec(x_2);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_4, 0);
if (lean::is_exclusive(x_4)) {
 x_14 = x_4;
} else {
 lean::inc(x_12);
 lean::dec(x_4);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::dec(x_12);
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_15);
lean::cnstr_set(x_20, 1, x_17);
lean::cnstr_set(x_20, 2, x_0);
if (lean::is_scalar(x_14)) {
 x_21 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_21 = x_14;
}
lean::cnstr_set(x_21, 0, x_20);
if (lean::is_scalar(x_11)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_11;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_9);
if (lean::is_scalar(x_8)) {
 x_23 = lean::alloc_cnstr(0, 1, 0);
} else {
 x_23 = x_8;
}
lean::cnstr_set(x_23, 0, x_22);
return x_23;
}
}
case 1:
{
obj* x_24; obj* x_26; 
x_24 = lean::cnstr_get(x_1, 0);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_24, 0);
lean::inc(x_26);
if (lean::obj_tag(x_26) == 0)
{
lean::dec(x_0);
lean::dec(x_24);
return x_1;
}
else
{
obj* x_30; obj* x_31; obj* x_33; obj* x_35; obj* x_37; obj* x_39; obj* x_40; obj* x_42; obj* x_43; obj* x_45; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 0);
 x_30 = x_1;
} else {
 lean::dec(x_1);
 x_30 = lean::box(0);
}
x_31 = lean::cnstr_get(x_24, 1);
x_33 = lean::cnstr_get(x_24, 2);
x_35 = lean::cnstr_get(x_24, 3);
x_37 = lean::cnstr_get(x_24, 4);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_release(x_24, 0);
 x_39 = x_24;
} else {
 lean::inc(x_31);
 lean::inc(x_33);
 lean::inc(x_35);
 lean::inc(x_37);
 lean::dec(x_24);
 x_39 = lean::box(0);
}
x_40 = lean::cnstr_get(x_26, 0);
if (lean::is_exclusive(x_26)) {
 x_42 = x_26;
} else {
 lean::inc(x_40);
 lean::dec(x_26);
 x_42 = lean::box(0);
}
x_43 = lean::cnstr_get(x_40, 0);
lean::inc(x_43);
x_45 = lean::cnstr_get(x_40, 1);
lean::inc(x_45);
lean::dec(x_40);
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_43);
lean::cnstr_set(x_48, 1, x_45);
lean::cnstr_set(x_48, 2, x_0);
if (lean::is_scalar(x_42)) {
 x_49 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_49 = x_42;
}
lean::cnstr_set(x_49, 0, x_48);
if (lean::is_scalar(x_39)) {
 x_50 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_50 = x_39;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_31);
lean::cnstr_set(x_50, 2, x_33);
lean::cnstr_set(x_50, 3, x_35);
lean::cnstr_set(x_50, 4, x_37);
if (lean::is_scalar(x_30)) {
 x_51 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_51 = x_30;
}
lean::cnstr_set(x_51, 0, x_50);
return x_51;
}
}
case 2:
{
obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_59; obj* x_60; obj* x_63; obj* x_64; 
x_52 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_54 = x_1;
} else {
 lean::inc(x_52);
 lean::dec(x_1);
 x_54 = lean::box(0);
}
x_55 = lean::cnstr_get(x_52, 0);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_52, 1);
lean::inc(x_57);
x_59 = l___private_init_lean_parser_token_3__updateTrailingLst___main(x_0, x_57);
x_60 = lean::cnstr_get(x_52, 2);
lean::inc(x_60);
lean::dec(x_52);
x_63 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_63, 0, x_55);
lean::cnstr_set(x_63, 1, x_59);
lean::cnstr_set(x_63, 2, x_60);
if (lean::is_scalar(x_54)) {
 x_64 = lean::alloc_cnstr(2, 1, 0);
} else {
 x_64 = x_54;
}
lean::cnstr_set(x_64, 0, x_63);
return x_64;
}
default:
{
lean::dec(x_0);
return x_1;
}
}
}
}
obj* l___private_init_lean_parser_token_3__updateTrailingLst___main(obj* x_0, obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
lean::dec(x_0);
return x_1;
}
else
{
obj* x_3; 
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
obj* x_5; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_release(x_1, 1);
 x_7 = x_1;
} else {
 lean::inc(x_5);
 lean::dec(x_1);
 x_7 = lean::box(0);
}
x_8 = l___private_init_lean_parser_token_3__updateTrailing___main(x_0, x_5);
if (lean::is_scalar(x_7)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_7;
}
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
else
{
obj* x_10; obj* x_14; obj* x_15; obj* x_16; 
x_10 = lean::cnstr_get(x_1, 0);
lean::inc(x_10);
lean::dec(x_1);
lean::inc(x_3);
x_14 = l___private_init_lean_parser_token_3__updateTrailingLst___main(x_0, x_3);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_15 = x_3;
} else {
 lean::dec(x_3);
 x_15 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_10);
lean::cnstr_set(x_16, 1, x_14);
return x_16;
}
}
}
}
obj* l___private_init_lean_parser_token_3__updateTrailing(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_parser_token_3__updateTrailing___main(x_0, x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_token_3__updateTrailingLst(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_parser_token_3__updateTrailingLst___main(x_0, x_1);
return x_2;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::apply_2(x_0, x_2, x_3);
return x_4;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_2);
x_6 = lean::apply_3(x_0, x_2, x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_12; obj* x_14; obj* x_16; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_12 = lean::cnstr_get(x_7, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_7, 1);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_7, 2);
lean::inc(x_16);
lean::dec(x_7);
x_19 = lean::apply_4(x_1, x_12, x_2, x_14, x_9);
x_20 = lean::cnstr_get(x_19, 0);
x_22 = lean::cnstr_get(x_19, 1);
if (lean::is_exclusive(x_19)) {
 x_24 = x_19;
} else {
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_19);
 x_24 = lean::box(0);
}
x_25 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_20);
if (lean::is_scalar(x_24)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_24;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_22);
return x_26;
}
else
{
obj* x_29; obj* x_31; obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_1);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_31 = x_6;
} else {
 lean::inc(x_29);
 lean::dec(x_6);
 x_31 = lean::box(0);
}
x_32 = lean::cnstr_get(x_7, 0);
x_34 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_35 = x_7;
} else {
 lean::inc(x_32);
 lean::dec(x_7);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_34);
x_37 = x_36;
if (lean::is_scalar(x_31)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_31;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_29);
return x_38;
}
}
}
obj* l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_withTrailing___rarg___lambda__1(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_4; obj* x_5; 
x_2 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_0);
lean::cnstr_set(x_4, 2, x_2);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_Parser_withTrailing___rarg___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Parser_whitespace(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 1);
x_12 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_14 = x_5;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
lean::inc(x_10);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_0);
lean::cnstr_set(x_16, 1, x_10);
x_17 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_14)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_14;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_10);
lean::cnstr_set(x_18, 2, x_17);
x_19 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_18);
if (lean::is_scalar(x_9)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_9;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_7);
return x_20;
}
else
{
obj* x_22; obj* x_24; obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_0);
x_22 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_24 = x_4;
} else {
 lean::inc(x_22);
 lean::dec(x_4);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_5, 0);
x_27 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_28 = x_5;
} else {
 lean::inc(x_25);
 lean::dec(x_5);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_27);
x_30 = x_29;
if (lean::is_scalar(x_24)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_24;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_22);
return x_31;
}
}
}
obj* l_Lean_Parser_withTrailing___rarg___lambda__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_6; obj* x_9; obj* x_10; 
x_3 = lean::cnstr_get(x_0, 0);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
x_9 = l___private_init_lean_parser_token_3__updateTrailing___main(x_2, x_1);
x_10 = lean::apply_2(x_6, lean::box(0), x_9);
return x_10;
}
}
obj* _init_l_Lean_Parser_withTrailing___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__2___boxed), 4, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_withTrailing___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::cnstr_get(x_0, 1);
lean::inc(x_4);
x_6 = l_Lean_Parser_withTrailing___rarg___closed__1;
x_7 = lean::apply_2(x_2, lean::box(0), x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__3), 3, 2);
lean::closure_set(x_8, 0, x_0);
lean::closure_set(x_8, 1, x_3);
x_9 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_withTrailing(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_withTrailing___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_withTrailing___rarg___lambda__2(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_withTrailing___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_withTrailing___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_withTrailing___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_withTrailing(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_mkRawRes(obj* x_0, obj* x_1) {
_start:
{
obj* x_4; obj* x_7; obj* x_8; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; 
lean::inc(x_1);
lean::inc(x_0);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_0);
lean::cnstr_set(x_4, 1, x_1);
lean::inc(x_0);
lean::inc(x_0);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_0);
x_8 = lean::cnstr_get(x_0, 1);
lean::inc(x_8);
lean::dec(x_0);
lean::inc(x_1);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_1);
lean::cnstr_set(x_12, 1, x_1);
x_13 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_13, 0, x_7);
lean::cnstr_set(x_13, 1, x_8);
lean::cnstr_set(x_13, 2, x_12);
x_14 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_14, 0, x_13);
x_15 = l_Lean_Parser_Substring_toString(x_4);
lean::dec(x_4);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_14);
lean::cnstr_set(x_17, 1, x_15);
x_18 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
return x_18;
}
}
obj* l_Lean_Parser_raw___rarg___lambda__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_mkRawRes(x_0, x_5);
if (x_1 == 0)
{
obj* x_8; obj* x_11; obj* x_14; 
lean::dec(x_4);
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::apply_2(x_11, lean::box(0), x_6);
return x_14;
}
else
{
obj* x_15; 
x_15 = l_Lean_Parser_withTrailing___rarg(x_2, x_3, x_4, x_6);
return x_15;
}
}
}
obj* l_Lean_Parser_raw___rarg___lambda__2(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::box(x_1);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_raw___rarg___lambda__1___boxed), 6, 5);
lean::closure_set(x_9, 0, x_0);
lean::closure_set(x_9, 1, x_8);
lean::closure_set(x_9, 2, x_2);
lean::closure_set(x_9, 3, x_3);
lean::closure_set(x_9, 4, x_4);
x_10 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_6, x_9);
return x_10;
}
}
obj* l_Lean_Parser_raw___rarg___lambda__3(uint8 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_10; obj* x_11; 
x_8 = lean::box(x_0);
lean::inc(x_4);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_raw___rarg___lambda__2___boxed), 8, 7);
lean::closure_set(x_10, 0, x_7);
lean::closure_set(x_10, 1, x_8);
lean::closure_set(x_10, 2, x_1);
lean::closure_set(x_10, 3, x_2);
lean::closure_set(x_10, 4, x_3);
lean::closure_set(x_10, 5, x_4);
lean::closure_set(x_10, 6, x_5);
x_11 = lean::apply_4(x_4, lean::box(0), lean::box(0), x_6, x_10);
return x_11;
}
}
obj* l_Lean_Parser_raw___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint8 x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_15; obj* x_16; 
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 0);
lean::inc(x_8);
x_10 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_11 = lean::apply_2(x_8, lean::box(0), x_10);
x_12 = lean::box(x_5);
lean::inc(x_11);
lean::inc(x_6);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_raw___rarg___lambda__3___boxed), 8, 7);
lean::closure_set(x_15, 0, x_12);
lean::closure_set(x_15, 1, x_0);
lean::closure_set(x_15, 2, x_1);
lean::closure_set(x_15, 3, x_2);
lean::closure_set(x_15, 4, x_6);
lean::closure_set(x_15, 5, x_11);
lean::closure_set(x_15, 6, x_4);
x_16 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_11, x_15);
return x_16;
}
}
obj* l_Lean_Parser_raw(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_raw___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_Lean_Parser_raw___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_1);
x_7 = l_Lean_Parser_raw___rarg___lambda__1(x_0, x_6, x_2, x_3, x_4, x_5);
lean::dec(x_3);
return x_7;
}
}
obj* l_Lean_Parser_raw___rarg___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_1);
x_9 = l_Lean_Parser_raw___rarg___lambda__2(x_0, x_8, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_7);
return x_9;
}
}
obj* l_Lean_Parser_raw___rarg___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_0);
x_9 = l_Lean_Parser_raw___rarg___lambda__3(x_8, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
obj* l_Lean_Parser_raw___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_5);
x_7 = l_Lean_Parser_raw___rarg(x_0, x_1, x_2, x_3, x_4, x_6);
lean::dec(x_3);
return x_7;
}
}
obj* l_Lean_Parser_raw___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_raw(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_raw_tokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, uint8 x_6) {
_start:
{
obj* x_7; 
x_7 = lean::box(0);
return x_7;
}
}
obj* l_Lean_Parser_raw_tokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_6);
x_8 = l_Lean_Parser_raw_tokens(x_0, x_1, x_2, x_3, x_4, x_5, x_7);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
lean::dec(x_5);
return x_8;
}
}
obj* l_Lean_Parser_raw_view___rarg___lambda__1(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_1; obj* x_4; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_1);
return x_4;
}
case 3:
{
obj* x_5; 
x_5 = lean::box(0);
return x_5;
}
default:
{
obj* x_7; 
lean::dec(x_0);
x_7 = lean::box(0);
return x_7;
}
}
}
}
obj* _init_l_Lean_Parser_raw_view___rarg___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = l_Option_getOrElse___main___rarg(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Parser_raw_view___rarg___lambda__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_2 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_4 = x_0;
} else {
 lean::inc(x_2);
 lean::dec(x_0);
 x_4 = lean::box(0);
}
x_5 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_5, 0, x_2);
if (lean::is_scalar(x_4)) {
 x_6 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_6 = x_4;
}
lean::cnstr_set(x_6, 0, x_5);
x_7 = lean::box(3);
x_8 = l_Option_getOrElse___main___rarg(x_6, x_7);
lean::dec(x_6);
return x_8;
}
}
}
obj* _init_l_Lean_Parser_raw_view___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_raw_view___rarg___lambda__1), 1, 0);
return x_0;
}
}
obj* _init_l_Lean_Parser_raw_view___rarg___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_raw_view___rarg___lambda__2), 1, 0);
return x_0;
}
}
obj* l_Lean_Parser_raw_view___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint8 x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = l_Lean_Parser_raw_view___rarg___closed__1;
x_7 = l_Lean_Parser_raw_view___rarg___closed__2;
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_Lean_Parser_raw_view(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_raw_view___rarg___boxed), 6, 0);
return x_1;
}
}
obj* l_Lean_Parser_raw_view___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_5);
x_7 = l_Lean_Parser_raw_view___rarg(x_0, x_1, x_2, x_3, x_4, x_6);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_7;
}
}
obj* l_Lean_Parser_raw_view___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_raw_view(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_rawStr_Lean_Parser_HasTokens(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint8 x_5) {
_start:
{
obj* x_6; 
x_6 = lean::box(0);
return x_6;
}
}
obj* l_Lean_Parser_rawStr_Lean_Parser_HasTokens___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_5);
x_7 = l_Lean_Parser_rawStr_Lean_Parser_HasTokens(x_0, x_1, x_2, x_3, x_4, x_6);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
lean::dec(x_4);
return x_7;
}
}
obj* l_Lean_Parser_rawStr_Lean_Parser_HasView___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, uint8 x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_10; obj* x_11; 
lean::inc(x_3);
x_6 = l_String_quote(x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
lean::inc(x_1);
lean::inc(x_0);
x_10 = l_Lean_Parser_MonadParsec_strCore___rarg(x_0, x_1, x_3, x_7);
x_11 = l_Lean_Parser_raw_view___rarg(x_0, x_1, x_2, lean::box(0), x_10, x_4);
lean::dec(x_10);
lean::dec(x_1);
lean::dec(x_0);
return x_11;
}
}
obj* l_Lean_Parser_rawStr_Lean_Parser_HasView(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_rawStr_Lean_Parser_HasView___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_rawStr_Lean_Parser_HasView___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_4);
x_6 = l_Lean_Parser_rawStr_Lean_Parser_HasView___rarg(x_0, x_1, x_2, x_3, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_rawStr_Lean_Parser_HasView___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_rawStr_Lean_Parser_HasView(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_rawStr___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, uint8 x_4) {
_start:
{
obj* x_6; obj* x_7; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_20; obj* x_21; 
lean::inc(x_3);
x_6 = l_String_quote(x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
lean::inc(x_1);
lean::inc(x_0);
x_10 = l_Lean_Parser_MonadParsec_strCore___rarg(x_0, x_1, x_3, x_7);
x_11 = lean::cnstr_get(x_0, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
x_15 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_16 = lean::apply_2(x_13, lean::box(0), x_15);
x_17 = lean::box(x_4);
lean::inc(x_16);
lean::inc(x_11);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_raw___rarg___lambda__3___boxed), 8, 7);
lean::closure_set(x_20, 0, x_17);
lean::closure_set(x_20, 1, x_0);
lean::closure_set(x_20, 2, x_1);
lean::closure_set(x_20, 3, x_2);
lean::closure_set(x_20, 4, x_11);
lean::closure_set(x_20, 5, x_16);
lean::closure_set(x_20, 6, x_10);
x_21 = lean::apply_4(x_11, lean::box(0), lean::box(0), x_16, x_20);
return x_21;
}
}
obj* l_Lean_Parser_rawStr(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_rawStr___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_rawStr___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_4);
x_6 = l_Lean_Parser_rawStr___rarg(x_0, x_1, x_2, x_3, x_5);
return x_6;
}
}
obj* l_Lean_Parser_rawStr___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_rawStr(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_rawStr_viewDefault___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, uint8 x_4) {
_start:
{
obj* x_5; 
x_5 = lean::box(0);
return x_5;
}
}
obj* l_Lean_Parser_rawStr_viewDefault(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_rawStr_viewDefault___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_rawStr_viewDefault___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; obj* x_6; 
x_5 = lean::unbox(x_4);
x_6 = l_Lean_Parser_rawStr_viewDefault___rarg(x_0, x_1, x_2, x_3, x_5);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_Parser_rawStr_viewDefault___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_rawStr_viewDefault(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_detailIdentPartEscaped() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("detailIdentPartEscaped");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_1, 0, x_0);
lean::cnstr_set(x_1, 1, x_0);
lean::cnstr_set(x_1, 2, x_0);
return x_1;
}
}
obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__1___closed__1;
return x_5;
}
else
{
obj* x_6; obj* x_9; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
if (lean::obj_tag(x_9) == 0)
{
obj* x_12; 
x_12 = lean::box(3);
x_1 = x_9;
x_2 = x_12;
goto lbl_3;
}
else
{
obj* x_13; obj* x_15; 
x_13 = lean::cnstr_get(x_9, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_9, 1);
lean::inc(x_15);
lean::dec(x_9);
x_1 = x_15;
x_2 = x_13;
goto lbl_3;
}
}
lbl_3:
{
obj* x_18; 
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_20; obj* x_23; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_23 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
x_18 = x_23;
goto lbl_19;
}
case 3:
{
obj* x_24; 
x_24 = lean::box(0);
x_18 = x_24;
goto lbl_19;
}
default:
{
obj* x_26; 
lean::dec(x_2);
x_26 = lean::box(0);
x_18 = x_26;
goto lbl_19;
}
}
lbl_19:
{
obj* x_27; obj* x_28; obj* x_30; obj* x_31; 
if (lean::obj_tag(x_1) == 0)
{
obj* x_33; 
x_33 = lean::box(3);
x_30 = x_1;
x_31 = x_33;
goto lbl_32;
}
else
{
obj* x_34; obj* x_36; 
x_34 = lean::cnstr_get(x_1, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_1, 1);
lean::inc(x_36);
lean::dec(x_1);
x_30 = x_36;
x_31 = x_34;
goto lbl_32;
}
lbl_29:
{
switch (lean::obj_tag(x_28)) {
case 0:
{
obj* x_39; obj* x_42; obj* x_43; 
x_39 = lean::cnstr_get(x_28, 0);
lean::inc(x_39);
lean::dec(x_28);
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_39);
x_43 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_43, 0, x_18);
lean::cnstr_set(x_43, 1, x_27);
lean::cnstr_set(x_43, 2, x_42);
return x_43;
}
case 3:
{
obj* x_44; obj* x_45; 
x_44 = lean::box(0);
x_45 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_45, 0, x_18);
lean::cnstr_set(x_45, 1, x_27);
lean::cnstr_set(x_45, 2, x_44);
return x_45;
}
default:
{
obj* x_47; obj* x_48; 
lean::dec(x_28);
x_47 = lean::box(0);
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_18);
lean::cnstr_set(x_48, 1, x_27);
lean::cnstr_set(x_48, 2, x_47);
return x_48;
}
}
}
lbl_32:
{
switch (lean::obj_tag(x_31)) {
case 0:
{
obj* x_49; obj* x_52; 
x_49 = lean::cnstr_get(x_31, 0);
lean::inc(x_49);
lean::dec(x_31);
x_52 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_52, 0, x_49);
if (lean::obj_tag(x_30) == 0)
{
obj* x_53; obj* x_54; 
x_53 = lean::box(0);
x_54 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_54, 0, x_18);
lean::cnstr_set(x_54, 1, x_52);
lean::cnstr_set(x_54, 2, x_53);
return x_54;
}
else
{
obj* x_55; 
x_55 = lean::cnstr_get(x_30, 0);
lean::inc(x_55);
lean::dec(x_30);
x_27 = x_52;
x_28 = x_55;
goto lbl_29;
}
}
case 3:
{
obj* x_58; 
x_58 = lean::box(0);
if (lean::obj_tag(x_30) == 0)
{
obj* x_59; 
x_59 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_59, 0, x_18);
lean::cnstr_set(x_59, 1, x_58);
lean::cnstr_set(x_59, 2, x_58);
return x_59;
}
else
{
obj* x_60; 
x_60 = lean::cnstr_get(x_30, 0);
lean::inc(x_60);
lean::dec(x_30);
x_27 = x_58;
x_28 = x_60;
goto lbl_29;
}
}
default:
{
obj* x_64; 
lean::dec(x_31);
x_64 = lean::box(0);
if (lean::obj_tag(x_30) == 0)
{
obj* x_65; 
x_65 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_65, 0, x_18);
lean::cnstr_set(x_65, 1, x_64);
lean::cnstr_set(x_65, 2, x_64);
return x_65;
}
else
{
obj* x_66; 
x_66 = lean::cnstr_get(x_30, 0);
lean::inc(x_66);
lean::dec(x_30);
x_27 = x_64;
x_28 = x_66;
goto lbl_29;
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = l_Option_getOrElse___main___rarg(x_1, x_2);
lean::inc(x_3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_0);
lean::inc(x_3);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_5);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_3);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_Lean_Parser_detailIdentPartEscaped;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = l_Option_getOrElse___main___rarg(x_1, x_2);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_0);
return x_4;
}
}
obj* _init_l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = l_Option_getOrElse___main___rarg(x_1, x_2);
lean::inc(x_3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_3);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_5; obj* x_8; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_0, 2);
lean::inc(x_5);
lean::dec(x_0);
x_8 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
if (lean::obj_tag(x_3) == 0)
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_9; 
x_9 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__1;
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_10 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_12 = x_5;
} else {
 lean::inc(x_10);
 lean::dec(x_5);
 x_12 = lean::box(0);
}
x_13 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_13, 0, x_10);
if (lean::is_scalar(x_12)) {
 x_14 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_14 = x_12;
}
lean::cnstr_set(x_14, 0, x_13);
x_15 = lean::box(3);
x_16 = l_Option_getOrElse___main___rarg(x_14, x_15);
lean::dec(x_14);
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_8);
x_19 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_20);
x_22 = l_Lean_Parser_detailIdentPartEscaped;
x_23 = l_Lean_Parser_Syntax_mkNode(x_22, x_21);
return x_23;
}
}
else
{
obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_24 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_26 = x_3;
} else {
 lean::inc(x_24);
 lean::dec(x_3);
 x_26 = lean::box(0);
}
x_27 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_27, 0, x_24);
if (lean::is_scalar(x_26)) {
 x_28 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_28 = x_26;
}
lean::cnstr_set(x_28, 0, x_27);
x_29 = lean::box(3);
x_30 = l_Option_getOrElse___main___rarg(x_28, x_29);
lean::dec(x_28);
if (lean::obj_tag(x_5) == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_32 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__2;
x_33 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_33, 0, x_30);
lean::cnstr_set(x_33, 1, x_32);
x_34 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_33);
x_36 = l_Lean_Parser_detailIdentPartEscaped;
x_37 = l_Lean_Parser_Syntax_mkNode(x_36, x_35);
return x_37;
}
else
{
obj* x_38; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_38 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_40 = x_5;
} else {
 lean::inc(x_38);
 lean::dec(x_5);
 x_40 = lean::box(0);
}
x_41 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_41, 0, x_38);
if (lean::is_scalar(x_40)) {
 x_42 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_42 = x_40;
}
lean::cnstr_set(x_42, 0, x_41);
x_43 = l_Option_getOrElse___main___rarg(x_42, x_29);
lean::dec(x_42);
x_45 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_8);
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_30);
lean::cnstr_set(x_46, 1, x_45);
x_47 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_46);
x_49 = l_Lean_Parser_detailIdentPartEscaped;
x_50 = l_Lean_Parser_Syntax_mkNode(x_49, x_48);
return x_50;
}
}
}
else
{
obj* x_51; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_51 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_53 = x_1;
} else {
 lean::inc(x_51);
 lean::dec(x_1);
 x_53 = lean::box(0);
}
x_54 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_54, 0, x_51);
if (lean::is_scalar(x_53)) {
 x_55 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_55 = x_53;
}
lean::cnstr_set(x_55, 0, x_54);
x_56 = lean::box(3);
x_57 = l_Option_getOrElse___main___rarg(x_55, x_56);
lean::dec(x_55);
if (lean::obj_tag(x_3) == 0)
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_59 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__3;
x_60 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_60, 0, x_57);
lean::cnstr_set(x_60, 1, x_59);
x_61 = l_Lean_Parser_detailIdentPartEscaped;
x_62 = l_Lean_Parser_Syntax_mkNode(x_61, x_60);
return x_62;
}
else
{
obj* x_63; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_63 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_65 = x_5;
} else {
 lean::inc(x_63);
 lean::dec(x_5);
 x_65 = lean::box(0);
}
x_66 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_66, 0, x_63);
if (lean::is_scalar(x_65)) {
 x_67 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_67 = x_65;
}
lean::cnstr_set(x_67, 0, x_66);
x_68 = l_Option_getOrElse___main___rarg(x_67, x_56);
lean::dec(x_67);
x_70 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_70, 0, x_68);
lean::cnstr_set(x_70, 1, x_8);
x_71 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_72 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_70);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_57);
lean::cnstr_set(x_73, 1, x_72);
x_74 = l_Lean_Parser_detailIdentPartEscaped;
x_75 = l_Lean_Parser_Syntax_mkNode(x_74, x_73);
return x_75;
}
}
else
{
obj* x_76; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_76 = lean::cnstr_get(x_3, 0);
if (lean::is_exclusive(x_3)) {
 x_78 = x_3;
} else {
 lean::inc(x_76);
 lean::dec(x_3);
 x_78 = lean::box(0);
}
x_79 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_79, 0, x_76);
if (lean::is_scalar(x_78)) {
 x_80 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_80 = x_78;
}
lean::cnstr_set(x_80, 0, x_79);
x_81 = l_Option_getOrElse___main___rarg(x_80, x_56);
lean::dec(x_80);
if (lean::obj_tag(x_5) == 0)
{
obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
x_83 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__2;
x_84 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_84, 0, x_81);
lean::cnstr_set(x_84, 1, x_83);
x_85 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_85, 0, x_57);
lean::cnstr_set(x_85, 1, x_84);
x_86 = l_Lean_Parser_detailIdentPartEscaped;
x_87 = l_Lean_Parser_Syntax_mkNode(x_86, x_85);
return x_87;
}
else
{
obj* x_88; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
x_88 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 x_90 = x_5;
} else {
 lean::inc(x_88);
 lean::dec(x_5);
 x_90 = lean::box(0);
}
x_91 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_91, 0, x_88);
if (lean::is_scalar(x_90)) {
 x_92 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_92 = x_90;
}
lean::cnstr_set(x_92, 0, x_91);
x_93 = l_Option_getOrElse___main___rarg(x_92, x_56);
lean::dec(x_92);
x_95 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_95, 0, x_93);
lean::cnstr_set(x_95, 1, x_8);
x_96 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_96, 0, x_81);
lean::cnstr_set(x_96, 1, x_95);
x_97 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_97, 0, x_57);
lean::cnstr_set(x_97, 1, x_96);
x_98 = l_Lean_Parser_detailIdentPartEscaped;
x_99 = l_Lean_Parser_Syntax_mkNode(x_98, x_97);
return x_99;
}
}
}
}
}
obj* _init_l_Lean_Parser_detailIdentPartEscaped_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_detailIdentPartEscaped_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_detailIdentPartEscaped_HasView_x_27;
return x_0;
}
}
obj* _init_l_Lean_Parser_detailIdentPart() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("detailIdentPart");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_detailIdentPartEscaped_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("detailIdentPart");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__2;
return x_2;
}
else
{
obj* x_3; obj* x_6; obj* x_8; obj* x_11; uint8 x_12; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__3;
x_12 = lean_name_dec_eq(x_6, x_11);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_8);
x_15 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__2;
return x_15;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__2;
return x_16;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_8, 1);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_19; obj* x_22; 
x_19 = lean::cnstr_get(x_8, 0);
lean::inc(x_19);
lean::dec(x_8);
x_22 = l_Lean_Parser_Syntax_asNode___main(x_19);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; 
x_23 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__2;
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; 
x_24 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_set(x_22, 0, lean::box(0));
 x_26 = x_22;
} else {
 lean::inc(x_24);
 lean::dec(x_22);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
switch (lean::obj_tag(x_27)) {
case 0:
{
obj* x_31; 
lean::dec(x_26);
lean::dec(x_24);
x_31 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__2;
return x_31;
}
case 1:
{
obj* x_35; 
lean::dec(x_26);
lean::dec(x_27);
lean::dec(x_24);
x_35 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__2;
return x_35;
}
default:
{
obj* x_36; obj* x_39; obj* x_41; obj* x_44; uint8 x_45; 
x_36 = lean::cnstr_get(x_24, 1);
lean::inc(x_36);
lean::dec(x_24);
x_39 = lean::cnstr_get(x_27, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_27, 1);
lean::inc(x_41);
lean::dec(x_27);
x_44 = lean::box(0);
x_45 = lean_name_dec_eq(x_39, x_44);
lean::dec(x_39);
if (x_45 == 0)
{
obj* x_50; 
lean::dec(x_26);
lean::dec(x_41);
lean::dec(x_36);
x_50 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__2;
return x_50;
}
else
{
if (lean::obj_tag(x_36) == 0)
{
obj* x_53; 
lean::dec(x_26);
lean::dec(x_41);
x_53 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__2;
return x_53;
}
else
{
obj* x_54; 
x_54 = lean::cnstr_get(x_36, 1);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; obj* x_59; uint8 x_60; 
x_56 = lean::cnstr_get(x_36, 0);
lean::inc(x_56);
lean::dec(x_36);
x_59 = lean::mk_nat_obj(0u);
x_60 = lean::nat_dec_eq(x_41, x_59);
lean::dec(x_41);
if (x_60 == 0)
{
switch (lean::obj_tag(x_56)) {
case 0:
{
obj* x_62; obj* x_65; obj* x_66; 
x_62 = lean::cnstr_get(x_56, 0);
lean::inc(x_62);
lean::dec(x_56);
if (lean::is_scalar(x_26)) {
 x_65 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_65 = x_26;
}
lean::cnstr_set(x_65, 0, x_62);
x_66 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_66, 0, x_65);
return x_66;
}
case 3:
{
obj* x_68; 
lean::dec(x_26);
x_68 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__1;
return x_68;
}
default:
{
obj* x_71; 
lean::dec(x_56);
lean::dec(x_26);
x_71 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__1;
return x_71;
}
}
}
else
{
obj* x_73; obj* x_74; obj* x_77; obj* x_78; 
lean::dec(x_26);
x_73 = l_Lean_Parser_detailIdentPartEscaped_HasView;
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
lean::dec(x_73);
x_77 = lean::apply_1(x_74, x_56);
x_78 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_78, 0, x_77);
return x_78;
}
}
else
{
obj* x_83; 
lean::dec(x_26);
lean::dec(x_41);
lean::dec(x_54);
lean::dec(x_36);
x_83 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__2;
return x_83;
}
}
}
}
}
}
}
else
{
obj* x_86; 
lean::dec(x_8);
lean::dec(x_17);
x_86 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__2;
return x_86;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(0u);
x_2 = lean_name_mk_numeral(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(1u);
x_3 = lean_name_mk_numeral(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean::box(3);
x_6 = l_Option_getOrElse___main___rarg(x_4, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_Lean_Parser_Syntax_mkNode(x_3, x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_0);
x_10 = l_Lean_Parser_detailIdentPart;
x_11 = l_Lean_Parser_Syntax_mkNode(x_10, x_9);
return x_11;
}
}
obj* _init_l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(1u);
x_2 = lean_name_mk_numeral(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
if (lean::obj_tag(x_0) == 0)
{
obj* x_2; obj* x_5; obj* x_6; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
x_5 = l_Lean_Parser_detailIdentPartEscaped_HasView;
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
x_9 = lean::apply_1(x_6, x_2);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_1);
x_11 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__1;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_1);
x_14 = l_Lean_Parser_detailIdentPart;
x_15 = l_Lean_Parser_Syntax_mkNode(x_14, x_13);
return x_15;
}
else
{
obj* x_16; 
x_16 = lean::cnstr_get(x_0, 0);
lean::inc(x_16);
lean::dec(x_0);
if (lean::obj_tag(x_16) == 0)
{
obj* x_19; 
x_19 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__2;
return x_19;
}
else
{
obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_20 = lean::cnstr_get(x_16, 0);
if (lean::is_exclusive(x_16)) {
 x_22 = x_16;
} else {
 lean::inc(x_20);
 lean::dec(x_16);
 x_22 = lean::box(0);
}
x_23 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_23, 0, x_20);
if (lean::is_scalar(x_22)) {
 x_24 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_24 = x_22;
}
lean::cnstr_set(x_24, 0, x_23);
x_25 = lean::box(3);
x_26 = l_Option_getOrElse___main___rarg(x_24, x_25);
lean::dec(x_24);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_1);
x_29 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__3;
x_30 = l_Lean_Parser_Syntax_mkNode(x_29, x_28);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_1);
x_32 = l_Lean_Parser_detailIdentPart;
x_33 = l_Lean_Parser_Syntax_mkNode(x_32, x_31);
return x_33;
}
}
}
}
obj* _init_l_Lean_Parser_detailIdentPart_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_detailIdentPart_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_detailIdentPart_HasView_x_27;
return x_0;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdEndEscape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = l_String_OldIterator_next___main(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_17;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__3(x_4, x_0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdEndEscape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = l_String_OldIterator_next___main(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_17;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__5(x_4, x_0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdEndEscape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = l_String_OldIterator_next___main(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_17;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__7(x_4, x_0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_String_OldIterator_hasNext___main(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_4 = lean::box(0);
x_5 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_13 = x_7;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_9);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; obj* x_19; obj* x_21; obj* x_24; uint32 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_13);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_15, 2);
lean::inc(x_21);
lean::dec(x_15);
x_24 = l_String_splitAux___main___closed__1;
x_25 = lean::unbox_uint32(x_17);
x_26 = lean::string_push(x_24, x_25);
x_27 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__2(x_26, x_0, x_19, x_11);
x_28 = lean::cnstr_get(x_27, 0);
x_30 = lean::cnstr_get(x_27, 1);
if (lean::is_exclusive(x_27)) {
 x_32 = x_27;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::dec(x_27);
 x_32 = lean::box(0);
}
x_33 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_28);
if (lean::is_scalar(x_32)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_32;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_30);
return x_34;
}
else
{
obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_35 = lean::cnstr_get(x_15, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_38 = x_15;
} else {
 lean::inc(x_35);
 lean::dec(x_15);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_35);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_37);
x_40 = x_39;
if (lean::is_scalar(x_13)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_13;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_11);
return x_41;
}
}
else
{
uint32 x_42; uint8 x_43; 
x_42 = l_String_OldIterator_curr___main(x_1);
x_43 = l_Lean_isIdEndEscape(x_42);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_44 = l_String_OldIterator_next___main(x_1);
x_45 = l_String_splitAux___main___closed__1;
x_46 = lean::string_push(x_45, x_42);
x_47 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4(x_46, x_0, x_44, x_2);
x_48 = lean::cnstr_get(x_47, 0);
x_50 = lean::cnstr_get(x_47, 1);
if (lean::is_exclusive(x_47)) {
 x_52 = x_47;
} else {
 lean::inc(x_48);
 lean::inc(x_50);
 lean::dec(x_47);
 x_52 = lean::box(0);
}
x_53 = lean::box(0);
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_53, x_48);
if (lean::is_scalar(x_52)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_52;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_50);
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_67; obj* x_69; obj* x_70; obj* x_71; 
x_56 = l_Char_quoteCore(x_42);
x_57 = l_Char_HasRepr___closed__1;
x_58 = lean::string_append(x_57, x_56);
lean::dec(x_56);
x_60 = lean::string_append(x_58, x_57);
x_61 = lean::box(0);
x_62 = l_mjoin___rarg___closed__1;
x_63 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_60, x_62, x_61, x_61, x_0, x_1, x_2);
lean::dec(x_1);
x_65 = lean::cnstr_get(x_63, 0);
x_67 = lean::cnstr_get(x_63, 1);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_set(x_63, 0, lean::box(0));
 lean::cnstr_set(x_63, 1, lean::box(0));
 x_69 = x_63;
} else {
 lean::inc(x_65);
 lean::inc(x_67);
 lean::dec(x_63);
 x_69 = lean::box(0);
}
x_70 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_71 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_70, x_65);
if (lean::obj_tag(x_71) == 0)
{
obj* x_73; obj* x_75; obj* x_77; obj* x_80; uint32 x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_86; obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_69);
x_73 = lean::cnstr_get(x_71, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_71, 1);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_71, 2);
lean::inc(x_77);
lean::dec(x_71);
x_80 = l_String_splitAux___main___closed__1;
x_81 = lean::unbox_uint32(x_73);
x_82 = lean::string_push(x_80, x_81);
x_83 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__6(x_82, x_0, x_75, x_67);
x_84 = lean::cnstr_get(x_83, 0);
x_86 = lean::cnstr_get(x_83, 1);
if (lean::is_exclusive(x_83)) {
 x_88 = x_83;
} else {
 lean::inc(x_84);
 lean::inc(x_86);
 lean::dec(x_83);
 x_88 = lean::box(0);
}
x_89 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_77, x_84);
if (lean::is_scalar(x_88)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_88;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_86);
return x_90;
}
else
{
obj* x_91; uint8 x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_91 = lean::cnstr_get(x_71, 0);
x_93 = lean::cnstr_get_scalar<uint8>(x_71, sizeof(void*)*1);
if (lean::is_exclusive(x_71)) {
 x_94 = x_71;
} else {
 lean::inc(x_91);
 lean::dec(x_71);
 x_94 = lean::box(0);
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_91);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_93);
x_96 = x_95;
if (lean::is_scalar(x_69)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_69;
}
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_67);
return x_97;
}
}
}
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__10(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdEndEscape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = l_String_OldIterator_next___main(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_17;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__10(x_4, x_0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__12(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdEndEscape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = l_String_OldIterator_next___main(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_17;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__11(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__12(x_4, x_0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__14(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdEndEscape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = l_String_OldIterator_next___main(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_17;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__13(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__14(x_4, x_0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__8(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_String_OldIterator_hasNext___main(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_4 = lean::box(0);
x_5 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_13 = x_7;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_9);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; obj* x_19; obj* x_21; obj* x_24; uint32 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_13);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_15, 2);
lean::inc(x_21);
lean::dec(x_15);
x_24 = l_String_splitAux___main___closed__1;
x_25 = lean::unbox_uint32(x_17);
x_26 = lean::string_push(x_24, x_25);
x_27 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__9(x_26, x_0, x_19, x_11);
x_28 = lean::cnstr_get(x_27, 0);
x_30 = lean::cnstr_get(x_27, 1);
if (lean::is_exclusive(x_27)) {
 x_32 = x_27;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::dec(x_27);
 x_32 = lean::box(0);
}
x_33 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_28);
if (lean::is_scalar(x_32)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_32;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_30);
return x_34;
}
else
{
obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_35 = lean::cnstr_get(x_15, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_38 = x_15;
} else {
 lean::inc(x_35);
 lean::dec(x_15);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_35);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_37);
x_40 = x_39;
if (lean::is_scalar(x_13)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_13;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_11);
return x_41;
}
}
else
{
uint32 x_42; uint8 x_43; 
x_42 = l_String_OldIterator_curr___main(x_1);
x_43 = l_Lean_isIdEndEscape(x_42);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_44 = l_String_OldIterator_next___main(x_1);
x_45 = l_String_splitAux___main___closed__1;
x_46 = lean::string_push(x_45, x_42);
x_47 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__11(x_46, x_0, x_44, x_2);
x_48 = lean::cnstr_get(x_47, 0);
x_50 = lean::cnstr_get(x_47, 1);
if (lean::is_exclusive(x_47)) {
 x_52 = x_47;
} else {
 lean::inc(x_48);
 lean::inc(x_50);
 lean::dec(x_47);
 x_52 = lean::box(0);
}
x_53 = lean::box(0);
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_53, x_48);
if (lean::is_scalar(x_52)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_52;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_50);
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_67; obj* x_69; obj* x_70; obj* x_71; 
x_56 = l_Char_quoteCore(x_42);
x_57 = l_Char_HasRepr___closed__1;
x_58 = lean::string_append(x_57, x_56);
lean::dec(x_56);
x_60 = lean::string_append(x_58, x_57);
x_61 = lean::box(0);
x_62 = l_mjoin___rarg___closed__1;
x_63 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_60, x_62, x_61, x_61, x_0, x_1, x_2);
lean::dec(x_1);
x_65 = lean::cnstr_get(x_63, 0);
x_67 = lean::cnstr_get(x_63, 1);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_set(x_63, 0, lean::box(0));
 lean::cnstr_set(x_63, 1, lean::box(0));
 x_69 = x_63;
} else {
 lean::inc(x_65);
 lean::inc(x_67);
 lean::dec(x_63);
 x_69 = lean::box(0);
}
x_70 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_71 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_70, x_65);
if (lean::obj_tag(x_71) == 0)
{
obj* x_73; obj* x_75; obj* x_77; obj* x_80; uint32 x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_86; obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_69);
x_73 = lean::cnstr_get(x_71, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_71, 1);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_71, 2);
lean::inc(x_77);
lean::dec(x_71);
x_80 = l_String_splitAux___main___closed__1;
x_81 = lean::unbox_uint32(x_73);
x_82 = lean::string_push(x_80, x_81);
x_83 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__13(x_82, x_0, x_75, x_67);
x_84 = lean::cnstr_get(x_83, 0);
x_86 = lean::cnstr_get(x_83, 1);
if (lean::is_exclusive(x_83)) {
 x_88 = x_83;
} else {
 lean::inc(x_84);
 lean::inc(x_86);
 lean::dec(x_83);
 x_88 = lean::box(0);
}
x_89 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_77, x_84);
if (lean::is_scalar(x_88)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_88;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_86);
return x_90;
}
else
{
obj* x_91; uint8 x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_91 = lean::cnstr_get(x_71, 0);
x_93 = lean::cnstr_get_scalar<uint8>(x_71, sizeof(void*)*1);
if (lean::is_exclusive(x_71)) {
 x_94 = x_71;
} else {
 lean::inc(x_91);
 lean::dec(x_71);
 x_94 = lean::box(0);
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_91);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_93);
x_96 = x_95;
if (lean::is_scalar(x_69)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_69;
}
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_67);
return x_97;
}
}
}
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__16(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_3);
lean::dec(x_0);
x_8 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_4);
lean::cnstr_set(x_9, 2, x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_5);
return x_10;
}
else
{
obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_20; obj* x_21; 
x_11 = lean::cnstr_get(x_2, 0);
x_13 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_15 = x_2;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_2);
 x_15 = lean::box(0);
}
lean::inc(x_3);
x_20 = lean::apply_3(x_11, x_3, x_4, x_5);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_23; 
x_23 = lean::cnstr_get(x_20, 1);
lean::inc(x_23);
lean::dec(x_20);
x_16 = x_21;
x_17 = x_23;
goto lbl_18;
}
else
{
uint8 x_26; 
x_26 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
if (lean::obj_tag(x_1) == 0)
{
if (x_26 == 0)
{
obj* x_27; obj* x_30; obj* x_32; uint8 x_33; obj* x_34; obj* x_35; 
x_27 = lean::cnstr_get(x_20, 1);
lean::inc(x_27);
lean::dec(x_20);
x_30 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 x_32 = x_21;
} else {
 lean::inc(x_30);
 lean::dec(x_21);
 x_32 = lean::box(0);
}
x_33 = 0;
if (lean::is_scalar(x_32)) {
 x_34 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_34 = x_32;
}
lean::cnstr_set(x_34, 0, x_30);
lean::cnstr_set_scalar(x_34, sizeof(void*)*1, x_33);
x_35 = x_34;
x_16 = x_35;
x_17 = x_27;
goto lbl_18;
}
else
{
obj* x_36; obj* x_39; obj* x_41; uint8 x_42; obj* x_43; obj* x_44; 
x_36 = lean::cnstr_get(x_20, 1);
lean::inc(x_36);
lean::dec(x_20);
x_39 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 x_41 = x_21;
} else {
 lean::inc(x_39);
 lean::dec(x_21);
 x_41 = lean::box(0);
}
x_42 = 1;
if (lean::is_scalar(x_41)) {
 x_43 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_43 = x_41;
}
lean::cnstr_set(x_43, 0, x_39);
lean::cnstr_set_scalar(x_43, sizeof(void*)*1, x_42);
x_44 = x_43;
x_16 = x_44;
x_17 = x_36;
goto lbl_18;
}
}
else
{
obj* x_45; obj* x_48; obj* x_50; obj* x_51; obj* x_53; obj* x_56; obj* x_57; obj* x_59; obj* x_61; obj* x_64; obj* x_66; obj* x_67; obj* x_68; 
x_45 = lean::cnstr_get(x_20, 1);
lean::inc(x_45);
lean::dec(x_20);
x_48 = lean::cnstr_get(x_21, 0);
if (lean::is_exclusive(x_21)) {
 lean::cnstr_set(x_21, 0, lean::box(0));
 x_50 = x_21;
} else {
 lean::inc(x_48);
 lean::dec(x_21);
 x_50 = lean::box(0);
}
x_51 = lean::cnstr_get(x_48, 3);
lean::inc(x_51);
x_53 = l_Option_get___main___at_Lean_Parser_run___spec__2(x_51);
lean::dec(x_51);
lean::inc(x_1);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_53);
lean::cnstr_set(x_56, 1, x_1);
x_57 = lean::cnstr_get(x_48, 0);
lean::inc(x_57);
x_59 = lean::cnstr_get(x_48, 1);
lean::inc(x_59);
x_61 = lean::cnstr_get(x_48, 2);
lean::inc(x_61);
lean::dec(x_48);
x_64 = l_List_reverse___rarg(x_56);
lean::inc(x_0);
x_66 = l_Lean_Parser_Syntax_mkNode(x_0, x_64);
x_67 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_67, 0, x_66);
x_68 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_68, 0, x_57);
lean::cnstr_set(x_68, 1, x_59);
lean::cnstr_set(x_68, 2, x_61);
lean::cnstr_set(x_68, 3, x_67);
if (x_26 == 0)
{
uint8 x_69; obj* x_70; obj* x_71; 
x_69 = 0;
if (lean::is_scalar(x_50)) {
 x_70 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_70 = x_50;
}
lean::cnstr_set(x_70, 0, x_68);
lean::cnstr_set_scalar(x_70, sizeof(void*)*1, x_69);
x_71 = x_70;
x_16 = x_71;
x_17 = x_45;
goto lbl_18;
}
else
{
uint8 x_72; obj* x_73; obj* x_74; 
x_72 = 1;
if (lean::is_scalar(x_50)) {
 x_73 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_73 = x_50;
}
lean::cnstr_set(x_73, 0, x_68);
lean::cnstr_set_scalar(x_73, sizeof(void*)*1, x_72);
x_74 = x_73;
x_16 = x_74;
x_17 = x_45;
goto lbl_18;
}
}
}
lbl_18:
{
if (lean::obj_tag(x_16) == 0)
{
obj* x_75; obj* x_77; obj* x_79; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_75 = lean::cnstr_get(x_16, 0);
x_77 = lean::cnstr_get(x_16, 1);
x_79 = lean::cnstr_get(x_16, 2);
if (lean::is_exclusive(x_16)) {
 x_81 = x_16;
} else {
 lean::inc(x_75);
 lean::inc(x_77);
 lean::inc(x_79);
 lean::dec(x_16);
 x_81 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_82 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_82 = x_15;
}
lean::cnstr_set(x_82, 0, x_75);
lean::cnstr_set(x_82, 1, x_1);
x_83 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_81)) {
 x_84 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_84 = x_81;
}
lean::cnstr_set(x_84, 0, x_82);
lean::cnstr_set(x_84, 1, x_77);
lean::cnstr_set(x_84, 2, x_83);
x_85 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_79, x_84);
if (lean::obj_tag(x_85) == 0)
{
obj* x_86; obj* x_88; obj* x_90; obj* x_93; obj* x_94; obj* x_96; obj* x_98; obj* x_99; obj* x_100; 
x_86 = lean::cnstr_get(x_85, 0);
lean::inc(x_86);
x_88 = lean::cnstr_get(x_85, 1);
lean::inc(x_88);
x_90 = lean::cnstr_get(x_85, 2);
lean::inc(x_90);
lean::dec(x_85);
x_93 = l_List_mfoldl___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__16(x_0, x_86, x_13, x_3, x_88, x_17);
x_94 = lean::cnstr_get(x_93, 0);
x_96 = lean::cnstr_get(x_93, 1);
if (lean::is_exclusive(x_93)) {
 x_98 = x_93;
} else {
 lean::inc(x_94);
 lean::inc(x_96);
 lean::dec(x_93);
 x_98 = lean::box(0);
}
x_99 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_90, x_94);
if (lean::is_scalar(x_98)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_98;
}
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_96);
return x_100;
}
else
{
obj* x_104; uint8 x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
lean::dec(x_13);
lean::dec(x_3);
lean::dec(x_0);
x_104 = lean::cnstr_get(x_85, 0);
x_106 = lean::cnstr_get_scalar<uint8>(x_85, sizeof(void*)*1);
if (lean::is_exclusive(x_85)) {
 x_107 = x_85;
} else {
 lean::inc(x_104);
 lean::dec(x_85);
 x_107 = lean::box(0);
}
if (lean::is_scalar(x_107)) {
 x_108 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_108 = x_107;
}
lean::cnstr_set(x_108, 0, x_104);
lean::cnstr_set_scalar(x_108, sizeof(void*)*1, x_106);
x_109 = x_108;
x_110 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_17);
return x_110;
}
}
else
{
obj* x_116; uint8 x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; 
lean::dec(x_13);
lean::dec(x_15);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
x_116 = lean::cnstr_get(x_16, 0);
x_118 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
if (lean::is_exclusive(x_16)) {
 x_119 = x_16;
} else {
 lean::inc(x_116);
 lean::dec(x_16);
 x_119 = lean::box(0);
}
if (lean::is_scalar(x_119)) {
 x_120 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_120 = x_119;
}
lean::cnstr_set(x_120, 0, x_116);
lean::cnstr_set_scalar(x_120, sizeof(void*)*1, x_118);
x_121 = x_120;
x_122 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_122, 0, x_121);
lean::cnstr_set(x_122, 1, x_17);
return x_122;
}
}
}
}
}
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__15(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_7; obj* x_8; 
x_5 = lean::box(0);
lean::inc(x_0);
x_7 = l_List_mfoldl___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__16(x_0, x_5, x_1, x_2, x_3, x_4);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_10 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_12 = x_7;
} else {
 lean::inc(x_10);
 lean::dec(x_7);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_8, 0);
x_15 = lean::cnstr_get(x_8, 1);
x_17 = lean::cnstr_get(x_8, 2);
if (lean::is_exclusive(x_8)) {
 x_19 = x_8;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_8);
 x_19 = lean::box(0);
}
x_20 = l_List_reverse___rarg(x_13);
x_21 = l_Lean_Parser_Syntax_mkNode(x_0, x_20);
x_22 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_19)) {
 x_23 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_23 = x_19;
}
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_15);
lean::cnstr_set(x_23, 2, x_22);
x_24 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_23);
if (lean::is_scalar(x_12)) {
 x_25 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_25 = x_12;
}
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_10);
return x_25;
}
else
{
obj* x_27; obj* x_29; obj* x_30; uint8 x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_0);
x_27 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_29 = x_7;
} else {
 lean::inc(x_27);
 lean::dec(x_7);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_8, 0);
x_32 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_33 = x_8;
} else {
 lean::inc(x_30);
 lean::dec(x_8);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_30);
lean::cnstr_set_scalar(x_34, sizeof(void*)*1, x_32);
x_35 = x_34;
if (lean::is_scalar(x_29)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_29;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_27);
return x_36;
}
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__18(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdRest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_OldIterator_next___main(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__17___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_String_OldIterator_remaining___main(x_0);
x_3 = l_String_splitAux___main___closed__1;
x_4 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__18(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__17(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__17___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__20(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdRest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_OldIterator_next___main(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__19___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_String_OldIterator_remaining___main(x_0);
x_3 = l_String_splitAux___main___closed__1;
x_4 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__20(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__19(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__19___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__22(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdRest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_OldIterator_next___main(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__21___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_String_OldIterator_remaining___main(x_0);
x_3 = l_String_splitAux___main___closed__1;
x_4 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__22(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__21(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__21___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__24(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdRest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_OldIterator_next___main(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__23___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_String_OldIterator_remaining___main(x_0);
x_3 = l_String_splitAux___main___closed__1;
x_4 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__24(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__23(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__23___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__26(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdRest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_OldIterator_next___main(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__25___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_String_OldIterator_remaining___main(x_0);
x_3 = l_String_splitAux___main___closed__1;
x_4 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__26(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__25(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__25___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__28(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdRest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_OldIterator_next___main(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__27___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_String_OldIterator_remaining___main(x_0);
x_3 = l_String_splitAux___main___closed__1;
x_4 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__28(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__27(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__27___rarg), 2, 0);
return x_1;
}
}
obj* l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__29(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_1);
x_6 = lean::box(0);
x_7 = l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1;
x_8 = l_mjoin___rarg___closed__1;
x_9 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_7, x_8, x_6, x_6, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_9;
}
else
{
obj* x_12; obj* x_14; obj* x_16; obj* x_19; obj* x_20; obj* x_22; obj* x_24; obj* x_25; obj* x_26; 
x_12 = lean::cnstr_get(x_0, 0);
x_14 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 lean::cnstr_set(x_0, 1, lean::box(0));
 x_16 = x_0;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_0);
 x_16 = lean::box(0);
}
lean::inc(x_3);
lean::inc(x_2);
x_19 = lean::apply_3(x_12, x_2, x_3, x_4);
x_20 = lean::cnstr_get(x_19, 0);
x_22 = lean::cnstr_get(x_19, 1);
if (lean::is_exclusive(x_19)) {
 lean::cnstr_set(x_19, 0, lean::box(0));
 lean::cnstr_set(x_19, 1, lean::box(0));
 x_24 = x_19;
} else {
 lean::inc(x_20);
 lean::inc(x_22);
 lean::dec(x_19);
 x_24 = lean::box(0);
}
x_25 = lean::mk_nat_obj(1u);
x_26 = lean::nat_add(x_1, x_25);
if (lean::obj_tag(x_20) == 0)
{
obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_27 = lean::cnstr_get(x_20, 0);
x_29 = lean::cnstr_get(x_20, 1);
x_31 = lean::cnstr_get(x_20, 2);
if (lean::is_exclusive(x_20)) {
 x_33 = x_20;
} else {
 lean::inc(x_27);
 lean::inc(x_29);
 lean::inc(x_31);
 lean::dec(x_20);
 x_33 = lean::box(0);
}
x_34 = lean::box(0);
x_35 = lean_name_mk_numeral(x_34, x_1);
x_36 = lean::box(0);
if (lean::is_scalar(x_16)) {
 x_37 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_37 = x_16;
}
lean::cnstr_set(x_37, 0, x_27);
lean::cnstr_set(x_37, 1, x_36);
x_38 = l_Lean_Parser_Syntax_mkNode(x_35, x_37);
x_39 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_33)) {
 x_40 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_40 = x_33;
}
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_29);
lean::cnstr_set(x_40, 2, x_39);
x_41 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_31, x_40);
if (lean::obj_tag(x_41) == 0)
{
obj* x_46; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_26);
lean::dec(x_14);
if (lean::is_scalar(x_24)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_24;
}
lean::cnstr_set(x_46, 0, x_41);
lean::cnstr_set(x_46, 1, x_22);
return x_46;
}
else
{
uint8 x_47; 
x_47 = lean::cnstr_get_scalar<uint8>(x_41, sizeof(void*)*1);
if (x_47 == 0)
{
obj* x_49; obj* x_52; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_24);
x_49 = lean::cnstr_get(x_41, 0);
lean::inc(x_49);
lean::dec(x_41);
x_52 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__29(x_14, x_26, x_2, x_3, x_22);
x_53 = lean::cnstr_get(x_52, 0);
x_55 = lean::cnstr_get(x_52, 1);
if (lean::is_exclusive(x_52)) {
 x_57 = x_52;
} else {
 lean::inc(x_53);
 lean::inc(x_55);
 lean::dec(x_52);
 x_57 = lean::box(0);
}
x_58 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_49, x_53);
if (lean::is_scalar(x_57)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_57;
}
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_55);
return x_59;
}
else
{
obj* x_64; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_26);
lean::dec(x_14);
if (lean::is_scalar(x_24)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_24;
}
lean::cnstr_set(x_64, 0, x_41);
lean::cnstr_set(x_64, 1, x_22);
return x_64;
}
}
}
else
{
uint8 x_67; 
lean::dec(x_1);
lean::dec(x_16);
x_67 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
if (x_67 == 0)
{
obj* x_69; obj* x_72; obj* x_73; obj* x_75; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_24);
x_69 = lean::cnstr_get(x_20, 0);
lean::inc(x_69);
lean::dec(x_20);
x_72 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__29(x_14, x_26, x_2, x_3, x_22);
x_73 = lean::cnstr_get(x_72, 0);
x_75 = lean::cnstr_get(x_72, 1);
if (lean::is_exclusive(x_72)) {
 x_77 = x_72;
} else {
 lean::inc(x_73);
 lean::inc(x_75);
 lean::dec(x_72);
 x_77 = lean::box(0);
}
x_78 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_69, x_73);
if (lean::is_scalar(x_77)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_77;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_75);
return x_79;
}
else
{
obj* x_84; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_26);
lean::dec(x_14);
x_84 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_86 = x_20;
} else {
 lean::inc(x_84);
 lean::dec(x_20);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_84);
lean::cnstr_set_scalar(x_87, sizeof(void*)*1, x_67);
x_88 = x_87;
if (lean::is_scalar(x_24)) {
 x_89 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_89 = x_24;
}
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_22);
return x_89;
}
}
}
}
}
obj* _init_l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_5; obj* x_7; obj* x_10; obj* x_12; obj* x_14; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_List_cons_tokens___rarg(x_0, x_0);
x_2 = l_Lean_Parser_List_cons_tokens___rarg(x_0, x_1);
x_3 = l_Lean_Parser_List_cons_tokens___rarg(x_0, x_2);
lean::dec(x_2);
x_5 = l_Lean_Parser_tokens___rarg(x_3);
lean::dec(x_3);
x_7 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_1);
lean::dec(x_1);
lean::dec(x_5);
x_10 = l_Lean_Parser_tokens___rarg(x_7);
lean::dec(x_7);
x_12 = l_Lean_Parser_List_cons_tokens___rarg(x_10, x_0);
lean::dec(x_10);
x_14 = l_Lean_Parser_tokens___rarg(x_12);
lean::dec(x_12);
return x_14;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__6(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__9___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__9(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__11___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__11(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__13___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__13(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__8___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__8(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__17___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__17(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__19___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__19(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__21___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__21(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__23___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__23(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__25___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__25(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__27___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__27(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdEndEscape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = l_String_OldIterator_next___main(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_17;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__3(x_4, x_0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdEndEscape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = l_String_OldIterator_next___main(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_17;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__5(x_4, x_0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdEndEscape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = l_String_OldIterator_next___main(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_17;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__7(x_4, x_0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_String_OldIterator_hasNext___main(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_4 = lean::box(0);
x_5 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_13 = x_7;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_9);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; obj* x_19; obj* x_21; obj* x_24; uint32 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_13);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_15, 2);
lean::inc(x_21);
lean::dec(x_15);
x_24 = l_String_splitAux___main___closed__1;
x_25 = lean::unbox_uint32(x_17);
x_26 = lean::string_push(x_24, x_25);
x_27 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__2(x_26, x_0, x_19, x_11);
x_28 = lean::cnstr_get(x_27, 0);
x_30 = lean::cnstr_get(x_27, 1);
if (lean::is_exclusive(x_27)) {
 x_32 = x_27;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::dec(x_27);
 x_32 = lean::box(0);
}
x_33 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_28);
if (lean::is_scalar(x_32)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_32;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_30);
return x_34;
}
else
{
obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_35 = lean::cnstr_get(x_15, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_38 = x_15;
} else {
 lean::inc(x_35);
 lean::dec(x_15);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_35);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_37);
x_40 = x_39;
if (lean::is_scalar(x_13)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_13;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_11);
return x_41;
}
}
else
{
uint32 x_42; uint8 x_43; 
x_42 = l_String_OldIterator_curr___main(x_1);
x_43 = l_Lean_isIdEndEscape(x_42);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_44 = l_String_OldIterator_next___main(x_1);
x_45 = l_String_splitAux___main___closed__1;
x_46 = lean::string_push(x_45, x_42);
x_47 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__4(x_46, x_0, x_44, x_2);
x_48 = lean::cnstr_get(x_47, 0);
x_50 = lean::cnstr_get(x_47, 1);
if (lean::is_exclusive(x_47)) {
 x_52 = x_47;
} else {
 lean::inc(x_48);
 lean::inc(x_50);
 lean::dec(x_47);
 x_52 = lean::box(0);
}
x_53 = lean::box(0);
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_53, x_48);
if (lean::is_scalar(x_52)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_52;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_50);
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_67; obj* x_69; obj* x_70; obj* x_71; 
x_56 = l_Char_quoteCore(x_42);
x_57 = l_Char_HasRepr___closed__1;
x_58 = lean::string_append(x_57, x_56);
lean::dec(x_56);
x_60 = lean::string_append(x_58, x_57);
x_61 = lean::box(0);
x_62 = l_mjoin___rarg___closed__1;
x_63 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_60, x_62, x_61, x_61, x_0, x_1, x_2);
lean::dec(x_1);
x_65 = lean::cnstr_get(x_63, 0);
x_67 = lean::cnstr_get(x_63, 1);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_set(x_63, 0, lean::box(0));
 lean::cnstr_set(x_63, 1, lean::box(0));
 x_69 = x_63;
} else {
 lean::inc(x_65);
 lean::inc(x_67);
 lean::dec(x_63);
 x_69 = lean::box(0);
}
x_70 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_71 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_70, x_65);
if (lean::obj_tag(x_71) == 0)
{
obj* x_73; obj* x_75; obj* x_77; obj* x_80; uint32 x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_86; obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_69);
x_73 = lean::cnstr_get(x_71, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_71, 1);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_71, 2);
lean::inc(x_77);
lean::dec(x_71);
x_80 = l_String_splitAux___main___closed__1;
x_81 = lean::unbox_uint32(x_73);
x_82 = lean::string_push(x_80, x_81);
x_83 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__6(x_82, x_0, x_75, x_67);
x_84 = lean::cnstr_get(x_83, 0);
x_86 = lean::cnstr_get(x_83, 1);
if (lean::is_exclusive(x_83)) {
 x_88 = x_83;
} else {
 lean::inc(x_84);
 lean::inc(x_86);
 lean::dec(x_83);
 x_88 = lean::box(0);
}
x_89 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_77, x_84);
if (lean::is_scalar(x_88)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_88;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_86);
return x_90;
}
else
{
obj* x_91; uint8 x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_91 = lean::cnstr_get(x_71, 0);
x_93 = lean::cnstr_get_scalar<uint8>(x_71, sizeof(void*)*1);
if (lean::is_exclusive(x_71)) {
 x_94 = x_71;
} else {
 lean::inc(x_91);
 lean::dec(x_71);
 x_94 = lean::box(0);
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_91);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_93);
x_96 = x_95;
if (lean::is_scalar(x_69)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_69;
}
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_67);
return x_97;
}
}
}
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__9(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdRest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_OldIterator_next___main(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__8___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_String_OldIterator_remaining___main(x_0);
x_3 = l_String_splitAux___main___closed__1;
x_4 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__9(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__8(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__8___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__11(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdRest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_OldIterator_next___main(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__10___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_String_OldIterator_remaining___main(x_0);
x_3 = l_String_splitAux___main___closed__1;
x_4 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__11(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__10(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__10___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__13(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdRest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_OldIterator_next___main(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__12___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_String_OldIterator_remaining___main(x_0);
x_3 = l_String_splitAux___main___closed__1;
x_4 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__13(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__12(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__12___rarg), 2, 0);
return x_1;
}
}
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3(x_0, x_1, x_3, x_4, x_5);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_11 = x_6;
} else {
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_7, 1);
x_14 = lean::cnstr_get(x_7, 2);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_16 = x_7;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_7);
 x_16 = lean::box(0);
}
lean::inc(x_12);
x_18 = l_Lean_Parser_mkRawRes(x_2, x_12);
x_19 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_16)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_16;
}
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_12);
lean::cnstr_set(x_20, 2, x_19);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_20);
if (lean::is_scalar(x_11)) {
 x_22 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_22 = x_11;
}
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_9);
return x_22;
}
else
{
obj* x_24; obj* x_26; obj* x_27; uint8 x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_2);
x_24 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_26 = x_6;
} else {
 lean::inc(x_24);
 lean::dec(x_6);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_7, 0);
x_29 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_30 = x_7;
} else {
 lean::inc(x_27);
 lean::dec(x_7);
 x_30 = lean::box(0);
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_27);
lean::cnstr_set_scalar(x_31, sizeof(void*)*1, x_29);
x_32 = x_31;
if (lean::is_scalar(x_26)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_26;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_24);
return x_33;
}
}
}
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__1(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 1);
x_12 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_14 = x_5;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
lean::inc(x_10);
x_16 = l_Lean_Parser_mkRawRes(x_0, x_10);
x_17 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_14)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_14;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_10);
lean::cnstr_set(x_18, 2, x_17);
x_19 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_18);
if (lean::is_scalar(x_9)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_9;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_7);
return x_20;
}
else
{
obj* x_22; obj* x_24; obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_0);
x_22 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_24 = x_4;
} else {
 lean::inc(x_22);
 lean::dec(x_4);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_5, 0);
x_27 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_28 = x_5;
} else {
 lean::inc(x_25);
 lean::dec(x_5);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_27);
x_30 = x_29;
if (lean::is_scalar(x_24)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_24;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_22);
return x_31;
}
}
}
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_7; 
x_7 = l_String_OldIterator_hasNext___main(x_2);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_18; obj* x_19; 
x_8 = lean::box(0);
x_9 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_10 = l_mjoin___rarg___closed__1;
x_11 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_9, x_10, x_8, x_8, x_1, x_2, x_3);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_11, 1);
lean::inc(x_15);
lean::dec(x_11);
x_18 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_19 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_13);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_22; obj* x_25; obj* x_26; obj* x_28; obj* x_31; 
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 2);
lean::inc(x_22);
lean::dec(x_19);
x_25 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__8___rarg(x_20, x_15);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
x_31 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_26);
x_4 = x_31;
x_5 = x_28;
goto lbl_6;
}
else
{
obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; 
x_32 = lean::cnstr_get(x_19, 0);
x_34 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
if (lean::is_exclusive(x_19)) {
 x_35 = x_19;
} else {
 lean::inc(x_32);
 lean::dec(x_19);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_34);
x_37 = x_36;
x_4 = x_37;
x_5 = x_15;
goto lbl_6;
}
}
else
{
uint32 x_38; uint8 x_39; 
x_38 = l_String_OldIterator_curr___main(x_2);
x_39 = l_Lean_isIdFirst(x_38);
if (x_39 == 0)
{
obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_49; obj* x_51; obj* x_54; obj* x_55; 
x_40 = l_Char_quoteCore(x_38);
x_41 = l_Char_HasRepr___closed__1;
x_42 = lean::string_append(x_41, x_40);
lean::dec(x_40);
x_44 = lean::string_append(x_42, x_41);
x_45 = lean::box(0);
x_46 = l_mjoin___rarg___closed__1;
x_47 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_44, x_46, x_45, x_45, x_1, x_2, x_3);
lean::dec(x_2);
x_49 = lean::cnstr_get(x_47, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_47, 1);
lean::inc(x_51);
lean::dec(x_47);
x_54 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_55 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_54, x_49);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; obj* x_58; obj* x_61; obj* x_62; obj* x_64; obj* x_67; 
x_56 = lean::cnstr_get(x_55, 1);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_55, 2);
lean::inc(x_58);
lean::dec(x_55);
x_61 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__10___rarg(x_56, x_51);
x_62 = lean::cnstr_get(x_61, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_61, 1);
lean::inc(x_64);
lean::dec(x_61);
x_67 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_62);
x_4 = x_67;
x_5 = x_64;
goto lbl_6;
}
else
{
obj* x_68; uint8 x_70; obj* x_71; obj* x_72; obj* x_73; 
x_68 = lean::cnstr_get(x_55, 0);
x_70 = lean::cnstr_get_scalar<uint8>(x_55, sizeof(void*)*1);
if (lean::is_exclusive(x_55)) {
 x_71 = x_55;
} else {
 lean::inc(x_68);
 lean::dec(x_55);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_68);
lean::cnstr_set_scalar(x_72, sizeof(void*)*1, x_70);
x_73 = x_72;
x_4 = x_73;
x_5 = x_51;
goto lbl_6;
}
}
else
{
obj* x_74; obj* x_75; obj* x_76; obj* x_78; obj* x_81; obj* x_82; 
x_74 = l_String_OldIterator_next___main(x_2);
x_75 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__12___rarg(x_74, x_3);
x_76 = lean::cnstr_get(x_75, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_75, 1);
lean::inc(x_78);
lean::dec(x_75);
x_81 = lean::box(0);
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_81, x_76);
x_4 = x_82;
x_5 = x_78;
goto lbl_6;
}
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_83; obj* x_85; obj* x_87; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_83 = lean::cnstr_get(x_4, 1);
x_85 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_87 = x_4;
} else {
 lean::inc(x_83);
 lean::inc(x_85);
 lean::dec(x_4);
 x_87 = lean::box(0);
}
lean::inc(x_83);
x_89 = l_Lean_Parser_mkRawRes(x_0, x_83);
x_90 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_87)) {
 x_91 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_91 = x_87;
}
lean::cnstr_set(x_91, 0, x_89);
lean::cnstr_set(x_91, 1, x_83);
lean::cnstr_set(x_91, 2, x_90);
x_92 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_85, x_91);
x_93 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_5);
return x_93;
}
else
{
obj* x_95; uint8 x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
lean::dec(x_0);
x_95 = lean::cnstr_get(x_4, 0);
x_97 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_98 = x_4;
} else {
 lean::inc(x_95);
 lean::dec(x_4);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_95);
lean::cnstr_set_scalar(x_99, sizeof(void*)*1, x_97);
x_100 = x_99;
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_5);
return x_101;
}
}
}
}
obj* _init_l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; uint32 x_1; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_14; uint32 x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_0 = lean::mk_string("");
x_1 = l_Lean_idBeginEscape;
lean::inc(x_0);
x_3 = lean::string_push(x_0, x_1);
lean::inc(x_3);
x_5 = l_String_quote(x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__1___boxed), 6, 2);
lean::closure_set(x_9, 0, x_3);
lean::closure_set(x_9, 1, x_6);
lean::inc(x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_11, 0, x_8);
lean::closure_set(x_11, 1, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__2___boxed), 4, 0);
lean::inc(x_8);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_14, 0, x_8);
lean::closure_set(x_14, 1, x_12);
x_15 = l_Lean_idEndEscape;
x_16 = lean::string_push(x_0, x_15);
lean::inc(x_16);
x_18 = l_String_quote(x_16);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__1___boxed), 6, 2);
lean::closure_set(x_20, 0, x_16);
lean::closure_set(x_20, 1, x_19);
lean::inc(x_8);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_22, 0, x_8);
lean::closure_set(x_22, 1, x_20);
x_23 = lean::box(0);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_14);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_11);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_Lean_Parser_detailIdentPartEscaped;
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__15), 5, 2);
lean::closure_set(x_28, 0, x_27);
lean::closure_set(x_28, 1, x_26);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__3___boxed), 4, 0);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_30, 0, x_8);
lean::closure_set(x_30, 1, x_29);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_23);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_28);
lean::cnstr_set(x_32, 1, x_31);
x_33 = lean::mk_nat_obj(0u);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__29), 5, 2);
lean::closure_set(x_34, 0, x_32);
lean::closure_set(x_34, 1, x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_23);
x_36 = l_Lean_Parser_BasicParserM_Monad;
x_37 = l_Lean_Parser_BasicParserM_MonadExcept;
x_38 = l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
x_39 = l_Lean_Parser_BasicParserM_Alternative;
x_40 = l_Lean_Parser_detailIdentPart;
x_41 = l_Lean_Parser_detailIdentPart_HasView;
x_42 = l_Lean_Parser_Combinators_node_view___rarg(x_36, x_37, x_38, x_39, x_40, x_35, x_41);
lean::dec(x_35);
return x_42;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__6(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__8___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__8(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__10___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__10(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__12___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___spec__12(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__2(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__3(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdEndEscape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = l_String_OldIterator_next___main(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_17;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser___spec__3(x_4, x_0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdEndEscape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = l_String_OldIterator_next___main(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_17;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser___spec__5(x_4, x_0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdEndEscape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = l_String_OldIterator_next___main(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_17;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser___spec__7(x_4, x_0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_String_OldIterator_hasNext___main(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_4 = lean::box(0);
x_5 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_13 = x_7;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_9);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; obj* x_19; obj* x_21; obj* x_24; uint32 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_13);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_15, 2);
lean::inc(x_21);
lean::dec(x_15);
x_24 = l_String_splitAux___main___closed__1;
x_25 = lean::unbox_uint32(x_17);
x_26 = lean::string_push(x_24, x_25);
x_27 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser___spec__2(x_26, x_0, x_19, x_11);
x_28 = lean::cnstr_get(x_27, 0);
x_30 = lean::cnstr_get(x_27, 1);
if (lean::is_exclusive(x_27)) {
 x_32 = x_27;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::dec(x_27);
 x_32 = lean::box(0);
}
x_33 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_28);
if (lean::is_scalar(x_32)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_32;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_30);
return x_34;
}
else
{
obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_35 = lean::cnstr_get(x_15, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_38 = x_15;
} else {
 lean::inc(x_35);
 lean::dec(x_15);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_35);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_37);
x_40 = x_39;
if (lean::is_scalar(x_13)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_13;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_11);
return x_41;
}
}
else
{
uint32 x_42; uint8 x_43; 
x_42 = l_String_OldIterator_curr___main(x_1);
x_43 = l_Lean_isIdEndEscape(x_42);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_44 = l_String_OldIterator_next___main(x_1);
x_45 = l_String_splitAux___main___closed__1;
x_46 = lean::string_push(x_45, x_42);
x_47 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser___spec__4(x_46, x_0, x_44, x_2);
x_48 = lean::cnstr_get(x_47, 0);
x_50 = lean::cnstr_get(x_47, 1);
if (lean::is_exclusive(x_47)) {
 x_52 = x_47;
} else {
 lean::inc(x_48);
 lean::inc(x_50);
 lean::dec(x_47);
 x_52 = lean::box(0);
}
x_53 = lean::box(0);
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_53, x_48);
if (lean::is_scalar(x_52)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_52;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_50);
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_67; obj* x_69; obj* x_70; obj* x_71; 
x_56 = l_Char_quoteCore(x_42);
x_57 = l_Char_HasRepr___closed__1;
x_58 = lean::string_append(x_57, x_56);
lean::dec(x_56);
x_60 = lean::string_append(x_58, x_57);
x_61 = lean::box(0);
x_62 = l_mjoin___rarg___closed__1;
x_63 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_60, x_62, x_61, x_61, x_0, x_1, x_2);
lean::dec(x_1);
x_65 = lean::cnstr_get(x_63, 0);
x_67 = lean::cnstr_get(x_63, 1);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_set(x_63, 0, lean::box(0));
 lean::cnstr_set(x_63, 1, lean::box(0));
 x_69 = x_63;
} else {
 lean::inc(x_65);
 lean::inc(x_67);
 lean::dec(x_63);
 x_69 = lean::box(0);
}
x_70 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_71 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_70, x_65);
if (lean::obj_tag(x_71) == 0)
{
obj* x_73; obj* x_75; obj* x_77; obj* x_80; uint32 x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_86; obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_69);
x_73 = lean::cnstr_get(x_71, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_71, 1);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_71, 2);
lean::inc(x_77);
lean::dec(x_71);
x_80 = l_String_splitAux___main___closed__1;
x_81 = lean::unbox_uint32(x_73);
x_82 = lean::string_push(x_80, x_81);
x_83 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser___spec__6(x_82, x_0, x_75, x_67);
x_84 = lean::cnstr_get(x_83, 0);
x_86 = lean::cnstr_get(x_83, 1);
if (lean::is_exclusive(x_83)) {
 x_88 = x_83;
} else {
 lean::inc(x_84);
 lean::inc(x_86);
 lean::dec(x_83);
 x_88 = lean::box(0);
}
x_89 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_77, x_84);
if (lean::is_scalar(x_88)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_88;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_86);
return x_90;
}
else
{
obj* x_91; uint8 x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_91 = lean::cnstr_get(x_71, 0);
x_93 = lean::cnstr_get_scalar<uint8>(x_71, sizeof(void*)*1);
if (lean::is_exclusive(x_71)) {
 x_94 = x_71;
} else {
 lean::inc(x_91);
 lean::dec(x_71);
 x_94 = lean::box(0);
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_91);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_93);
x_96 = x_95;
if (lean::is_scalar(x_69)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_69;
}
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_67);
return x_97;
}
}
}
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser___spec__9(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdRest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_OldIterator_next___main(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__8___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_String_OldIterator_remaining___main(x_0);
x_3 = l_String_splitAux___main___closed__1;
x_4 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser___spec__9(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__8(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__8___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser___spec__11(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdRest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_OldIterator_next___main(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__10___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_String_OldIterator_remaining___main(x_0);
x_3 = l_String_splitAux___main___closed__1;
x_4 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser___spec__11(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__10(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__10___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser___spec__13(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdRest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_OldIterator_next___main(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__12___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = l_String_OldIterator_remaining___main(x_0);
x_3 = l_String_splitAux___main___closed__1;
x_4 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser___spec__13(x_2, x_3, x_0);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_1);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__12(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__12___rarg), 2, 0);
return x_1;
}
}
obj* l_Lean_Parser_detailIdentPart_Parser___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser___spec__1(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 1);
x_12 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_14 = x_5;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
lean::inc(x_10);
x_16 = l_Lean_Parser_mkRawRes(x_0, x_10);
x_17 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_14)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_14;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_10);
lean::cnstr_set(x_18, 2, x_17);
x_19 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_18);
if (lean::is_scalar(x_9)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_9;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_7);
return x_20;
}
else
{
obj* x_22; obj* x_24; obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_0);
x_22 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_24 = x_4;
} else {
 lean::inc(x_22);
 lean::dec(x_4);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_5, 0);
x_27 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_28 = x_5;
} else {
 lean::inc(x_25);
 lean::dec(x_5);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_27);
x_30 = x_29;
if (lean::is_scalar(x_24)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_24;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_22);
return x_31;
}
}
}
obj* l_Lean_Parser_detailIdentPart_Parser___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_7; 
x_7 = l_String_OldIterator_hasNext___main(x_2);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_18; obj* x_19; 
x_8 = lean::box(0);
x_9 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_10 = l_mjoin___rarg___closed__1;
x_11 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_9, x_10, x_8, x_8, x_1, x_2, x_3);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_11, 1);
lean::inc(x_15);
lean::dec(x_11);
x_18 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_19 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_13);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; obj* x_22; obj* x_25; obj* x_26; obj* x_28; obj* x_31; 
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_19, 2);
lean::inc(x_22);
lean::dec(x_19);
x_25 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__8___rarg(x_20, x_15);
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
lean::dec(x_25);
x_31 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_26);
x_4 = x_31;
x_5 = x_28;
goto lbl_6;
}
else
{
obj* x_32; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; 
x_32 = lean::cnstr_get(x_19, 0);
x_34 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
if (lean::is_exclusive(x_19)) {
 x_35 = x_19;
} else {
 lean::inc(x_32);
 lean::dec(x_19);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_32);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_34);
x_37 = x_36;
x_4 = x_37;
x_5 = x_15;
goto lbl_6;
}
}
else
{
uint32 x_38; uint8 x_39; 
x_38 = l_String_OldIterator_curr___main(x_2);
x_39 = l_Lean_isIdFirst(x_38);
if (x_39 == 0)
{
obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_49; obj* x_51; obj* x_54; obj* x_55; 
x_40 = l_Char_quoteCore(x_38);
x_41 = l_Char_HasRepr___closed__1;
x_42 = lean::string_append(x_41, x_40);
lean::dec(x_40);
x_44 = lean::string_append(x_42, x_41);
x_45 = lean::box(0);
x_46 = l_mjoin___rarg___closed__1;
x_47 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_44, x_46, x_45, x_45, x_1, x_2, x_3);
lean::dec(x_2);
x_49 = lean::cnstr_get(x_47, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_47, 1);
lean::inc(x_51);
lean::dec(x_47);
x_54 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_55 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_54, x_49);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; obj* x_58; obj* x_61; obj* x_62; obj* x_64; obj* x_67; 
x_56 = lean::cnstr_get(x_55, 1);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_55, 2);
lean::inc(x_58);
lean::dec(x_55);
x_61 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__10___rarg(x_56, x_51);
x_62 = lean::cnstr_get(x_61, 0);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_61, 1);
lean::inc(x_64);
lean::dec(x_61);
x_67 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_62);
x_4 = x_67;
x_5 = x_64;
goto lbl_6;
}
else
{
obj* x_68; uint8 x_70; obj* x_71; obj* x_72; obj* x_73; 
x_68 = lean::cnstr_get(x_55, 0);
x_70 = lean::cnstr_get_scalar<uint8>(x_55, sizeof(void*)*1);
if (lean::is_exclusive(x_55)) {
 x_71 = x_55;
} else {
 lean::inc(x_68);
 lean::dec(x_55);
 x_71 = lean::box(0);
}
if (lean::is_scalar(x_71)) {
 x_72 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_72 = x_71;
}
lean::cnstr_set(x_72, 0, x_68);
lean::cnstr_set_scalar(x_72, sizeof(void*)*1, x_70);
x_73 = x_72;
x_4 = x_73;
x_5 = x_51;
goto lbl_6;
}
}
else
{
obj* x_74; obj* x_75; obj* x_76; obj* x_78; obj* x_81; obj* x_82; 
x_74 = l_String_OldIterator_next___main(x_2);
x_75 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__12___rarg(x_74, x_3);
x_76 = lean::cnstr_get(x_75, 0);
lean::inc(x_76);
x_78 = lean::cnstr_get(x_75, 1);
lean::inc(x_78);
lean::dec(x_75);
x_81 = lean::box(0);
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_81, x_76);
x_4 = x_82;
x_5 = x_78;
goto lbl_6;
}
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_83; obj* x_85; obj* x_87; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; 
x_83 = lean::cnstr_get(x_4, 1);
x_85 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_87 = x_4;
} else {
 lean::inc(x_83);
 lean::inc(x_85);
 lean::dec(x_4);
 x_87 = lean::box(0);
}
lean::inc(x_83);
x_89 = l_Lean_Parser_mkRawRes(x_0, x_83);
x_90 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_87)) {
 x_91 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_91 = x_87;
}
lean::cnstr_set(x_91, 0, x_89);
lean::cnstr_set(x_91, 1, x_83);
lean::cnstr_set(x_91, 2, x_90);
x_92 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_85, x_91);
x_93 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_93, 0, x_92);
lean::cnstr_set(x_93, 1, x_5);
return x_93;
}
else
{
obj* x_95; uint8 x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
lean::dec(x_0);
x_95 = lean::cnstr_get(x_4, 0);
x_97 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_98 = x_4;
} else {
 lean::inc(x_95);
 lean::dec(x_4);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_95);
lean::cnstr_set_scalar(x_99, sizeof(void*)*1, x_97);
x_100 = x_99;
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_5);
return x_101;
}
}
}
}
obj* _init_l_Lean_Parser_detailIdentPart_Parser___closed__1() {
_start:
{
obj* x_0; uint32 x_1; obj* x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_14; uint32 x_15; obj* x_16; obj* x_18; obj* x_19; obj* x_20; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_0 = lean::mk_string("");
x_1 = l_Lean_idBeginEscape;
lean::inc(x_0);
x_3 = lean::string_push(x_0, x_1);
lean::inc(x_3);
x_5 = l_String_quote(x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_8, 0, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__1___boxed), 6, 2);
lean::closure_set(x_9, 0, x_3);
lean::closure_set(x_9, 1, x_6);
lean::inc(x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_11, 0, x_8);
lean::closure_set(x_11, 1, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPart_Parser___lambda__1___boxed), 4, 0);
lean::inc(x_8);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_14, 0, x_8);
lean::closure_set(x_14, 1, x_12);
x_15 = l_Lean_idEndEscape;
x_16 = lean::string_push(x_0, x_15);
lean::inc(x_16);
x_18 = l_String_quote(x_16);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_19, 0, x_18);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__1___boxed), 6, 2);
lean::closure_set(x_20, 0, x_16);
lean::closure_set(x_20, 1, x_19);
lean::inc(x_8);
x_22 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_22, 0, x_8);
lean::closure_set(x_22, 1, x_20);
x_23 = lean::box(0);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_14);
lean::cnstr_set(x_25, 1, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_11);
lean::cnstr_set(x_26, 1, x_25);
x_27 = l_Lean_Parser_detailIdentPartEscaped;
x_28 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__15), 5, 2);
lean::closure_set(x_28, 0, x_27);
lean::closure_set(x_28, 1, x_26);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPart_Parser___lambda__2___boxed), 4, 0);
x_30 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_30, 0, x_8);
lean::closure_set(x_30, 1, x_29);
x_31 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_23);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_28);
lean::cnstr_set(x_32, 1, x_31);
x_33 = lean::mk_nat_obj(0u);
x_34 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__29), 5, 2);
lean::closure_set(x_34, 0, x_32);
lean::closure_set(x_34, 1, x_33);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_23);
return x_35;
}
}
obj* l_Lean_Parser_detailIdentPart_Parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_Parser_detailIdentPart;
x_4 = l_Lean_Parser_detailIdentPart_Parser___closed__1;
x_5 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__15(x_3, x_4, x_0, x_1, x_2);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser___spec__6(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__8___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__8(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__10___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__10(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__12___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser___spec__12(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_detailIdentPart_Parser___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_detailIdentPart_Parser___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_detailIdentPart_Parser___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_detailIdentPart_Parser___lambda__2(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_Parser_detailIdentSuffix() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("detailIdentSuffix");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_detailIdentSuffix_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::box(3);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_Lean_Parser_detailIdentSuffix_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_detailIdentSuffix_HasView_x_27___lambda__1___closed__1;
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 x_5 = x_1;
} else {
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
if (lean::obj_tag(x_6) == 0)
{
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
x_10 = l_Lean_Parser_detailIdentSuffix_HasView_x_27___lambda__1___closed__1;
return x_10;
}
else
{
obj* x_11; obj* x_14; obj* x_15; 
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
lean::dec(x_6);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_11);
return x_15;
}
}
else
{
obj* x_16; 
x_16 = lean::cnstr_get(x_6, 0);
lean::inc(x_16);
switch (lean::obj_tag(x_16)) {
case 0:
{
obj* x_18; obj* x_21; obj* x_24; 
x_18 = lean::cnstr_get(x_6, 1);
lean::inc(x_18);
lean::dec(x_6);
x_21 = lean::cnstr_get(x_16, 0);
lean::inc(x_21);
lean::dec(x_16);
if (lean::is_scalar(x_5)) {
 x_24 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_24 = x_5;
}
lean::cnstr_set(x_24, 0, x_21);
if (lean::obj_tag(x_18) == 0)
{
obj* x_25; obj* x_26; 
x_25 = lean::box(3);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
else
{
obj* x_27; obj* x_30; 
x_27 = lean::cnstr_get(x_18, 0);
lean::inc(x_27);
lean::dec(x_18);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_24);
lean::cnstr_set(x_30, 1, x_27);
return x_30;
}
}
case 3:
{
obj* x_32; 
lean::dec(x_5);
x_32 = lean::cnstr_get(x_6, 1);
lean::inc(x_32);
lean::dec(x_6);
if (lean::obj_tag(x_32) == 0)
{
obj* x_35; 
x_35 = l_Lean_Parser_detailIdentSuffix_HasView_x_27___lambda__1___closed__1;
return x_35;
}
else
{
obj* x_36; obj* x_39; obj* x_40; 
x_36 = lean::cnstr_get(x_32, 0);
lean::inc(x_36);
lean::dec(x_32);
x_39 = lean::box(0);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_36);
return x_40;
}
}
default:
{
obj* x_43; 
lean::dec(x_5);
lean::dec(x_16);
x_43 = lean::cnstr_get(x_6, 1);
lean::inc(x_43);
lean::dec(x_6);
if (lean::obj_tag(x_43) == 0)
{
obj* x_46; 
x_46 = l_Lean_Parser_detailIdentSuffix_HasView_x_27___lambda__1___closed__1;
return x_46;
}
else
{
obj* x_47; obj* x_50; obj* x_51; 
x_47 = lean::cnstr_get(x_43, 0);
lean::inc(x_47);
lean::dec(x_43);
x_50 = lean::box(0);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_47);
return x_51;
}
}
}
}
}
}
}
obj* l_Lean_Parser_detailIdentSuffix_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_3);
lean::cnstr_set(x_7, 1, x_6);
if (lean::obj_tag(x_1) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = l_Lean_Parser_raw_view___rarg___lambda__2___closed__1;
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_7);
x_10 = l_Lean_Parser_detailIdentSuffix;
x_11 = l_Lean_Parser_Syntax_mkNode(x_10, x_9);
return x_11;
}
else
{
obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; obj* x_22; 
x_12 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 x_14 = x_1;
} else {
 lean::inc(x_12);
 lean::dec(x_1);
 x_14 = lean::box(0);
}
x_15 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_15, 0, x_12);
if (lean::is_scalar(x_14)) {
 x_16 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_16 = x_14;
}
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::box(3);
x_18 = l_Option_getOrElse___main___rarg(x_16, x_17);
lean::dec(x_16);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_7);
x_21 = l_Lean_Parser_detailIdentSuffix;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
}
}
obj* _init_l_Lean_Parser_detailIdentSuffix_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentSuffix_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentSuffix_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_detailIdentSuffix_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_detailIdentSuffix_HasView_x_27;
return x_0;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_13; 
x_8 = l_Option_getOrElse___main___rarg(x_2, x_6);
x_9 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_0);
lean::cnstr_set(x_9, 2, x_1);
lean::cnstr_set(x_9, 3, x_3);
x_10 = 0;
x_11 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set_scalar(x_11, sizeof(void*)*1, x_10);
x_12 = x_11;
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_7);
return x_13;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg___boxed), 8, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1(uint32 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_6 = lean::box(0);
x_7 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_8 = l_mjoin___rarg___closed__1;
x_9 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_7, x_8, x_6, x_6, x_1, x_2, x_3, x_4);
lean::dec(x_3);
x_11 = lean::cnstr_get(x_9, 0);
x_13 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 x_15 = x_9;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_9);
 x_15 = lean::box(0);
}
x_16 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_17 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_11);
if (lean::is_scalar(x_15)) {
 x_18 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_18 = x_15;
}
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_13);
return x_18;
}
else
{
uint32 x_19; uint8 x_20; 
x_19 = l_String_OldIterator_curr___main(x_3);
x_20 = x_19 == x_0;
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_21 = l_Char_quoteCore(x_19);
x_22 = l_Char_HasRepr___closed__1;
x_23 = lean::string_append(x_22, x_21);
lean::dec(x_21);
x_25 = lean::string_append(x_23, x_22);
x_26 = lean::box(0);
x_27 = l_mjoin___rarg___closed__1;
x_28 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_25, x_27, x_26, x_26, x_1, x_2, x_3, x_4);
lean::dec(x_3);
x_30 = lean::cnstr_get(x_28, 0);
x_32 = lean::cnstr_get(x_28, 1);
if (lean::is_exclusive(x_28)) {
 x_34 = x_28;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::dec(x_28);
 x_34 = lean::box(0);
}
x_35 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_36 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_35, x_30);
if (lean::is_scalar(x_34)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_34;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_32);
return x_37;
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_38 = l_String_OldIterator_next___main(x_3);
x_39 = lean::box(0);
x_40 = lean::box_uint32(x_19);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_38);
lean::cnstr_set(x_41, 2, x_39);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_4);
return x_42;
}
}
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__3(uint32 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_9; obj* x_10; 
lean::inc(x_3);
x_9 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1(x_0, x_1, x_2, x_3, x_4);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_15; obj* x_17; obj* x_19; uint32 x_20; obj* x_22; obj* x_23; 
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::cnstr_get(x_10, 1);
x_17 = lean::cnstr_get(x_10, 2);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_set(x_10, 1, lean::box(0));
 lean::cnstr_set(x_10, 2, lean::box(0));
 x_19 = x_10;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_10);
 x_19 = lean::box(0);
}
x_20 = l_Lean_idBeginEscape;
lean::inc(x_15);
x_22 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1(x_20, x_1, x_2, x_15, x_12);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_27; obj* x_30; 
lean::dec(x_15);
lean::dec(x_19);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
lean::dec(x_22);
x_30 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_23);
x_5 = x_30;
x_6 = x_27;
goto lbl_7;
}
else
{
uint8 x_31; 
x_31 = lean::cnstr_get_scalar<uint8>(x_23, sizeof(void*)*1);
if (x_31 == 0)
{
obj* x_32; obj* x_35; uint8 x_38; 
x_32 = lean::cnstr_get(x_22, 1);
lean::inc(x_32);
lean::dec(x_22);
x_35 = lean::cnstr_get(x_23, 0);
lean::inc(x_35);
lean::dec(x_23);
x_38 = l_String_OldIterator_hasNext___main(x_15);
if (x_38 == 0)
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_19);
x_40 = lean::box(0);
x_41 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_42 = l_mjoin___rarg___closed__1;
x_43 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_41, x_42, x_40, x_40, x_1, x_2, x_15, x_32);
lean::dec(x_15);
x_45 = lean::cnstr_get(x_43, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_43, 1);
lean::inc(x_47);
lean::dec(x_43);
x_50 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_51 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_50, x_45);
x_52 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_35, x_51);
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_52);
x_5 = x_53;
x_6 = x_47;
goto lbl_7;
}
else
{
uint32 x_54; uint8 x_55; 
x_54 = l_String_OldIterator_curr___main(x_15);
x_55 = l_Lean_isIdFirst(x_54);
if (x_55 == 0)
{
obj* x_57; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_66; obj* x_68; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_19);
x_57 = l_Char_quoteCore(x_54);
x_58 = l_Char_HasRepr___closed__1;
x_59 = lean::string_append(x_58, x_57);
lean::dec(x_57);
x_61 = lean::string_append(x_59, x_58);
x_62 = lean::box(0);
x_63 = l_mjoin___rarg___closed__1;
x_64 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_61, x_63, x_62, x_62, x_1, x_2, x_15, x_32);
lean::dec(x_15);
x_66 = lean::cnstr_get(x_64, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_64, 1);
lean::inc(x_68);
lean::dec(x_64);
x_71 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_72 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_71, x_66);
x_73 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_35, x_72);
x_74 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_73);
x_5 = x_74;
x_6 = x_68;
goto lbl_7;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_35);
x_76 = l_String_OldIterator_next___main(x_15);
x_77 = lean::box(0);
x_78 = lean::box_uint32(x_54);
if (lean::is_scalar(x_19)) {
 x_79 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_79 = x_19;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_76);
lean::cnstr_set(x_79, 2, x_77);
x_80 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_79);
x_5 = x_80;
x_6 = x_32;
goto lbl_7;
}
}
}
else
{
obj* x_83; obj* x_86; 
lean::dec(x_15);
lean::dec(x_19);
x_83 = lean::cnstr_get(x_22, 1);
lean::inc(x_83);
lean::dec(x_22);
x_86 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_23);
x_5 = x_86;
x_6 = x_83;
goto lbl_7;
}
}
}
else
{
obj* x_87; obj* x_90; uint8 x_92; obj* x_93; obj* x_94; obj* x_95; 
x_87 = lean::cnstr_get(x_9, 1);
lean::inc(x_87);
lean::dec(x_9);
x_90 = lean::cnstr_get(x_10, 0);
x_92 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 x_93 = x_10;
} else {
 lean::inc(x_90);
 lean::dec(x_10);
 x_93 = lean::box(0);
}
if (lean::is_scalar(x_93)) {
 x_94 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_94 = x_93;
}
lean::cnstr_set(x_94, 0, x_90);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_92);
x_95 = x_94;
x_5 = x_95;
x_6 = x_87;
goto lbl_7;
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_96; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_96 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_98 = x_5;
} else {
 lean::inc(x_96);
 lean::dec(x_5);
 x_98 = lean::box(0);
}
x_99 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_98)) {
 x_100 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_100 = x_98;
}
lean::cnstr_set(x_100, 0, x_96);
lean::cnstr_set(x_100, 1, x_3);
lean::cnstr_set(x_100, 2, x_99);
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_6);
return x_101;
}
else
{
obj* x_103; 
lean::dec(x_3);
x_103 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_103, 0, x_5);
lean::cnstr_set(x_103, 1, x_6);
return x_103;
}
}
}
}
obj* l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::apply_3(x_0, x_2, x_3, x_4);
return x_5;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__5(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = l_String_isEmpty(x_0);
if (x_6 == 0)
{
obj* x_7; obj* x_8; usize x_9; obj* x_11; obj* x_12; obj* x_14; 
x_7 = lean::string_length(x_0);
x_8 = lean::mk_nat_obj(0u);
x_9 = l_String_toSubstring___closed__1;
lean::inc(x_0);
x_11 = lean::alloc_cnstr(0, 2, sizeof(size_t)*1);
lean::cnstr_set(x_11, 0, x_0);
lean::cnstr_set(x_11, 1, x_8);
lean::cnstr_set_scalar(x_11, sizeof(void*)*2, x_9);
x_12 = x_11;
lean::inc(x_4);
x_14 = l___private_init_lean_parser_parsec_2__strAux___main(x_7, x_12, x_4);
if (lean::obj_tag(x_14) == 0)
{
obj* x_16; obj* x_17; obj* x_18; uint8 x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::dec(x_0);
x_16 = lean::box(0);
x_17 = l_String_splitAux___main___closed__1;
x_18 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_18, 0, x_4);
lean::cnstr_set(x_18, 1, x_17);
lean::cnstr_set(x_18, 2, x_1);
lean::cnstr_set(x_18, 3, x_16);
x_19 = 0;
x_20 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set_scalar(x_20, sizeof(void*)*1, x_19);
x_21 = x_20;
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_5);
return x_22;
}
else
{
obj* x_25; obj* x_28; obj* x_29; obj* x_30; 
lean::dec(x_4);
lean::dec(x_1);
x_25 = lean::cnstr_get(x_14, 0);
lean::inc(x_25);
lean::dec(x_14);
x_28 = lean::box(0);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_0);
lean::cnstr_set(x_29, 1, x_25);
lean::cnstr_set(x_29, 2, x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_5);
return x_30;
}
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_1);
lean::dec(x_0);
x_33 = l_String_splitAux___main___closed__1;
x_34 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_35 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_4);
lean::cnstr_set(x_35, 2, x_34);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_5);
return x_36;
}
}
}
obj* l_ReaderT_bind___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__6___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_8; obj* x_9; 
lean::inc(x_3);
lean::inc(x_2);
x_8 = lean::apply_4(x_0, x_2, x_3, x_4, x_5);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_14; obj* x_16; obj* x_18; obj* x_21; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_28; 
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_14 = lean::cnstr_get(x_9, 0);
lean::inc(x_14);
x_16 = lean::cnstr_get(x_9, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_9, 2);
lean::inc(x_18);
lean::dec(x_9);
x_21 = lean::apply_5(x_1, x_14, x_2, x_3, x_16, x_11);
x_22 = lean::cnstr_get(x_21, 0);
x_24 = lean::cnstr_get(x_21, 1);
if (lean::is_exclusive(x_21)) {
 x_26 = x_21;
} else {
 lean::inc(x_22);
 lean::inc(x_24);
 lean::dec(x_21);
 x_26 = lean::box(0);
}
x_27 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_22);
if (lean::is_scalar(x_26)) {
 x_28 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_28 = x_26;
}
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_24);
return x_28;
}
else
{
obj* x_32; obj* x_34; obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_32 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_34 = x_8;
} else {
 lean::inc(x_32);
 lean::dec(x_8);
 x_34 = lean::box(0);
}
x_35 = lean::cnstr_get(x_9, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_38 = x_9;
} else {
 lean::inc(x_35);
 lean::dec(x_9);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_35);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_37);
x_40 = x_39;
if (lean::is_scalar(x_34)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_34;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_32);
return x_41;
}
}
}
obj* l_ReaderT_bind___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__6(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__6___rarg), 6, 0);
return x_2;
}
}
obj* l_Lean_Parser_RecT_recurse___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__7(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::apply_4(x_1, x_0, x_2, x_3, x_4);
return x_5;
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__9(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_10 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_1);
lean::cnstr_set(x_11, 1, x_5);
lean::cnstr_set(x_11, 2, x_10);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_6);
return x_12;
}
else
{
obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_23; obj* x_24; 
x_13 = lean::cnstr_get(x_2, 0);
x_15 = lean::cnstr_get(x_2, 1);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 x_17 = x_2;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_2);
 x_17 = lean::box(0);
}
lean::inc(x_4);
lean::inc(x_3);
x_23 = lean::apply_4(x_13, x_3, x_4, x_5, x_6);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_26; 
x_26 = lean::cnstr_get(x_23, 1);
lean::inc(x_26);
lean::dec(x_23);
x_18 = x_24;
x_19 = x_26;
goto lbl_20;
}
else
{
uint8 x_29; 
x_29 = lean::cnstr_get_scalar<uint8>(x_24, sizeof(void*)*1);
if (lean::obj_tag(x_1) == 0)
{
if (x_29 == 0)
{
obj* x_30; obj* x_33; obj* x_35; uint8 x_36; obj* x_37; obj* x_38; 
x_30 = lean::cnstr_get(x_23, 1);
lean::inc(x_30);
lean::dec(x_23);
x_33 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_35 = x_24;
} else {
 lean::inc(x_33);
 lean::dec(x_24);
 x_35 = lean::box(0);
}
x_36 = 0;
if (lean::is_scalar(x_35)) {
 x_37 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_37 = x_35;
}
lean::cnstr_set(x_37, 0, x_33);
lean::cnstr_set_scalar(x_37, sizeof(void*)*1, x_36);
x_38 = x_37;
x_18 = x_38;
x_19 = x_30;
goto lbl_20;
}
else
{
obj* x_39; obj* x_42; obj* x_44; uint8 x_45; obj* x_46; obj* x_47; 
x_39 = lean::cnstr_get(x_23, 1);
lean::inc(x_39);
lean::dec(x_23);
x_42 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 x_44 = x_24;
} else {
 lean::inc(x_42);
 lean::dec(x_24);
 x_44 = lean::box(0);
}
x_45 = 1;
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_42);
lean::cnstr_set_scalar(x_46, sizeof(void*)*1, x_45);
x_47 = x_46;
x_18 = x_47;
x_19 = x_39;
goto lbl_20;
}
}
else
{
obj* x_48; obj* x_51; obj* x_53; obj* x_54; obj* x_56; obj* x_59; obj* x_60; obj* x_62; obj* x_64; obj* x_67; obj* x_69; obj* x_70; obj* x_71; 
x_48 = lean::cnstr_get(x_23, 1);
lean::inc(x_48);
lean::dec(x_23);
x_51 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_set(x_24, 0, lean::box(0));
 x_53 = x_24;
} else {
 lean::inc(x_51);
 lean::dec(x_24);
 x_53 = lean::box(0);
}
x_54 = lean::cnstr_get(x_51, 3);
lean::inc(x_54);
x_56 = l_Option_get___main___at_Lean_Parser_run___spec__2(x_54);
lean::dec(x_54);
lean::inc(x_1);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_56);
lean::cnstr_set(x_59, 1, x_1);
x_60 = lean::cnstr_get(x_51, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_51, 1);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_51, 2);
lean::inc(x_64);
lean::dec(x_51);
x_67 = l_List_reverse___rarg(x_59);
lean::inc(x_0);
x_69 = l_Lean_Parser_Syntax_mkNode(x_0, x_67);
x_70 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_70, 0, x_69);
x_71 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_71, 0, x_60);
lean::cnstr_set(x_71, 1, x_62);
lean::cnstr_set(x_71, 2, x_64);
lean::cnstr_set(x_71, 3, x_70);
if (x_29 == 0)
{
uint8 x_72; obj* x_73; obj* x_74; 
x_72 = 0;
if (lean::is_scalar(x_53)) {
 x_73 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_73 = x_53;
}
lean::cnstr_set(x_73, 0, x_71);
lean::cnstr_set_scalar(x_73, sizeof(void*)*1, x_72);
x_74 = x_73;
x_18 = x_74;
x_19 = x_48;
goto lbl_20;
}
else
{
uint8 x_75; obj* x_76; obj* x_77; 
x_75 = 1;
if (lean::is_scalar(x_53)) {
 x_76 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_76 = x_53;
}
lean::cnstr_set(x_76, 0, x_71);
lean::cnstr_set_scalar(x_76, sizeof(void*)*1, x_75);
x_77 = x_76;
x_18 = x_77;
x_19 = x_48;
goto lbl_20;
}
}
}
lbl_20:
{
if (lean::obj_tag(x_18) == 0)
{
obj* x_78; obj* x_80; obj* x_82; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_78 = lean::cnstr_get(x_18, 0);
x_80 = lean::cnstr_get(x_18, 1);
x_82 = lean::cnstr_get(x_18, 2);
if (lean::is_exclusive(x_18)) {
 x_84 = x_18;
} else {
 lean::inc(x_78);
 lean::inc(x_80);
 lean::inc(x_82);
 lean::dec(x_18);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_17)) {
 x_85 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_85 = x_17;
}
lean::cnstr_set(x_85, 0, x_78);
lean::cnstr_set(x_85, 1, x_1);
x_86 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_84)) {
 x_87 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_87 = x_84;
}
lean::cnstr_set(x_87, 0, x_85);
lean::cnstr_set(x_87, 1, x_80);
lean::cnstr_set(x_87, 2, x_86);
x_88 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_82, x_87);
if (lean::obj_tag(x_88) == 0)
{
obj* x_89; obj* x_91; obj* x_93; obj* x_96; obj* x_97; obj* x_99; obj* x_101; obj* x_102; obj* x_103; 
x_89 = lean::cnstr_get(x_88, 0);
lean::inc(x_89);
x_91 = lean::cnstr_get(x_88, 1);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_88, 2);
lean::inc(x_93);
lean::dec(x_88);
x_96 = l_List_mfoldl___main___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__9(x_0, x_89, x_15, x_3, x_4, x_91, x_19);
x_97 = lean::cnstr_get(x_96, 0);
x_99 = lean::cnstr_get(x_96, 1);
if (lean::is_exclusive(x_96)) {
 x_101 = x_96;
} else {
 lean::inc(x_97);
 lean::inc(x_99);
 lean::dec(x_96);
 x_101 = lean::box(0);
}
x_102 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_93, x_97);
if (lean::is_scalar(x_101)) {
 x_103 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_103 = x_101;
}
lean::cnstr_set(x_103, 0, x_102);
lean::cnstr_set(x_103, 1, x_99);
return x_103;
}
else
{
obj* x_108; uint8 x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
lean::dec(x_15);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_108 = lean::cnstr_get(x_88, 0);
x_110 = lean::cnstr_get_scalar<uint8>(x_88, sizeof(void*)*1);
if (lean::is_exclusive(x_88)) {
 x_111 = x_88;
} else {
 lean::inc(x_108);
 lean::dec(x_88);
 x_111 = lean::box(0);
}
if (lean::is_scalar(x_111)) {
 x_112 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_112 = x_111;
}
lean::cnstr_set(x_112, 0, x_108);
lean::cnstr_set_scalar(x_112, sizeof(void*)*1, x_110);
x_113 = x_112;
x_114 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_19);
return x_114;
}
}
else
{
obj* x_121; uint8 x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; 
lean::dec(x_15);
lean::dec(x_4);
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_17);
x_121 = lean::cnstr_get(x_18, 0);
x_123 = lean::cnstr_get_scalar<uint8>(x_18, sizeof(void*)*1);
if (lean::is_exclusive(x_18)) {
 x_124 = x_18;
} else {
 lean::inc(x_121);
 lean::dec(x_18);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_124)) {
 x_125 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_125 = x_124;
}
lean::cnstr_set(x_125, 0, x_121);
lean::cnstr_set_scalar(x_125, sizeof(void*)*1, x_123);
x_126 = x_125;
x_127 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_127, 0, x_126);
lean::cnstr_set(x_127, 1, x_19);
return x_127;
}
}
}
}
}
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_8; obj* x_9; 
x_6 = lean::box(0);
lean::inc(x_0);
x_8 = l_List_mfoldl___main___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__9(x_0, x_6, x_1, x_2, x_3, x_4, x_5);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_11 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_13 = x_8;
} else {
 lean::inc(x_11);
 lean::dec(x_8);
 x_13 = lean::box(0);
}
x_14 = lean::cnstr_get(x_9, 0);
x_16 = lean::cnstr_get(x_9, 1);
x_18 = lean::cnstr_get(x_9, 2);
if (lean::is_exclusive(x_9)) {
 x_20 = x_9;
} else {
 lean::inc(x_14);
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_9);
 x_20 = lean::box(0);
}
x_21 = l_List_reverse___rarg(x_14);
x_22 = l_Lean_Parser_Syntax_mkNode(x_0, x_21);
x_23 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_20)) {
 x_24 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_24 = x_20;
}
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_16);
lean::cnstr_set(x_24, 2, x_23);
x_25 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_24);
if (lean::is_scalar(x_13)) {
 x_26 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_26 = x_13;
}
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_11);
return x_26;
}
else
{
obj* x_28; obj* x_30; obj* x_31; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
lean::dec(x_0);
x_28 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_30 = x_8;
} else {
 lean::inc(x_28);
 lean::dec(x_8);
 x_30 = lean::box(0);
}
x_31 = lean::cnstr_get(x_9, 0);
x_33 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_34 = x_9;
} else {
 lean::inc(x_31);
 lean::dec(x_9);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_31);
lean::cnstr_set_scalar(x_35, sizeof(void*)*1, x_33);
x_36 = x_35;
if (lean::is_scalar(x_30)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_30;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_28);
return x_37;
}
}
}
obj* _init_l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_6; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_List_cons_tokens___rarg(x_0, x_0);
x_2 = l_Lean_Parser_List_cons_tokens___rarg(x_0, x_1);
lean::dec(x_1);
x_4 = l_Lean_Parser_tokens___rarg(x_2);
lean::dec(x_2);
x_6 = l_Lean_Parser_tokens___rarg(x_4);
lean::dec(x_4);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_0, x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_2);
lean::dec(x_4);
lean::dec(x_5);
lean::dec(x_6);
return x_8;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_0);
x_6 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1(x_5, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_0);
x_6 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__3(x_5, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__5(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_3);
return x_6;
}
}
obj* l_ReaderT_bind___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__6___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_ReaderT_bind___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__6(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___spec__1(uint32 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_9; obj* x_10; 
lean::inc(x_3);
x_9 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1(x_0, x_1, x_2, x_3, x_4);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_15; obj* x_17; obj* x_19; uint32 x_20; obj* x_22; obj* x_23; 
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::cnstr_get(x_10, 1);
x_17 = lean::cnstr_get(x_10, 2);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_set(x_10, 1, lean::box(0));
 lean::cnstr_set(x_10, 2, lean::box(0));
 x_19 = x_10;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_10);
 x_19 = lean::box(0);
}
x_20 = l_Lean_idBeginEscape;
lean::inc(x_15);
x_22 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1(x_20, x_1, x_2, x_15, x_12);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_27; obj* x_30; 
lean::dec(x_15);
lean::dec(x_19);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
lean::dec(x_22);
x_30 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_23);
x_5 = x_30;
x_6 = x_27;
goto lbl_7;
}
else
{
uint8 x_31; 
x_31 = lean::cnstr_get_scalar<uint8>(x_23, sizeof(void*)*1);
if (x_31 == 0)
{
obj* x_32; obj* x_35; uint8 x_38; 
x_32 = lean::cnstr_get(x_22, 1);
lean::inc(x_32);
lean::dec(x_22);
x_35 = lean::cnstr_get(x_23, 0);
lean::inc(x_35);
lean::dec(x_23);
x_38 = l_String_OldIterator_hasNext___main(x_15);
if (x_38 == 0)
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_19);
x_40 = lean::box(0);
x_41 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_42 = l_mjoin___rarg___closed__1;
x_43 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_41, x_42, x_40, x_40, x_1, x_2, x_15, x_32);
lean::dec(x_15);
x_45 = lean::cnstr_get(x_43, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_43, 1);
lean::inc(x_47);
lean::dec(x_43);
x_50 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_51 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_50, x_45);
x_52 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_35, x_51);
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_52);
x_5 = x_53;
x_6 = x_47;
goto lbl_7;
}
else
{
uint32 x_54; uint8 x_55; 
x_54 = l_String_OldIterator_curr___main(x_15);
x_55 = l_Lean_isIdFirst(x_54);
if (x_55 == 0)
{
obj* x_57; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_66; obj* x_68; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_19);
x_57 = l_Char_quoteCore(x_54);
x_58 = l_Char_HasRepr___closed__1;
x_59 = lean::string_append(x_58, x_57);
lean::dec(x_57);
x_61 = lean::string_append(x_59, x_58);
x_62 = lean::box(0);
x_63 = l_mjoin___rarg___closed__1;
x_64 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_61, x_63, x_62, x_62, x_1, x_2, x_15, x_32);
lean::dec(x_15);
x_66 = lean::cnstr_get(x_64, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_64, 1);
lean::inc(x_68);
lean::dec(x_64);
x_71 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_72 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_71, x_66);
x_73 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_35, x_72);
x_74 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_73);
x_5 = x_74;
x_6 = x_68;
goto lbl_7;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_35);
x_76 = l_String_OldIterator_next___main(x_15);
x_77 = lean::box(0);
x_78 = lean::box_uint32(x_54);
if (lean::is_scalar(x_19)) {
 x_79 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_79 = x_19;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_76);
lean::cnstr_set(x_79, 2, x_77);
x_80 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_79);
x_5 = x_80;
x_6 = x_32;
goto lbl_7;
}
}
}
else
{
obj* x_83; obj* x_86; 
lean::dec(x_15);
lean::dec(x_19);
x_83 = lean::cnstr_get(x_22, 1);
lean::inc(x_83);
lean::dec(x_22);
x_86 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_23);
x_5 = x_86;
x_6 = x_83;
goto lbl_7;
}
}
}
else
{
obj* x_87; obj* x_90; uint8 x_92; obj* x_93; obj* x_94; obj* x_95; 
x_87 = lean::cnstr_get(x_9, 1);
lean::inc(x_87);
lean::dec(x_9);
x_90 = lean::cnstr_get(x_10, 0);
x_92 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 x_93 = x_10;
} else {
 lean::inc(x_90);
 lean::dec(x_10);
 x_93 = lean::box(0);
}
if (lean::is_scalar(x_93)) {
 x_94 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_94 = x_93;
}
lean::cnstr_set(x_94, 0, x_90);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_92);
x_95 = x_94;
x_5 = x_95;
x_6 = x_87;
goto lbl_7;
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_96; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_96 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_98 = x_5;
} else {
 lean::inc(x_96);
 lean::dec(x_5);
 x_98 = lean::box(0);
}
x_99 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_98)) {
 x_100 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_100 = x_98;
}
lean::cnstr_set(x_100, 0, x_96);
lean::cnstr_set(x_100, 1, x_3);
lean::cnstr_set(x_100, 2, x_99);
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_6);
return x_101;
}
else
{
obj* x_103; 
lean::dec(x_3);
x_103 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_103, 0, x_5);
lean::cnstr_set(x_103, 1, x_6);
return x_103;
}
}
}
}
obj* l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__1(uint32 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; 
x_5 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___spec__1(x_0, x_1, x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
x_8 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 x_10 = x_5;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_5);
 x_10 = lean::box(0);
}
x_11 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_6);
if (lean::is_scalar(x_10)) {
 x_12 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_12 = x_10;
}
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_8);
return x_12;
}
}
obj* l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = l_Lean_Name_toString___closed__1;
x_7 = l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__5(x_6, x_0, x_2, x_3, x_4, x_5);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_10 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_12 = x_7;
} else {
 lean::inc(x_10);
 lean::dec(x_7);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_8, 1);
x_15 = lean::cnstr_get(x_8, 2);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_17 = x_8;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::dec(x_8);
 x_17 = lean::box(0);
}
lean::inc(x_13);
x_19 = l_Lean_Parser_mkRawRes(x_1, x_13);
x_20 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_17)) {
 x_21 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_21 = x_17;
}
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_13);
lean::cnstr_set(x_21, 2, x_20);
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_21);
if (lean::is_scalar(x_12)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_12;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_10);
return x_23;
}
else
{
obj* x_25; obj* x_27; obj* x_28; uint8 x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_1);
x_25 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_27 = x_7;
} else {
 lean::inc(x_25);
 lean::dec(x_7);
 x_27 = lean::box(0);
}
x_28 = lean::cnstr_get(x_8, 0);
x_30 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_31 = x_8;
} else {
 lean::inc(x_28);
 lean::dec(x_8);
 x_31 = lean::box(0);
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_28);
lean::cnstr_set_scalar(x_32, sizeof(void*)*1, x_30);
x_33 = x_32;
if (lean::is_scalar(x_27)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_27;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_25);
return x_34;
}
}
}
obj* _init_l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint32 x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_33; 
x_0 = l_Lean_Parser_BasicParserM_Monad;
x_1 = l_ReaderT_Monad___rarg(x_0);
x_2 = l_Lean_Parser_BasicParserM_MonadExcept;
x_3 = l_ReaderT_MonadExcept___rarg(x_2);
x_4 = l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
x_5 = l_Lean_Parser_RecT_Lean_Parser_MonadParsec___rarg(x_0, lean::box(0), x_4);
x_6 = l_Lean_Parser_BasicParserM_Alternative;
x_7 = l_ReaderT_Alternative___rarg(x_0, x_6);
x_8 = 46;
x_9 = lean::box_uint32(x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__1___boxed), 5, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = lean::mk_string(".");
x_12 = l_String_quote(x_11);
x_13 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_13, 0, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_15, 0, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed), 5, 1);
lean::closure_set(x_16, 0, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__2___boxed), 6, 1);
lean::closure_set(x_17, 0, x_13);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__6___rarg), 6, 2);
lean::closure_set(x_18, 0, x_16);
lean::closure_set(x_18, 1, x_17);
x_19 = lean::box(0);
x_20 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_recurse___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__7), 5, 1);
lean::closure_set(x_20, 0, x_19);
x_21 = lean::box(0);
x_22 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_21);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_18);
lean::cnstr_set(x_23, 1, x_22);
x_24 = l_Lean_Parser_detailIdentSuffix;
lean::inc(x_23);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__8), 6, 2);
lean::closure_set(x_26, 0, x_24);
lean::closure_set(x_26, 1, x_23);
x_27 = l_Lean_Parser_detailIdentSuffix_HasView;
x_28 = l_Lean_Parser_Combinators_node_view___rarg(x_1, x_3, x_5, x_7, x_24, x_23, x_27);
lean::dec(x_23);
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_1);
x_33 = l_Lean_Parser_Combinators_seqRight_view___rarg(x_7, lean::box(0), lean::box(0), x_10, x_26, x_28);
lean::dec(x_26);
lean::dec(x_10);
lean::dec(x_7);
return x_33;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_0);
x_6 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___spec__1(x_5, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_0);
x_6 = l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__1(x_5, x_1, x_2, x_3, x_4);
lean::dec(x_1);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__2(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser___spec__1(obj* x_0, obj* x_1, uint32 x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_9; obj* x_10; 
lean::inc(x_3);
x_9 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1(x_2, x_0, x_1, x_3, x_4);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_15; obj* x_17; obj* x_19; uint32 x_20; obj* x_22; obj* x_23; 
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::cnstr_get(x_10, 1);
x_17 = lean::cnstr_get(x_10, 2);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_set(x_10, 1, lean::box(0));
 lean::cnstr_set(x_10, 2, lean::box(0));
 x_19 = x_10;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_10);
 x_19 = lean::box(0);
}
x_20 = l_Lean_idBeginEscape;
lean::inc(x_15);
x_22 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1(x_20, x_0, x_1, x_15, x_12);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_27; obj* x_30; 
lean::dec(x_15);
lean::dec(x_19);
x_27 = lean::cnstr_get(x_22, 1);
lean::inc(x_27);
lean::dec(x_22);
x_30 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_23);
x_5 = x_30;
x_6 = x_27;
goto lbl_7;
}
else
{
uint8 x_31; 
x_31 = lean::cnstr_get_scalar<uint8>(x_23, sizeof(void*)*1);
if (x_31 == 0)
{
obj* x_32; obj* x_35; uint8 x_38; 
x_32 = lean::cnstr_get(x_22, 1);
lean::inc(x_32);
lean::dec(x_22);
x_35 = lean::cnstr_get(x_23, 0);
lean::inc(x_35);
lean::dec(x_23);
x_38 = l_String_OldIterator_hasNext___main(x_15);
if (x_38 == 0)
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_45; obj* x_47; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_19);
x_40 = lean::box(0);
x_41 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_42 = l_mjoin___rarg___closed__1;
x_43 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_41, x_42, x_40, x_40, x_0, x_1, x_15, x_32);
lean::dec(x_15);
x_45 = lean::cnstr_get(x_43, 0);
lean::inc(x_45);
x_47 = lean::cnstr_get(x_43, 1);
lean::inc(x_47);
lean::dec(x_43);
x_50 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_51 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_50, x_45);
x_52 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_35, x_51);
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_52);
x_5 = x_53;
x_6 = x_47;
goto lbl_7;
}
else
{
uint32 x_54; uint8 x_55; 
x_54 = l_String_OldIterator_curr___main(x_15);
x_55 = l_Lean_isIdFirst(x_54);
if (x_55 == 0)
{
obj* x_57; obj* x_58; obj* x_59; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_66; obj* x_68; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_19);
x_57 = l_Char_quoteCore(x_54);
x_58 = l_Char_HasRepr___closed__1;
x_59 = lean::string_append(x_58, x_57);
lean::dec(x_57);
x_61 = lean::string_append(x_59, x_58);
x_62 = lean::box(0);
x_63 = l_mjoin___rarg___closed__1;
x_64 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_61, x_63, x_62, x_62, x_0, x_1, x_15, x_32);
lean::dec(x_15);
x_66 = lean::cnstr_get(x_64, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_64, 1);
lean::inc(x_68);
lean::dec(x_64);
x_71 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_72 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_71, x_66);
x_73 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_35, x_72);
x_74 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_73);
x_5 = x_74;
x_6 = x_68;
goto lbl_7;
}
else
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
lean::dec(x_35);
x_76 = l_String_OldIterator_next___main(x_15);
x_77 = lean::box(0);
x_78 = lean::box_uint32(x_54);
if (lean::is_scalar(x_19)) {
 x_79 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_79 = x_19;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_76);
lean::cnstr_set(x_79, 2, x_77);
x_80 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_79);
x_5 = x_80;
x_6 = x_32;
goto lbl_7;
}
}
}
else
{
obj* x_83; obj* x_86; 
lean::dec(x_15);
lean::dec(x_19);
x_83 = lean::cnstr_get(x_22, 1);
lean::inc(x_83);
lean::dec(x_22);
x_86 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_23);
x_5 = x_86;
x_6 = x_83;
goto lbl_7;
}
}
}
else
{
obj* x_87; obj* x_90; uint8 x_92; obj* x_93; obj* x_94; obj* x_95; 
x_87 = lean::cnstr_get(x_9, 1);
lean::inc(x_87);
lean::dec(x_9);
x_90 = lean::cnstr_get(x_10, 0);
x_92 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 x_93 = x_10;
} else {
 lean::inc(x_90);
 lean::dec(x_10);
 x_93 = lean::box(0);
}
if (lean::is_scalar(x_93)) {
 x_94 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_94 = x_93;
}
lean::cnstr_set(x_94, 0, x_90);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_92);
x_95 = x_94;
x_5 = x_95;
x_6 = x_87;
goto lbl_7;
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_96; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_96 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_98 = x_5;
} else {
 lean::inc(x_96);
 lean::dec(x_5);
 x_98 = lean::box(0);
}
x_99 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_98)) {
 x_100 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_100 = x_98;
}
lean::cnstr_set(x_100, 0, x_96);
lean::cnstr_set(x_100, 1, x_3);
lean::cnstr_set(x_100, 2, x_99);
x_101 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_6);
return x_101;
}
else
{
obj* x_103; 
lean::dec(x_3);
x_103 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_103, 0, x_5);
lean::cnstr_set(x_103, 1, x_6);
return x_103;
}
}
}
}
obj* _init_l_Lean_Parser_detailIdentSuffix_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_0 = lean::mk_string(".");
x_1 = l_String_quote(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed), 5, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__2___boxed), 6, 1);
lean::closure_set(x_6, 0, x_2);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__6___rarg), 6, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_6);
x_8 = lean::box(0);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_recurse___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__7), 5, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_10);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_7);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
obj* l_Lean_Parser_detailIdentSuffix_Parser(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; 
x_4 = 46;
x_5 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser___spec__1(x_0, x_1, x_4, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
x_8 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 lean::cnstr_set(x_5, 1, lean::box(0));
 x_10 = x_5;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::dec(x_5);
 x_10 = lean::box(0);
}
x_11 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_6);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_10);
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_11, 2);
lean::inc(x_15);
lean::dec(x_11);
x_18 = l_Lean_Parser_detailIdentSuffix;
x_19 = l_Lean_Parser_detailIdentSuffix_Parser___closed__1;
x_20 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__8(x_18, x_19, x_0, x_1, x_13, x_8);
x_21 = lean::cnstr_get(x_20, 0);
x_23 = lean::cnstr_get(x_20, 1);
if (lean::is_exclusive(x_20)) {
 x_25 = x_20;
} else {
 lean::inc(x_21);
 lean::inc(x_23);
 lean::dec(x_20);
 x_25 = lean::box(0);
}
x_26 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_21);
if (lean::is_scalar(x_25)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_25;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_23);
return x_27;
}
else
{
obj* x_30; uint8 x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_1);
lean::dec(x_0);
x_30 = lean::cnstr_get(x_11, 0);
x_32 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 x_33 = x_11;
} else {
 lean::inc(x_30);
 lean::dec(x_11);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_30);
lean::cnstr_set_scalar(x_34, sizeof(void*)*1, x_32);
x_35 = x_34;
if (lean::is_scalar(x_10)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_10;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_8);
return x_36;
}
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_2);
x_6 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser___spec__1(x_0, x_1, x_5, x_3, x_4);
lean::dec(x_0);
lean::dec(x_1);
return x_6;
}
}
obj* _init_l_Lean_Parser_detailIdent() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("detailIdent");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_detailIdent_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_detailIdentSuffix_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_detailIdent_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_4; obj* x_5; obj* x_6; 
x_0 = l_Lean_Parser_detailIdentPart_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
x_4 = lean::box(3);
x_5 = lean::apply_1(x_1, x_4);
x_6 = l_Lean_Parser_Syntax_asNode___main(x_4);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; 
x_7 = l_Lean_Parser_detailIdent_HasView_x_27___lambda__1___closed__1;
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_5);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_set(x_6, 0, lean::box(0));
 x_11 = x_6;
} else {
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
if (lean::obj_tag(x_12) == 0)
{
obj* x_16; obj* x_17; 
lean::dec(x_11);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_5);
lean::cnstr_set(x_17, 1, x_16);
return x_17;
}
else
{
obj* x_18; 
x_18 = lean::cnstr_get(x_12, 1);
lean::inc(x_18);
if (lean::obj_tag(x_18) == 0)
{
obj* x_20; obj* x_23; obj* x_24; obj* x_27; obj* x_28; obj* x_29; 
x_20 = lean::cnstr_get(x_12, 0);
lean::inc(x_20);
lean::dec(x_12);
x_23 = l_Lean_Parser_detailIdentSuffix_HasView;
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
lean::dec(x_23);
x_27 = lean::apply_1(x_24, x_20);
if (lean::is_scalar(x_11)) {
 x_28 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_28 = x_11;
}
lean::cnstr_set(x_28, 0, x_27);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_5);
lean::cnstr_set(x_29, 1, x_28);
return x_29;
}
else
{
obj* x_33; obj* x_34; 
lean::dec(x_11);
lean::dec(x_12);
lean::dec(x_18);
x_33 = l_Lean_Parser_detailIdent_HasView_x_27___lambda__1___closed__1;
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_5);
lean::cnstr_set(x_34, 1, x_33);
return x_34;
}
}
}
}
}
obj* l_Lean_Parser_detailIdent_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_4; 
x_4 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_4) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_detailIdent_HasView_x_27___lambda__1___closed__2;
return x_5;
}
else
{
obj* x_6; obj* x_9; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
lean::dec(x_4);
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
if (lean::obj_tag(x_9) == 0)
{
obj* x_12; 
x_12 = lean::box(3);
x_1 = x_9;
x_2 = x_12;
goto lbl_3;
}
else
{
obj* x_13; obj* x_15; 
x_13 = lean::cnstr_get(x_9, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_9, 1);
lean::inc(x_15);
lean::dec(x_9);
x_1 = x_15;
x_2 = x_13;
goto lbl_3;
}
}
lbl_3:
{
obj* x_18; obj* x_19; obj* x_22; 
x_18 = l_Lean_Parser_detailIdentPart_HasView;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
lean::dec(x_18);
x_22 = lean::apply_1(x_19, x_2);
if (lean::obj_tag(x_1) == 0)
{
obj* x_23; obj* x_24; 
x_23 = lean::box(3);
x_24 = l_Lean_Parser_Syntax_asNode___main(x_23);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; 
x_25 = l_Lean_Parser_detailIdent_HasView_x_27___lambda__1___closed__1;
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_22);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
else
{
obj* x_27; obj* x_29; obj* x_30; 
x_27 = lean::cnstr_get(x_24, 0);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_set(x_24, 0, lean::box(0));
 x_29 = x_24;
} else {
 lean::inc(x_27);
 lean::dec(x_24);
 x_29 = lean::box(0);
}
x_30 = lean::cnstr_get(x_27, 1);
lean::inc(x_30);
lean::dec(x_27);
if (lean::obj_tag(x_30) == 0)
{
obj* x_34; obj* x_35; 
lean::dec(x_29);
x_34 = lean::box(0);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_22);
lean::cnstr_set(x_35, 1, x_34);
return x_35;
}
else
{
obj* x_36; 
x_36 = lean::cnstr_get(x_30, 1);
lean::inc(x_36);
if (lean::obj_tag(x_36) == 0)
{
obj* x_38; obj* x_41; obj* x_42; obj* x_45; obj* x_46; obj* x_47; 
x_38 = lean::cnstr_get(x_30, 0);
lean::inc(x_38);
lean::dec(x_30);
x_41 = l_Lean_Parser_detailIdentSuffix_HasView;
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
lean::dec(x_41);
x_45 = lean::apply_1(x_42, x_38);
if (lean::is_scalar(x_29)) {
 x_46 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_46 = x_29;
}
lean::cnstr_set(x_46, 0, x_45);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_22);
lean::cnstr_set(x_47, 1, x_46);
return x_47;
}
else
{
obj* x_51; obj* x_52; 
lean::dec(x_29);
lean::dec(x_30);
lean::dec(x_36);
x_51 = l_Lean_Parser_detailIdent_HasView_x_27___lambda__1___closed__1;
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_22);
lean::cnstr_set(x_52, 1, x_51);
return x_52;
}
}
}
}
else
{
obj* x_53; obj* x_56; 
x_53 = lean::cnstr_get(x_1, 0);
lean::inc(x_53);
lean::dec(x_1);
x_56 = l_Lean_Parser_Syntax_asNode___main(x_53);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; obj* x_58; 
x_57 = l_Lean_Parser_detailIdent_HasView_x_27___lambda__1___closed__1;
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_22);
lean::cnstr_set(x_58, 1, x_57);
return x_58;
}
else
{
obj* x_59; obj* x_61; obj* x_62; 
x_59 = lean::cnstr_get(x_56, 0);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_set(x_56, 0, lean::box(0));
 x_61 = x_56;
} else {
 lean::inc(x_59);
 lean::dec(x_56);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_59, 1);
lean::inc(x_62);
lean::dec(x_59);
if (lean::obj_tag(x_62) == 0)
{
obj* x_66; obj* x_67; 
lean::dec(x_61);
x_66 = lean::box(0);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_22);
lean::cnstr_set(x_67, 1, x_66);
return x_67;
}
else
{
obj* x_68; 
x_68 = lean::cnstr_get(x_62, 1);
lean::inc(x_68);
if (lean::obj_tag(x_68) == 0)
{
obj* x_70; obj* x_73; obj* x_74; obj* x_77; obj* x_78; obj* x_79; 
x_70 = lean::cnstr_get(x_62, 0);
lean::inc(x_70);
lean::dec(x_62);
x_73 = l_Lean_Parser_detailIdentSuffix_HasView;
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
lean::dec(x_73);
x_77 = lean::apply_1(x_74, x_70);
if (lean::is_scalar(x_61)) {
 x_78 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_78 = x_61;
}
lean::cnstr_set(x_78, 0, x_77);
x_79 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_79, 0, x_22);
lean::cnstr_set(x_79, 1, x_78);
return x_79;
}
else
{
obj* x_83; obj* x_84; 
lean::dec(x_68);
lean::dec(x_62);
lean::dec(x_61);
x_83 = l_Lean_Parser_detailIdent_HasView_x_27___lambda__1___closed__1;
x_84 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_84, 0, x_22);
lean::cnstr_set(x_84, 1, x_83);
return x_84;
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_detailIdent_HasView_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; 
x_0 = lean::box(0);
x_1 = l_Lean_Parser_noKind;
x_2 = l_Lean_Parser_Syntax_mkNode(x_1, x_0);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_0);
return x_3;
}
}
obj* l_Lean_Parser_detailIdent_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; obj* x_3; obj* x_6; obj* x_7; obj* x_10; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
x_3 = lean::cnstr_get(x_0, 1);
lean::inc(x_3);
lean::dec(x_0);
x_6 = l_Lean_Parser_detailIdentPart_HasView;
x_7 = lean::cnstr_get(x_6, 1);
lean::inc(x_7);
lean::dec(x_6);
x_10 = lean::apply_1(x_7, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = l_Lean_Parser_detailIdent_HasView_x_27___lambda__2___closed__1;
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_Lean_Parser_detailIdent;
x_14 = l_Lean_Parser_Syntax_mkNode(x_13, x_12);
return x_14;
}
else
{
obj* x_15; obj* x_18; obj* x_19; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
lean::dec(x_3);
x_18 = lean::box(0);
x_19 = l_Lean_Parser_detailIdentSuffix_HasView;
x_20 = lean::cnstr_get(x_19, 1);
lean::inc(x_20);
lean::dec(x_19);
x_23 = lean::apply_1(x_20, x_15);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_18);
x_25 = l_Lean_Parser_noKind;
x_26 = l_Lean_Parser_Syntax_mkNode(x_25, x_24);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_18);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_10);
lean::cnstr_set(x_28, 1, x_27);
x_29 = l_Lean_Parser_detailIdent;
x_30 = l_Lean_Parser_Syntax_mkNode(x_29, x_28);
return x_30;
}
}
}
obj* _init_l_Lean_Parser_detailIdent_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdent_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdent_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_detailIdent_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_detailIdent_HasView_x_27;
return x_0;
}
}
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_detailIdent_x_27___spec__1(obj* x_0, uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
if (x_1 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_14; obj* x_15; 
x_9 = lean::box(0);
lean::inc(x_4);
x_14 = lean::apply_4(x_0, x_2, x_3, x_4, x_5);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; obj* x_20; obj* x_22; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_17 = lean::cnstr_get(x_14, 1);
lean::inc(x_17);
lean::dec(x_14);
x_20 = lean::cnstr_get(x_15, 0);
x_22 = lean::cnstr_get(x_15, 1);
x_24 = lean::cnstr_get(x_15, 2);
if (lean::is_exclusive(x_15)) {
 x_26 = x_15;
} else {
 lean::inc(x_20);
 lean::inc(x_22);
 lean::inc(x_24);
 lean::dec(x_15);
 x_26 = lean::box(0);
}
x_27 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_27, 0, x_20);
x_28 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_26)) {
 x_29 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_29 = x_26;
}
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_22);
lean::cnstr_set(x_29, 2, x_28);
x_30 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_29);
x_10 = x_30;
x_11 = x_17;
goto lbl_12;
}
else
{
obj* x_31; obj* x_34; uint8 x_36; obj* x_37; obj* x_38; obj* x_39; 
x_31 = lean::cnstr_get(x_14, 1);
lean::inc(x_31);
lean::dec(x_14);
x_34 = lean::cnstr_get(x_15, 0);
x_36 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_37 = x_15;
} else {
 lean::inc(x_34);
 lean::dec(x_15);
 x_37 = lean::box(0);
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_34);
lean::cnstr_set_scalar(x_38, sizeof(void*)*1, x_36);
x_39 = x_38;
x_10 = x_39;
x_11 = x_31;
goto lbl_12;
}
}
else
{
obj* x_40; obj* x_43; uint8 x_45; obj* x_46; obj* x_47; obj* x_49; obj* x_51; obj* x_53; obj* x_56; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_40 = lean::cnstr_get(x_14, 1);
lean::inc(x_40);
lean::dec(x_14);
x_43 = lean::cnstr_get(x_15, 0);
x_45 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 x_46 = x_15;
} else {
 lean::inc(x_43);
 lean::dec(x_15);
 x_46 = lean::box(0);
}
x_47 = lean::cnstr_get(x_43, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_43, 1);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_43, 2);
lean::inc(x_51);
x_53 = lean::cnstr_get(x_43, 3);
lean::inc(x_53);
lean::dec(x_43);
x_56 = l_Option_get___main___at_Lean_Parser_run___spec__2(x_53);
lean::dec(x_53);
x_58 = lean::box(0);
x_59 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_59, 0, x_56);
lean::cnstr_set(x_59, 1, x_58);
x_60 = l_Lean_Parser_noKind;
x_61 = l_Lean_Parser_Syntax_mkNode(x_60, x_59);
x_62 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_62, 0, x_61);
x_63 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_63, 0, x_47);
lean::cnstr_set(x_63, 1, x_49);
lean::cnstr_set(x_63, 2, x_51);
lean::cnstr_set(x_63, 3, x_62);
if (x_45 == 0)
{
uint8 x_64; obj* x_65; obj* x_66; 
x_64 = 0;
if (lean::is_scalar(x_46)) {
 x_65 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_65 = x_46;
}
lean::cnstr_set(x_65, 0, x_63);
lean::cnstr_set_scalar(x_65, sizeof(void*)*1, x_64);
x_66 = x_65;
x_10 = x_66;
x_11 = x_40;
goto lbl_12;
}
else
{
uint8 x_67; obj* x_68; obj* x_69; 
x_67 = 1;
if (lean::is_scalar(x_46)) {
 x_68 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_68 = x_46;
}
lean::cnstr_set(x_68, 0, x_63);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_67);
x_69 = x_68;
x_10 = x_69;
x_11 = x_40;
goto lbl_12;
}
}
lbl_12:
{
if (lean::obj_tag(x_10) == 0)
{
lean::dec(x_4);
x_6 = x_10;
x_7 = x_11;
goto lbl_8;
}
else
{
uint8 x_71; 
x_71 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (x_71 == 0)
{
obj* x_72; obj* x_75; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_72 = lean::cnstr_get(x_10, 0);
lean::inc(x_72);
lean::dec(x_10);
x_75 = lean::cnstr_get(x_72, 2);
lean::inc(x_75);
lean::dec(x_72);
x_78 = l_mjoin___rarg___closed__1;
x_79 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_79, 0, x_75);
lean::closure_set(x_79, 1, x_78);
x_80 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_80, 0, x_79);
x_81 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_81, 0, x_9);
lean::cnstr_set(x_81, 1, x_4);
lean::cnstr_set(x_81, 2, x_80);
x_6 = x_81;
x_7 = x_11;
goto lbl_8;
}
else
{
lean::dec(x_4);
x_6 = x_10;
x_7 = x_11;
goto lbl_8;
}
}
}
}
else
{
obj* x_83; 
x_83 = lean::apply_4(x_0, x_2, x_3, x_4, x_5);
return x_83;
}
lbl_8:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_84; 
x_84 = lean::cnstr_get(x_6, 0);
lean::inc(x_84);
if (lean::obj_tag(x_84) == 0)
{
obj* x_86; obj* x_88; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_86 = lean::cnstr_get(x_6, 1);
x_88 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_90 = x_6;
} else {
 lean::inc(x_86);
 lean::inc(x_88);
 lean::dec(x_6);
 x_90 = lean::box(0);
}
x_91 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_92 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_90)) {
 x_93 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_93 = x_90;
}
lean::cnstr_set(x_93, 0, x_91);
lean::cnstr_set(x_93, 1, x_86);
lean::cnstr_set(x_93, 2, x_92);
x_94 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_88, x_93);
x_95 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_7);
return x_95;
}
else
{
obj* x_96; obj* x_98; obj* x_100; obj* x_101; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
x_96 = lean::cnstr_get(x_6, 1);
x_98 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_100 = x_6;
} else {
 lean::inc(x_96);
 lean::inc(x_98);
 lean::dec(x_6);
 x_100 = lean::box(0);
}
x_101 = lean::cnstr_get(x_84, 0);
lean::inc(x_101);
lean::dec(x_84);
x_104 = lean::box(0);
x_105 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_105, 0, x_101);
lean::cnstr_set(x_105, 1, x_104);
x_106 = l_Lean_Parser_noKind;
x_107 = l_Lean_Parser_Syntax_mkNode(x_106, x_105);
x_108 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_100)) {
 x_109 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_109 = x_100;
}
lean::cnstr_set(x_109, 0, x_107);
lean::cnstr_set(x_109, 1, x_96);
lean::cnstr_set(x_109, 2, x_108);
x_110 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_98, x_109);
x_111 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_111, 0, x_110);
lean::cnstr_set(x_111, 1, x_7);
return x_111;
}
}
else
{
obj* x_112; uint8 x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
x_112 = lean::cnstr_get(x_6, 0);
x_114 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_115 = x_6;
} else {
 lean::inc(x_112);
 lean::dec(x_6);
 x_115 = lean::box(0);
}
if (lean::is_scalar(x_115)) {
 x_116 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_116 = x_115;
}
lean::cnstr_set(x_116, 0, x_112);
lean::cnstr_set_scalar(x_116, sizeof(void*)*1, x_114);
x_117 = x_116;
x_118 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_118, 0, x_117);
lean::cnstr_set(x_118, 1, x_7);
return x_118;
}
}
}
}
obj* _init_l_Lean_Parser_detailIdent_x_27___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; uint8 x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPart_Parser), 3, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed), 5, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentSuffix_Parser), 4, 0);
x_3 = 0;
x_4 = lean::box(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_detailIdent_x_27___spec__1___boxed), 6, 2);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set(x_8, 1, x_7);
return x_8;
}
}
obj* l_Lean_Parser_detailIdent_x_27(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_detailIdent;
x_5 = l_Lean_Parser_detailIdent_x_27___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__8(x_4, x_5, x_0, x_1, x_2, x_3);
return x_6;
}
}
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_detailIdent_x_27___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_1);
x_7 = l_Lean_Parser_Combinators_optional___at_Lean_Parser_detailIdent_x_27___spec__1(x_0, x_6, x_2, x_3, x_4, x_5);
return x_7;
}
}
obj* l_Lean_Parser_detailIdent_Parser___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::box(0);
x_5 = l_Lean_Parser_RecT_runParsec___rarg___lambda__1___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_1, x_2, x_3);
return x_7;
}
}
obj* l_Lean_Parser_detailIdent_Parser___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_detailIdent;
x_6 = l_Lean_Parser_detailIdent_x_27___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__8(x_5, x_6, x_0, x_2, x_3, x_4);
return x_7;
}
}
obj* _init_l_Lean_Parser_detailIdent_Parser___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdent_Parser___lambda__1___boxed), 4, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdent_Parser___lambda__2___boxed), 5, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_fixCore___rarg___boxed), 3, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_Lean_Parser_detailIdent_Parser(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_Lean_Parser_detailIdent;
x_4 = l_Lean_Parser_detailIdent_x_27___closed__1;
x_5 = l_Lean_Parser_detailIdent_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__8(x_3, x_4, x_5, x_0, x_1, x_2);
return x_6;
}
}
obj* l_Lean_Parser_detailIdent_Parser___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_detailIdent_Parser___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_detailIdent_Parser___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_detailIdent_Parser___lambda__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2___rarg(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = l_String_OldIterator_curr___main(x_0);
x_3 = l_Lean_Parser_finishCommentBlock___closed__2;
x_4 = lean::box_uint32(x_2);
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_0);
lean::cnstr_set(x_5, 2, x_3);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2___rarg), 2, 0);
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdRest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_OldIterator_next___main(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__5(x_4, x_0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdRest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_OldIterator_next___main(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__7(x_4, x_0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__9(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdRest(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_OldIterator_next___main(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__9(x_4, x_0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l_Lean_Parser_idPartDefault___at___private_init_lean_parser_token_4__ident_x_27___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_String_OldIterator_hasNext___main(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_4 = lean::box(0);
x_5 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_13 = x_7;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_9);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; obj* x_19; obj* x_21; obj* x_24; uint32 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_13);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_15, 2);
lean::inc(x_21);
lean::dec(x_15);
x_24 = l_String_splitAux___main___closed__1;
x_25 = lean::unbox_uint32(x_17);
x_26 = lean::string_push(x_24, x_25);
x_27 = l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__4(x_26, x_0, x_19, x_11);
x_28 = lean::cnstr_get(x_27, 0);
x_30 = lean::cnstr_get(x_27, 1);
if (lean::is_exclusive(x_27)) {
 x_32 = x_27;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::dec(x_27);
 x_32 = lean::box(0);
}
x_33 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_28);
if (lean::is_scalar(x_32)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_32;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_30);
return x_34;
}
else
{
obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_35 = lean::cnstr_get(x_15, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_38 = x_15;
} else {
 lean::inc(x_35);
 lean::dec(x_15);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_35);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_37);
x_40 = x_39;
if (lean::is_scalar(x_13)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_13;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_11);
return x_41;
}
}
else
{
uint32 x_42; uint8 x_43; 
x_42 = l_String_OldIterator_curr___main(x_1);
x_43 = l_Lean_isIdFirst(x_42);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
x_44 = l_Char_quoteCore(x_42);
x_45 = l_Char_HasRepr___closed__1;
x_46 = lean::string_append(x_45, x_44);
lean::dec(x_44);
x_48 = lean::string_append(x_46, x_45);
x_49 = lean::box(0);
x_50 = l_mjoin___rarg___closed__1;
x_51 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_48, x_50, x_49, x_49, x_0, x_1, x_2);
lean::dec(x_1);
x_53 = lean::cnstr_get(x_51, 0);
x_55 = lean::cnstr_get(x_51, 1);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_set(x_51, 0, lean::box(0));
 lean::cnstr_set(x_51, 1, lean::box(0));
 x_57 = x_51;
} else {
 lean::inc(x_53);
 lean::inc(x_55);
 lean::dec(x_51);
 x_57 = lean::box(0);
}
x_58 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_59 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_53);
if (lean::obj_tag(x_59) == 0)
{
obj* x_61; obj* x_63; obj* x_65; obj* x_68; uint32 x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_74; obj* x_76; obj* x_77; obj* x_78; 
lean::dec(x_57);
x_61 = lean::cnstr_get(x_59, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_59, 1);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_59, 2);
lean::inc(x_65);
lean::dec(x_59);
x_68 = l_String_splitAux___main___closed__1;
x_69 = lean::unbox_uint32(x_61);
x_70 = lean::string_push(x_68, x_69);
x_71 = l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__6(x_70, x_0, x_63, x_55);
x_72 = lean::cnstr_get(x_71, 0);
x_74 = lean::cnstr_get(x_71, 1);
if (lean::is_exclusive(x_71)) {
 x_76 = x_71;
} else {
 lean::inc(x_72);
 lean::inc(x_74);
 lean::dec(x_71);
 x_76 = lean::box(0);
}
x_77 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_65, x_72);
if (lean::is_scalar(x_76)) {
 x_78 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_78 = x_76;
}
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_74);
return x_78;
}
else
{
obj* x_79; uint8 x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_79 = lean::cnstr_get(x_59, 0);
x_81 = lean::cnstr_get_scalar<uint8>(x_59, sizeof(void*)*1);
if (lean::is_exclusive(x_59)) {
 x_82 = x_59;
} else {
 lean::inc(x_79);
 lean::dec(x_59);
 x_82 = lean::box(0);
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_83 = x_82;
}
lean::cnstr_set(x_83, 0, x_79);
lean::cnstr_set_scalar(x_83, sizeof(void*)*1, x_81);
x_84 = x_83;
if (lean::is_scalar(x_57)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_57;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_55);
return x_85;
}
}
else
{
obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_92; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_86 = l_String_OldIterator_next___main(x_1);
x_87 = l_String_splitAux___main___closed__1;
x_88 = lean::string_push(x_87, x_42);
x_89 = l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__8(x_88, x_0, x_86, x_2);
x_90 = lean::cnstr_get(x_89, 0);
x_92 = lean::cnstr_get(x_89, 1);
if (lean::is_exclusive(x_89)) {
 x_94 = x_89;
} else {
 lean::inc(x_90);
 lean::inc(x_92);
 lean::dec(x_89);
 x_94 = lean::box(0);
}
x_95 = lean::box(0);
x_96 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_95, x_90);
if (lean::is_scalar(x_94)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_94;
}
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_92);
return x_97;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_String_OldIterator_hasNext___main(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_10; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_5 = lean::box(0);
x_6 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_7 = l_mjoin___rarg___closed__1;
x_8 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_6, x_7, x_5, x_5, x_1, x_2, x_3);
lean::dec(x_2);
x_10 = lean::cnstr_get(x_8, 0);
x_12 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 x_14 = x_8;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_8);
 x_14 = lean::box(0);
}
x_15 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_16 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_10);
if (lean::is_scalar(x_14)) {
 x_17 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_17 = x_14;
}
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_12);
return x_17;
}
else
{
uint32 x_18; uint8 x_19; 
x_18 = l_String_OldIterator_curr___main(x_2);
x_19 = x_18 == x_0;
if (x_19 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_31; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_20 = l_Char_quoteCore(x_18);
x_21 = l_Char_HasRepr___closed__1;
x_22 = lean::string_append(x_21, x_20);
lean::dec(x_20);
x_24 = lean::string_append(x_22, x_21);
x_25 = lean::box(0);
x_26 = l_mjoin___rarg___closed__1;
x_27 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_24, x_26, x_25, x_25, x_1, x_2, x_3);
lean::dec(x_2);
x_29 = lean::cnstr_get(x_27, 0);
x_31 = lean::cnstr_get(x_27, 1);
if (lean::is_exclusive(x_27)) {
 x_33 = x_27;
} else {
 lean::inc(x_29);
 lean::inc(x_31);
 lean::dec(x_27);
 x_33 = lean::box(0);
}
x_34 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_34, x_29);
if (lean::is_scalar(x_33)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_33;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_31);
return x_36;
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_37 = l_String_OldIterator_next___main(x_2);
x_38 = lean::box(0);
x_39 = lean::box_uint32(x_18);
x_40 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_37);
lean::cnstr_set(x_40, 2, x_38);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_3);
return x_41;
}
}
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__14(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdEndEscape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = l_String_OldIterator_next___main(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_17;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__13(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__14(x_4, x_0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__16(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdEndEscape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = l_String_OldIterator_next___main(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_17;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__15(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__16(x_4, x_0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__18(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Lean_isIdEndEscape(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_14; 
x_10 = lean::mk_nat_obj(1u);
x_11 = lean::nat_sub(x_0, x_10);
lean::dec(x_0);
x_13 = lean::string_push(x_1, x_8);
x_14 = l_String_OldIterator_next___main(x_2);
x_0 = x_11;
x_1 = x_13;
x_2 = x_14;
goto _start;
}
else
{
obj* x_17; 
lean::dec(x_0);
x_17 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_17;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__17(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__18(x_4, x_0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at___private_init_lean_parser_token_4__ident_x_27___spec__12(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_String_OldIterator_hasNext___main(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_4 = lean::box(0);
x_5 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_13 = x_7;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_9);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; obj* x_19; obj* x_21; obj* x_24; uint32 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_13);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_15, 2);
lean::inc(x_21);
lean::dec(x_15);
x_24 = l_String_splitAux___main___closed__1;
x_25 = lean::unbox_uint32(x_17);
x_26 = lean::string_push(x_24, x_25);
x_27 = l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__13(x_26, x_0, x_19, x_11);
x_28 = lean::cnstr_get(x_27, 0);
x_30 = lean::cnstr_get(x_27, 1);
if (lean::is_exclusive(x_27)) {
 x_32 = x_27;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::dec(x_27);
 x_32 = lean::box(0);
}
x_33 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_28);
if (lean::is_scalar(x_32)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_32;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_30);
return x_34;
}
else
{
obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_35 = lean::cnstr_get(x_15, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_38 = x_15;
} else {
 lean::inc(x_35);
 lean::dec(x_15);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_35);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_37);
x_40 = x_39;
if (lean::is_scalar(x_13)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_13;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_11);
return x_41;
}
}
else
{
uint32 x_42; uint8 x_43; 
x_42 = l_String_OldIterator_curr___main(x_1);
x_43 = l_Lean_isIdEndEscape(x_42);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_50; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_44 = l_String_OldIterator_next___main(x_1);
x_45 = l_String_splitAux___main___closed__1;
x_46 = lean::string_push(x_45, x_42);
x_47 = l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__15(x_46, x_0, x_44, x_2);
x_48 = lean::cnstr_get(x_47, 0);
x_50 = lean::cnstr_get(x_47, 1);
if (lean::is_exclusive(x_47)) {
 x_52 = x_47;
} else {
 lean::inc(x_48);
 lean::inc(x_50);
 lean::dec(x_47);
 x_52 = lean::box(0);
}
x_53 = lean::box(0);
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_53, x_48);
if (lean::is_scalar(x_52)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_52;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_50);
return x_55;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_67; obj* x_69; obj* x_70; obj* x_71; 
x_56 = l_Char_quoteCore(x_42);
x_57 = l_Char_HasRepr___closed__1;
x_58 = lean::string_append(x_57, x_56);
lean::dec(x_56);
x_60 = lean::string_append(x_58, x_57);
x_61 = lean::box(0);
x_62 = l_mjoin___rarg___closed__1;
x_63 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_60, x_62, x_61, x_61, x_0, x_1, x_2);
lean::dec(x_1);
x_65 = lean::cnstr_get(x_63, 0);
x_67 = lean::cnstr_get(x_63, 1);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_set(x_63, 0, lean::box(0));
 lean::cnstr_set(x_63, 1, lean::box(0));
 x_69 = x_63;
} else {
 lean::inc(x_65);
 lean::inc(x_67);
 lean::dec(x_63);
 x_69 = lean::box(0);
}
x_70 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_71 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_70, x_65);
if (lean::obj_tag(x_71) == 0)
{
obj* x_73; obj* x_75; obj* x_77; obj* x_80; uint32 x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_86; obj* x_88; obj* x_89; obj* x_90; 
lean::dec(x_69);
x_73 = lean::cnstr_get(x_71, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_71, 1);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_71, 2);
lean::inc(x_77);
lean::dec(x_71);
x_80 = l_String_splitAux___main___closed__1;
x_81 = lean::unbox_uint32(x_73);
x_82 = lean::string_push(x_80, x_81);
x_83 = l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__17(x_82, x_0, x_75, x_67);
x_84 = lean::cnstr_get(x_83, 0);
x_86 = lean::cnstr_get(x_83, 1);
if (lean::is_exclusive(x_83)) {
 x_88 = x_83;
} else {
 lean::inc(x_84);
 lean::inc(x_86);
 lean::dec(x_83);
 x_88 = lean::box(0);
}
x_89 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_77, x_84);
if (lean::is_scalar(x_88)) {
 x_90 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_90 = x_88;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_86);
return x_90;
}
else
{
obj* x_91; uint8 x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_91 = lean::cnstr_get(x_71, 0);
x_93 = lean::cnstr_get_scalar<uint8>(x_71, sizeof(void*)*1);
if (lean::is_exclusive(x_71)) {
 x_94 = x_71;
} else {
 lean::inc(x_91);
 lean::dec(x_71);
 x_94 = lean::box(0);
}
if (lean::is_scalar(x_94)) {
 x_95 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_95 = x_94;
}
lean::cnstr_set(x_95, 0, x_91);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_93);
x_96 = x_95;
if (lean::is_scalar(x_69)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_69;
}
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_67);
return x_97;
}
}
}
}
}
obj* l_Lean_Parser_idPartEscaped___at___private_init_lean_parser_token_4__ident_x_27___spec__10(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_idBeginEscape;
x_4 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_3, x_0, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_18; obj* x_20; obj* x_21; 
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 2);
lean::inc(x_12);
lean::dec(x_5);
x_15 = l_Lean_Parser_MonadParsec_takeWhile1___at___private_init_lean_parser_token_4__ident_x_27___spec__12(x_0, x_10, x_7);
x_16 = lean::cnstr_get(x_15, 0);
x_18 = lean::cnstr_get(x_15, 1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_set(x_15, 0, lean::box(0));
 lean::cnstr_set(x_15, 1, lean::box(0));
 x_20 = x_15;
} else {
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_15);
 x_20 = lean::box(0);
}
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_16);
if (lean::obj_tag(x_21) == 0)
{
obj* x_23; obj* x_25; obj* x_27; uint32 x_30; obj* x_31; obj* x_32; 
lean::dec(x_20);
x_23 = lean::cnstr_get(x_21, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_21, 1);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_21, 2);
lean::inc(x_27);
lean::dec(x_21);
x_30 = l_Lean_idEndEscape;
x_31 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_30, x_0, x_25, x_18);
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
if (lean::obj_tag(x_32) == 0)
{
obj* x_34; obj* x_36; obj* x_37; obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_34 = lean::cnstr_get(x_31, 1);
if (lean::is_exclusive(x_31)) {
 lean::cnstr_release(x_31, 0);
 x_36 = x_31;
} else {
 lean::inc(x_34);
 lean::dec(x_31);
 x_36 = lean::box(0);
}
x_37 = lean::cnstr_get(x_32, 1);
x_39 = lean::cnstr_get(x_32, 2);
if (lean::is_exclusive(x_32)) {
 lean::cnstr_release(x_32, 0);
 x_41 = x_32;
} else {
 lean::inc(x_37);
 lean::inc(x_39);
 lean::dec(x_32);
 x_41 = lean::box(0);
}
x_42 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_41)) {
 x_43 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_43 = x_41;
}
lean::cnstr_set(x_43, 0, x_23);
lean::cnstr_set(x_43, 1, x_37);
lean::cnstr_set(x_43, 2, x_42);
x_44 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_39, x_43);
x_45 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_27, x_44);
if (lean::is_scalar(x_36)) {
 x_46 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_46 = x_36;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_34);
return x_46;
}
else
{
obj* x_48; obj* x_50; obj* x_51; uint8 x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_23);
x_48 = lean::cnstr_get(x_31, 1);
if (lean::is_exclusive(x_31)) {
 lean::cnstr_release(x_31, 0);
 x_50 = x_31;
} else {
 lean::inc(x_48);
 lean::dec(x_31);
 x_50 = lean::box(0);
}
x_51 = lean::cnstr_get(x_32, 0);
x_53 = lean::cnstr_get_scalar<uint8>(x_32, sizeof(void*)*1);
if (lean::is_exclusive(x_32)) {
 x_54 = x_32;
} else {
 lean::inc(x_51);
 lean::dec(x_32);
 x_54 = lean::box(0);
}
if (lean::is_scalar(x_54)) {
 x_55 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_55 = x_54;
}
lean::cnstr_set(x_55, 0, x_51);
lean::cnstr_set_scalar(x_55, sizeof(void*)*1, x_53);
x_56 = x_55;
x_57 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_27, x_56);
if (lean::is_scalar(x_50)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_50;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_48);
return x_58;
}
}
else
{
obj* x_59; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_59 = lean::cnstr_get(x_21, 0);
x_61 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
if (lean::is_exclusive(x_21)) {
 x_62 = x_21;
} else {
 lean::inc(x_59);
 lean::dec(x_21);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_59);
lean::cnstr_set_scalar(x_63, sizeof(void*)*1, x_61);
x_64 = x_63;
if (lean::is_scalar(x_20)) {
 x_65 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_65 = x_20;
}
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_18);
return x_65;
}
}
else
{
obj* x_66; obj* x_68; obj* x_69; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_66 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_68 = x_4;
} else {
 lean::inc(x_66);
 lean::dec(x_4);
 x_68 = lean::box(0);
}
x_69 = lean::cnstr_get(x_5, 0);
x_71 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_72 = x_5;
} else {
 lean::inc(x_69);
 lean::dec(x_5);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_69);
lean::cnstr_set_scalar(x_73, sizeof(void*)*1, x_71);
x_74 = x_73;
if (lean::is_scalar(x_68)) {
 x_75 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_75 = x_68;
}
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_66);
return x_75;
}
}
}
obj* l_Lean_Parser_idPart___at___private_init_lean_parser_token_4__ident_x_27___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Parser_MonadParsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2___rarg(x_1, x_2);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; uint32 x_16; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_set(x_3, 1, lean::box(0));
 x_8 = x_3;
} else {
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_4, 0);
x_11 = lean::cnstr_get(x_4, 1);
x_13 = lean::cnstr_get(x_4, 2);
if (lean::is_exclusive(x_4)) {
 x_15 = x_4;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_4);
 x_15 = lean::box(0);
}
x_16 = lean::unbox_uint32(x_9);
x_17 = l_Lean_isIdBeginEscape(x_16);
x_18 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_19 = lean::box(x_17);
if (lean::is_scalar(x_15)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_15;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_11);
lean::cnstr_set(x_20, 2, x_18);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_20);
if (lean::obj_tag(x_21) == 0)
{
obj* x_23; uint8 x_25; 
lean::dec(x_8);
x_23 = lean::cnstr_get(x_21, 0);
lean::inc(x_23);
x_25 = lean::unbox(x_23);
if (x_25 == 0)
{
obj* x_26; obj* x_28; obj* x_31; obj* x_32; obj* x_34; obj* x_36; obj* x_37; obj* x_38; 
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
x_28 = lean::cnstr_get(x_21, 2);
lean::inc(x_28);
lean::dec(x_21);
x_31 = l_Lean_Parser_idPartDefault___at___private_init_lean_parser_token_4__ident_x_27___spec__3(x_0, x_26, x_6);
x_32 = lean::cnstr_get(x_31, 0);
x_34 = lean::cnstr_get(x_31, 1);
if (lean::is_exclusive(x_31)) {
 x_36 = x_31;
} else {
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_31);
 x_36 = lean::box(0);
}
x_37 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_28, x_32);
if (lean::is_scalar(x_36)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_36;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_34);
return x_38;
}
else
{
obj* x_39; obj* x_41; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_51; 
x_39 = lean::cnstr_get(x_21, 1);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_21, 2);
lean::inc(x_41);
lean::dec(x_21);
x_44 = l_Lean_Parser_idPartEscaped___at___private_init_lean_parser_token_4__ident_x_27___spec__10(x_0, x_39, x_6);
x_45 = lean::cnstr_get(x_44, 0);
x_47 = lean::cnstr_get(x_44, 1);
if (lean::is_exclusive(x_44)) {
 x_49 = x_44;
} else {
 lean::inc(x_45);
 lean::inc(x_47);
 lean::dec(x_44);
 x_49 = lean::box(0);
}
x_50 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_41, x_45);
if (lean::is_scalar(x_49)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_49;
}
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_47);
return x_51;
}
}
else
{
obj* x_52; uint8 x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_52 = lean::cnstr_get(x_21, 0);
x_54 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
if (lean::is_exclusive(x_21)) {
 x_55 = x_21;
} else {
 lean::inc(x_52);
 lean::dec(x_21);
 x_55 = lean::box(0);
}
if (lean::is_scalar(x_55)) {
 x_56 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_56 = x_55;
}
lean::cnstr_set(x_56, 0, x_52);
lean::cnstr_set_scalar(x_56, sizeof(void*)*1, x_54);
x_57 = x_56;
if (lean::is_scalar(x_8)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_8;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_6);
return x_58;
}
}
else
{
obj* x_59; obj* x_61; obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_59 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 x_61 = x_3;
} else {
 lean::inc(x_59);
 lean::dec(x_3);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_4, 0);
x_64 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_65 = x_4;
} else {
 lean::inc(x_62);
 lean::dec(x_4);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_62);
lean::cnstr_set_scalar(x_66, sizeof(void*)*1, x_64);
x_67 = x_66;
if (lean::is_scalar(x_61)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_61;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_59);
return x_68;
}
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_4__ident_x_27___spec__19(obj* x_0, obj* x_1, uint32 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_10; obj* x_11; 
lean::inc(x_4);
x_10 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_2, x_3, x_4, x_5);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_16; obj* x_18; obj* x_20; uint32 x_21; obj* x_23; obj* x_24; 
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = lean::cnstr_get(x_11, 1);
x_18 = lean::cnstr_get(x_11, 2);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_set(x_11, 1, lean::box(0));
 lean::cnstr_set(x_11, 2, lean::box(0));
 x_20 = x_11;
} else {
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_11);
 x_20 = lean::box(0);
}
x_21 = l_Lean_idBeginEscape;
lean::inc(x_16);
x_23 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_21, x_3, x_16, x_13);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_30; obj* x_33; 
lean::dec(x_16);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_20);
x_30 = lean::cnstr_get(x_23, 1);
lean::inc(x_30);
lean::dec(x_23);
x_33 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_24);
x_6 = x_33;
x_7 = x_30;
goto lbl_8;
}
else
{
uint8 x_34; 
x_34 = lean::cnstr_get_scalar<uint8>(x_24, sizeof(void*)*1);
if (x_34 == 0)
{
obj* x_35; obj* x_38; uint8 x_41; 
x_35 = lean::cnstr_get(x_23, 1);
lean::inc(x_35);
lean::dec(x_23);
x_38 = lean::cnstr_get(x_24, 0);
lean::inc(x_38);
lean::dec(x_24);
x_41 = l_String_OldIterator_hasNext___main(x_16);
if (x_41 == 0)
{
obj* x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_20);
x_43 = lean::box(0);
x_44 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_45 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_44, x_0, x_43, x_43, x_3, x_16, x_35);
lean::dec(x_16);
x_47 = lean::cnstr_get(x_45, 0);
lean::inc(x_47);
x_49 = lean::cnstr_get(x_45, 1);
lean::inc(x_49);
lean::dec(x_45);
x_52 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_1, x_47);
x_53 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_38, x_52);
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_53);
x_6 = x_54;
x_7 = x_49;
goto lbl_8;
}
else
{
uint32 x_55; uint8 x_56; 
x_55 = l_String_OldIterator_curr___main(x_16);
x_56 = l_Lean_isIdFirst(x_55);
if (x_56 == 0)
{
obj* x_58; obj* x_59; obj* x_60; obj* x_62; obj* x_63; obj* x_64; obj* x_66; obj* x_68; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_20);
x_58 = l_Char_quoteCore(x_55);
x_59 = l_Char_HasRepr___closed__1;
x_60 = lean::string_append(x_59, x_58);
lean::dec(x_58);
x_62 = lean::string_append(x_60, x_59);
x_63 = lean::box(0);
x_64 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_62, x_0, x_63, x_63, x_3, x_16, x_35);
lean::dec(x_16);
x_66 = lean::cnstr_get(x_64, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_64, 1);
lean::inc(x_68);
lean::dec(x_64);
x_71 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_1, x_66);
x_72 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_38, x_71);
x_73 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_72);
x_6 = x_73;
x_7 = x_68;
goto lbl_8;
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_38);
x_77 = l_String_OldIterator_next___main(x_16);
x_78 = lean::box(0);
x_79 = lean::box_uint32(x_55);
if (lean::is_scalar(x_20)) {
 x_80 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_80 = x_20;
}
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_77);
lean::cnstr_set(x_80, 2, x_78);
x_81 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_80);
x_6 = x_81;
x_7 = x_35;
goto lbl_8;
}
}
}
else
{
obj* x_86; obj* x_89; 
lean::dec(x_16);
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_20);
x_86 = lean::cnstr_get(x_23, 1);
lean::inc(x_86);
lean::dec(x_23);
x_89 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_24);
x_6 = x_89;
x_7 = x_86;
goto lbl_8;
}
}
}
else
{
obj* x_92; obj* x_95; uint8 x_97; obj* x_98; obj* x_99; obj* x_100; 
lean::dec(x_1);
lean::dec(x_0);
x_92 = lean::cnstr_get(x_10, 1);
lean::inc(x_92);
lean::dec(x_10);
x_95 = lean::cnstr_get(x_11, 0);
x_97 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 x_98 = x_11;
} else {
 lean::inc(x_95);
 lean::dec(x_11);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_95);
lean::cnstr_set_scalar(x_99, sizeof(void*)*1, x_97);
x_100 = x_99;
x_6 = x_100;
x_7 = x_92;
goto lbl_8;
}
lbl_8:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_101; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_101 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_103 = x_6;
} else {
 lean::inc(x_101);
 lean::dec(x_6);
 x_103 = lean::box(0);
}
x_104 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_103)) {
 x_105 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_105 = x_103;
}
lean::cnstr_set(x_105, 0, x_101);
lean::cnstr_set(x_105, 1, x_4);
lean::cnstr_set(x_105, 2, x_104);
x_106 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_106, 0, x_105);
lean::cnstr_set(x_106, 1, x_7);
return x_106;
}
else
{
obj* x_108; 
lean::dec(x_4);
x_108 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_108, 0, x_6);
lean::cnstr_set(x_108, 1, x_7);
return x_108;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_2, x_6);
if (x_7 == 0)
{
obj* x_11; obj* x_12; 
lean::inc(x_4);
lean::inc(x_3);
lean::inc(x_0);
x_11 = lean::apply_3(x_0, x_3, x_4, x_5);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_34; obj* x_35; 
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
x_17 = lean::cnstr_get(x_12, 0);
x_19 = lean::cnstr_get(x_12, 1);
x_21 = lean::cnstr_get(x_12, 2);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_set(x_12, 0, lean::box(0));
 lean::cnstr_set(x_12, 1, lean::box(0));
 lean::cnstr_set(x_12, 2, lean::box(0));
 x_23 = x_12;
} else {
 lean::inc(x_17);
 lean::inc(x_19);
 lean::inc(x_21);
 lean::dec(x_12);
 x_23 = lean::box(0);
}
x_24 = lean::mk_nat_obj(1u);
x_25 = lean::nat_sub(x_2, x_24);
lean::inc(x_1);
x_27 = lean_name_mk_string(x_1, x_17);
x_28 = l_Lean_Parser_MonadParsec_foldlAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21(x_0, x_27, x_25, x_3, x_19, x_14);
lean::dec(x_25);
x_30 = lean::cnstr_get(x_28, 0);
x_32 = lean::cnstr_get(x_28, 1);
if (lean::is_exclusive(x_28)) {
 lean::cnstr_set(x_28, 0, lean::box(0));
 lean::cnstr_set(x_28, 1, lean::box(0));
 x_34 = x_28;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::dec(x_28);
 x_34 = lean::box(0);
}
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_30);
if (lean::obj_tag(x_35) == 0)
{
obj* x_39; 
lean::dec(x_23);
lean::dec(x_4);
lean::dec(x_1);
if (lean::is_scalar(x_34)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_34;
}
lean::cnstr_set(x_39, 0, x_35);
lean::cnstr_set(x_39, 1, x_32);
return x_39;
}
else
{
uint8 x_40; 
x_40 = lean::cnstr_get_scalar<uint8>(x_35, sizeof(void*)*1);
if (x_40 == 0)
{
obj* x_41; obj* x_44; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_41 = lean::cnstr_get(x_35, 0);
lean::inc(x_41);
lean::dec(x_35);
x_44 = lean::cnstr_get(x_41, 2);
lean::inc(x_44);
lean::dec(x_41);
x_47 = l_mjoin___rarg___closed__1;
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_48, 0, x_44);
lean::closure_set(x_48, 1, x_47);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
if (lean::is_scalar(x_23)) {
 x_50 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_50 = x_23;
}
lean::cnstr_set(x_50, 0, x_1);
lean::cnstr_set(x_50, 1, x_4);
lean::cnstr_set(x_50, 2, x_49);
if (lean::is_scalar(x_34)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_34;
}
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_32);
return x_51;
}
else
{
obj* x_55; 
lean::dec(x_23);
lean::dec(x_4);
lean::dec(x_1);
if (lean::is_scalar(x_34)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_34;
}
lean::cnstr_set(x_55, 0, x_35);
lean::cnstr_set(x_55, 1, x_32);
return x_55;
}
}
}
else
{
uint8 x_58; 
lean::dec(x_3);
lean::dec(x_0);
x_58 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (x_58 == 0)
{
obj* x_59; obj* x_61; obj* x_62; obj* x_65; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_59 = lean::cnstr_get(x_11, 1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_61 = x_11;
} else {
 lean::inc(x_59);
 lean::dec(x_11);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_12, 0);
lean::inc(x_62);
lean::dec(x_12);
x_65 = lean::cnstr_get(x_62, 2);
lean::inc(x_65);
lean::dec(x_62);
x_68 = l_mjoin___rarg___closed__1;
x_69 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_69, 0, x_65);
lean::closure_set(x_69, 1, x_68);
x_70 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_70, 0, x_69);
x_71 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_71, 0, x_1);
lean::cnstr_set(x_71, 1, x_4);
lean::cnstr_set(x_71, 2, x_70);
if (lean::is_scalar(x_61)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_61;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_59);
return x_72;
}
else
{
obj* x_75; obj* x_77; obj* x_78; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_4);
lean::dec(x_1);
x_75 = lean::cnstr_get(x_11, 1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_77 = x_11;
} else {
 lean::inc(x_75);
 lean::dec(x_11);
 x_77 = lean::box(0);
}
x_78 = lean::cnstr_get(x_12, 0);
if (lean::is_exclusive(x_12)) {
 x_80 = x_12;
} else {
 lean::inc(x_78);
 lean::dec(x_12);
 x_80 = lean::box(0);
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_78);
lean::cnstr_set_scalar(x_81, sizeof(void*)*1, x_58);
x_82 = x_81;
if (lean::is_scalar(x_77)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_77;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_75);
return x_83;
}
}
}
else
{
obj* x_86; obj* x_87; obj* x_88; 
lean::dec(x_3);
lean::dec(x_0);
x_86 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_87 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_87, 0, x_1);
lean::cnstr_set(x_87, 1, x_4);
lean::cnstr_set(x_87, 2, x_86);
x_88 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_88, 0, x_87);
lean::cnstr_set(x_88, 1, x_5);
return x_88;
}
}
}
obj* l_Lean_Parser_MonadParsec_foldl___at___private_init_lean_parser_token_4__ident_x_27___spec__20(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_5 = l_String_OldIterator_remaining___main(x_3);
x_6 = l_Lean_Parser_MonadParsec_foldlAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21(x_1, x_0, x_5, x_2, x_3, x_4);
lean::dec(x_5);
x_8 = lean::cnstr_get(x_6, 0);
x_10 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 x_12 = x_6;
} else {
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_6);
 x_12 = lean::box(0);
}
x_13 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_14 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_8);
if (lean::is_scalar(x_12)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_12;
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_10);
return x_15;
}
}
obj* l___private_init_lean_parser_token_4__ident_x_27___lambda__1(obj* x_0, uint32 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_5 = l_mjoin___rarg___closed__1;
x_6 = l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_4__ident_x_27___spec__19(x_5, x_0, x_1, x_2, x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 x_11 = x_6;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_7);
if (lean::is_scalar(x_11)) {
 x_13 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_13 = x_11;
}
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_9);
return x_13;
}
}
obj* l___private_init_lean_parser_token_4__ident_x_27___lambda__2(uint32 x_0, uint32 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_0, x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_11; obj* x_13; obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_23; 
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_6, 2);
lean::inc(x_13);
lean::dec(x_6);
x_16 = l_Lean_Parser_idPart___at___private_init_lean_parser_token_4__ident_x_27___spec__1(x_2, x_11, x_8);
x_17 = lean::cnstr_get(x_16, 0);
x_19 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 x_21 = x_16;
} else {
 lean::inc(x_17);
 lean::inc(x_19);
 lean::dec(x_16);
 x_21 = lean::box(0);
}
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_17);
if (lean::is_scalar(x_21)) {
 x_23 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_23 = x_21;
}
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_19);
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; uint8 x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_24 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_26 = x_5;
} else {
 lean::inc(x_24);
 lean::dec(x_5);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_6, 0);
x_29 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_30 = x_6;
} else {
 lean::inc(x_27);
 lean::dec(x_6);
 x_30 = lean::box(0);
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_27);
lean::cnstr_set_scalar(x_31, sizeof(void*)*1, x_29);
x_32 = x_31;
if (lean::is_scalar(x_26)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_26;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_24);
return x_33;
}
}
}
obj* _init_l___private_init_lean_parser_token_4__ident_x_27___closed__1() {
_start:
{
obj* x_0; obj* x_1; uint32 x_2; obj* x_3; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
x_2 = 46;
x_3 = lean::box_uint32(x_2);
lean::inc(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_token_4__ident_x_27___lambda__1___boxed), 5, 2);
lean::closure_set(x_5, 0, x_1);
lean::closure_set(x_5, 1, x_3);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_token_4__ident_x_27___lambda__2___boxed), 5, 1);
lean::closure_set(x_6, 0, x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l___private_init_lean_parser_token_4__ident_x_27(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; 
lean::inc(x_1);
x_4 = l_Lean_Parser_idPart___at___private_init_lean_parser_token_4__ident_x_27___spec__1(x_0, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_10; obj* x_12; obj* x_14; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_5, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 1);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_5, 2);
lean::inc(x_14);
lean::dec(x_5);
x_17 = lean::box(0);
x_18 = lean_name_mk_string(x_17, x_10);
x_19 = l___private_init_lean_parser_token_4__ident_x_27___closed__1;
x_20 = l_Lean_Parser_MonadParsec_foldl___at___private_init_lean_parser_token_4__ident_x_27___spec__20(x_18, x_19, x_0, x_12, x_7);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_23; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_35; obj* x_36; obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_23 = lean::cnstr_get(x_20, 1);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_release(x_20, 0);
 x_25 = x_20;
} else {
 lean::inc(x_23);
 lean::dec(x_20);
 x_25 = lean::box(0);
}
x_26 = lean::cnstr_get(x_21, 0);
x_28 = lean::cnstr_get(x_21, 1);
x_30 = lean::cnstr_get(x_21, 2);
if (lean::is_exclusive(x_21)) {
 x_32 = x_21;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::inc(x_30);
 lean::dec(x_21);
 x_32 = lean::box(0);
}
lean::inc(x_1);
lean::inc(x_1);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_1);
lean::cnstr_set(x_35, 1, x_1);
x_36 = lean::cnstr_get(x_1, 1);
lean::inc(x_36);
lean::inc(x_28);
lean::inc(x_28);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_28);
lean::cnstr_set(x_40, 1, x_28);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_35);
lean::cnstr_set(x_41, 1, x_36);
lean::cnstr_set(x_41, 2, x_40);
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::inc(x_28);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_1);
lean::cnstr_set(x_44, 1, x_28);
x_45 = lean::box(0);
x_46 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_46, 0, x_42);
lean::cnstr_set(x_46, 1, x_44);
lean::cnstr_set(x_46, 2, x_26);
lean::cnstr_set(x_46, 3, x_45);
lean::cnstr_set(x_46, 4, x_45);
x_47 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_47, 0, x_46);
x_48 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_32)) {
 x_49 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_49 = x_32;
}
lean::cnstr_set(x_49, 0, x_47);
lean::cnstr_set(x_49, 1, x_28);
lean::cnstr_set(x_49, 2, x_48);
x_50 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_30, x_49);
x_51 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_50);
x_52 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_51);
if (lean::is_scalar(x_25)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_25;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_23);
return x_54;
}
else
{
obj* x_56; obj* x_58; obj* x_59; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_1);
x_56 = lean::cnstr_get(x_20, 1);
if (lean::is_exclusive(x_20)) {
 lean::cnstr_release(x_20, 0);
 x_58 = x_20;
} else {
 lean::inc(x_56);
 lean::dec(x_20);
 x_58 = lean::box(0);
}
x_59 = lean::cnstr_get(x_21, 0);
x_61 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
if (lean::is_exclusive(x_21)) {
 x_62 = x_21;
} else {
 lean::inc(x_59);
 lean::dec(x_21);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_59);
lean::cnstr_set_scalar(x_63, sizeof(void*)*1, x_61);
x_64 = x_63;
x_65 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_64);
x_66 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_67 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_66, x_65);
if (lean::is_scalar(x_58)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_58;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_56);
return x_68;
}
}
else
{
obj* x_71; obj* x_73; obj* x_74; uint8 x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_1);
lean::dec(x_0);
x_71 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_73 = x_4;
} else {
 lean::inc(x_71);
 lean::dec(x_4);
 x_73 = lean::box(0);
}
x_74 = lean::cnstr_get(x_5, 0);
x_76 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_77 = x_5;
} else {
 lean::inc(x_74);
 lean::dec(x_5);
 x_77 = lean::box(0);
}
if (lean::is_scalar(x_77)) {
 x_78 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_78 = x_77;
}
lean::cnstr_set(x_78, 0, x_74);
lean::cnstr_set_scalar(x_78, sizeof(void*)*1, x_76);
x_79 = x_78;
x_80 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_81 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_80, x_79);
if (lean::is_scalar(x_73)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_73;
}
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_71);
return x_82;
}
}
}
obj* l_Lean_Parser_MonadParsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_curr___at___private_init_lean_parser_token_4__ident_x_27___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__6(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__8___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__8(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_idPartDefault___at___private_init_lean_parser_token_4__ident_x_27___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_idPartDefault___at___private_init_lean_parser_token_4__ident_x_27___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_4, x_1, x_2, x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__13___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__13(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__15___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__15(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__17___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x_27___spec__17(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at___private_init_lean_parser_token_4__ident_x_27___spec__12___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhile1___at___private_init_lean_parser_token_4__ident_x_27___spec__12(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Parser_idPartEscaped___at___private_init_lean_parser_token_4__ident_x_27___spec__10___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_idPartEscaped___at___private_init_lean_parser_token_4__ident_x_27___spec__10(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Parser_idPart___at___private_init_lean_parser_token_4__ident_x_27___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_idPart___at___private_init_lean_parser_token_4__ident_x_27___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_4__ident_x_27___spec__19___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint32 x_6; obj* x_7; 
x_6 = lean::unbox_uint32(x_2);
x_7 = l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_4__ident_x_27___spec__19(x_0, x_1, x_6, x_3, x_4, x_5);
lean::dec(x_3);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_foldlAux___main___at___private_init_lean_parser_token_4__ident_x_27___spec__21(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l___private_init_lean_parser_token_4__ident_x_27___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_1);
x_6 = l___private_init_lean_parser_token_4__ident_x_27___lambda__1(x_0, x_5, x_2, x_3, x_4);
lean::dec(x_2);
return x_6;
}
}
obj* l___private_init_lean_parser_token_4__ident_x_27___lambda__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; uint32 x_6; obj* x_7; 
x_5 = lean::unbox_uint32(x_0);
x_6 = lean::unbox_uint32(x_1);
x_7 = l___private_init_lean_parser_token_4__ident_x_27___lambda__2(x_5, x_6, x_2, x_3, x_4);
lean::dec(x_2);
return x_7;
}
}
obj* l_ReaderT_orelse___at_Lean_Parser_parseBinLit___spec__1___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_7; obj* x_8; 
lean::inc(x_3);
lean::inc(x_2);
x_7 = lean::apply_3(x_0, x_2, x_3, x_4);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_13; obj* x_15; obj* x_16; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_15 = x_7;
} else {
 lean::inc(x_13);
 lean::dec(x_7);
 x_15 = lean::box(0);
}
if (lean::is_scalar(x_15)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_15;
}
lean::cnstr_set(x_16, 0, x_8);
lean::cnstr_set(x_16, 1, x_13);
return x_16;
}
else
{
uint8 x_17; 
x_17 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (x_17 == 0)
{
obj* x_18; obj* x_21; obj* x_24; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; 
x_18 = lean::cnstr_get(x_7, 1);
lean::inc(x_18);
lean::dec(x_7);
x_21 = lean::cnstr_get(x_8, 0);
lean::inc(x_21);
lean::dec(x_8);
x_24 = lean::apply_3(x_1, x_2, x_3, x_18);
x_25 = lean::cnstr_get(x_24, 0);
x_27 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 x_29 = x_24;
} else {
 lean::inc(x_25);
 lean::inc(x_27);
 lean::dec(x_24);
 x_29 = lean::box(0);
}
x_30 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_21, x_25);
if (lean::is_scalar(x_29)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_29;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_27);
return x_31;
}
else
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_1);
lean::dec(x_3);
lean::dec(x_2);
x_35 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_37 = x_7;
} else {
 lean::inc(x_35);
 lean::dec(x_7);
 x_37 = lean::box(0);
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_8);
lean::cnstr_set(x_38, 1, x_35);
return x_38;
}
}
}
}
obj* l_ReaderT_orelse___at_Lean_Parser_parseBinLit___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_orelse___at_Lean_Parser_parseBinLit___spec__1___rarg), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27___main___at_Lean_Parser_parseBinLit___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
obj* x_9; obj* x_10; 
lean::inc(x_2);
lean::inc(x_0);
x_9 = lean::apply_3(x_0, x_2, x_3, x_4);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_25; 
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
lean::dec(x_9);
x_15 = lean::cnstr_get(x_10, 1);
x_17 = lean::cnstr_get(x_10, 2);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_set(x_10, 1, lean::box(0));
 lean::cnstr_set(x_10, 2, lean::box(0));
 x_19 = x_10;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_10);
 x_19 = lean::box(0);
}
x_20 = lean::mk_nat_obj(1u);
x_21 = lean::nat_sub(x_1, x_20);
lean::inc(x_15);
x_23 = l_Lean_Parser_MonadParsec_many1Aux_x_27___main___at_Lean_Parser_parseBinLit___spec__2(x_0, x_21, x_2, x_15, x_12);
lean::dec(x_21);
x_25 = lean::cnstr_get(x_23, 0);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
lean::dec(x_15);
lean::dec(x_19);
x_29 = lean::cnstr_get(x_23, 1);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 x_31 = x_23;
} else {
 lean::inc(x_29);
 lean::dec(x_23);
 x_31 = lean::box(0);
}
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_25);
if (lean::is_scalar(x_31)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_31;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_29);
return x_33;
}
else
{
uint8 x_34; 
x_34 = lean::cnstr_get_scalar<uint8>(x_25, sizeof(void*)*1);
if (x_34 == 0)
{
obj* x_35; obj* x_37; obj* x_38; obj* x_41; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_35 = lean::cnstr_get(x_23, 1);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 x_37 = x_23;
} else {
 lean::inc(x_35);
 lean::dec(x_23);
 x_37 = lean::box(0);
}
x_38 = lean::cnstr_get(x_25, 0);
lean::inc(x_38);
lean::dec(x_25);
x_41 = lean::cnstr_get(x_38, 2);
lean::inc(x_41);
lean::dec(x_38);
x_44 = l_mjoin___rarg___closed__1;
x_45 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_45, 0, x_41);
lean::closure_set(x_45, 1, x_44);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_45);
x_47 = lean::box(0);
if (lean::is_scalar(x_19)) {
 x_48 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_48 = x_19;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_15);
lean::cnstr_set(x_48, 2, x_46);
x_49 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_48);
if (lean::is_scalar(x_37)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_37;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_35);
return x_50;
}
else
{
obj* x_53; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_15);
lean::dec(x_19);
x_53 = lean::cnstr_get(x_23, 1);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 x_55 = x_23;
} else {
 lean::inc(x_53);
 lean::dec(x_23);
 x_55 = lean::box(0);
}
x_56 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_25);
if (lean::is_scalar(x_55)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_55;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_53);
return x_57;
}
}
}
else
{
obj* x_60; obj* x_62; obj* x_63; uint8 x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_0);
lean::dec(x_2);
x_60 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_62 = x_9;
} else {
 lean::inc(x_60);
 lean::dec(x_9);
 x_62 = lean::box(0);
}
x_63 = lean::cnstr_get(x_10, 0);
x_65 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 x_66 = x_10;
} else {
 lean::inc(x_63);
 lean::dec(x_10);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_63);
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_65);
x_68 = x_67;
if (lean::is_scalar(x_62)) {
 x_69 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_69 = x_62;
}
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_60);
return x_69;
}
}
else
{
obj* x_70; obj* x_71; 
x_70 = lean::apply_3(x_0, x_2, x_3, x_4);
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
if (lean::obj_tag(x_71) == 0)
{
obj* x_73; obj* x_75; obj* x_76; obj* x_78; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_73 = lean::cnstr_get(x_70, 1);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_release(x_70, 0);
 x_75 = x_70;
} else {
 lean::inc(x_73);
 lean::dec(x_70);
 x_75 = lean::box(0);
}
x_76 = lean::cnstr_get(x_71, 1);
x_78 = lean::cnstr_get(x_71, 2);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 x_80 = x_71;
} else {
 lean::inc(x_76);
 lean::inc(x_78);
 lean::dec(x_71);
 x_80 = lean::box(0);
}
x_81 = lean::box(0);
x_82 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_80)) {
 x_83 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_83 = x_80;
}
lean::cnstr_set(x_83, 0, x_81);
lean::cnstr_set(x_83, 1, x_76);
lean::cnstr_set(x_83, 2, x_82);
x_84 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_78, x_83);
if (lean::is_scalar(x_75)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_75;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_73);
return x_85;
}
else
{
obj* x_86; obj* x_88; obj* x_89; uint8 x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_86 = lean::cnstr_get(x_70, 1);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_release(x_70, 0);
 x_88 = x_70;
} else {
 lean::inc(x_86);
 lean::dec(x_70);
 x_88 = lean::box(0);
}
x_89 = lean::cnstr_get(x_71, 0);
x_91 = lean::cnstr_get_scalar<uint8>(x_71, sizeof(void*)*1);
if (lean::is_exclusive(x_71)) {
 x_92 = x_71;
} else {
 lean::inc(x_89);
 lean::dec(x_71);
 x_92 = lean::box(0);
}
if (lean::is_scalar(x_92)) {
 x_93 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_93 = x_92;
}
lean::cnstr_set(x_93, 0, x_89);
lean::cnstr_set_scalar(x_93, sizeof(void*)*1, x_91);
x_94 = x_93;
if (lean::is_scalar(x_88)) {
 x_95 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_95 = x_88;
}
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_86);
return x_95;
}
}
}
}
obj* _init_l_Lean_Parser_parseBinLit___closed__1() {
_start:
{
uint32 x_0; obj* x_1; obj* x_2; uint32 x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = 48;
x_1 = lean::box_uint32(x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11___boxed), 4, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = 49;
x_4 = lean::box_uint32(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11___boxed), 4, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_orelse___at_Lean_Parser_parseBinLit___spec__1___rarg), 5, 2);
lean::closure_set(x_6, 0, x_2);
lean::closure_set(x_6, 1, x_5);
return x_6;
}
}
obj* l_Lean_Parser_parseBinLit(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_3 = 48;
x_7 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_3, x_0, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_13; obj* x_15; uint32 x_18; obj* x_20; obj* x_21; 
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_8, 2);
lean::inc(x_15);
lean::dec(x_8);
x_18 = 98;
lean::inc(x_13);
x_20 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_18, x_0, x_13, x_10);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_24; obj* x_27; 
lean::dec(x_13);
x_24 = lean::cnstr_get(x_20, 1);
lean::inc(x_24);
lean::dec(x_20);
x_27 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_21);
x_4 = x_27;
x_5 = x_24;
goto lbl_6;
}
else
{
obj* x_28; obj* x_31; uint8 x_33; uint32 x_34; 
x_28 = lean::cnstr_get(x_20, 1);
lean::inc(x_28);
lean::dec(x_20);
x_31 = lean::cnstr_get(x_21, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
x_34 = 66;
if (x_33 == 0)
{
obj* x_36; obj* x_37; obj* x_39; obj* x_42; obj* x_43; 
lean::dec(x_21);
x_36 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_34, x_0, x_13, x_28);
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
lean::dec(x_36);
x_42 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_31, x_37);
x_43 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_42);
x_4 = x_43;
x_5 = x_39;
goto lbl_6;
}
else
{
obj* x_46; 
lean::dec(x_13);
lean::dec(x_31);
x_46 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_21);
x_4 = x_46;
x_5 = x_28;
goto lbl_6;
}
}
}
else
{
obj* x_47; obj* x_50; uint8 x_52; obj* x_53; obj* x_54; obj* x_55; 
x_47 = lean::cnstr_get(x_7, 1);
lean::inc(x_47);
lean::dec(x_7);
x_50 = lean::cnstr_get(x_8, 0);
x_52 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_53 = x_8;
} else {
 lean::inc(x_50);
 lean::dec(x_8);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_50);
lean::cnstr_set_scalar(x_54, sizeof(void*)*1, x_52);
x_55 = x_54;
x_4 = x_55;
x_5 = x_47;
goto lbl_6;
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_56; obj* x_58; obj* x_61; obj* x_62; obj* x_63; obj* x_65; obj* x_67; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
x_56 = lean::cnstr_get(x_4, 1);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_4, 2);
lean::inc(x_58);
lean::dec(x_4);
x_61 = l_String_OldIterator_remaining___main(x_56);
x_62 = l_Lean_Parser_parseBinLit___closed__1;
x_63 = l_Lean_Parser_MonadParsec_many1Aux_x_27___main___at_Lean_Parser_parseBinLit___spec__2(x_62, x_61, x_0, x_56, x_5);
lean::dec(x_61);
x_65 = lean::cnstr_get(x_63, 0);
x_67 = lean::cnstr_get(x_63, 1);
if (lean::is_exclusive(x_63)) {
 x_69 = x_63;
} else {
 lean::inc(x_65);
 lean::inc(x_67);
 lean::dec(x_63);
 x_69 = lean::box(0);
}
x_70 = l_Lean_Parser_finishCommentBlock___closed__2;
x_71 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_70, x_65);
x_72 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_71);
if (lean::is_scalar(x_69)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_69;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_67);
return x_73;
}
else
{
obj* x_75; uint8 x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
lean::dec(x_0);
x_75 = lean::cnstr_get(x_4, 0);
x_77 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_78 = x_4;
} else {
 lean::inc(x_75);
 lean::dec(x_4);
 x_78 = lean::box(0);
}
if (lean::is_scalar(x_78)) {
 x_79 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_79 = x_78;
}
lean::cnstr_set(x_79, 0, x_75);
lean::cnstr_set_scalar(x_79, sizeof(void*)*1, x_77);
x_80 = x_79;
x_81 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_5);
return x_81;
}
}
}
}
obj* l_ReaderT_orelse___at_Lean_Parser_parseBinLit___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_ReaderT_orelse___at_Lean_Parser_parseBinLit___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux_x_27___main___at_Lean_Parser_parseBinLit___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_many1Aux_x_27___main___at_Lean_Parser_parseBinLit___spec__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_parseOctLit___spec__3(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
uint8 x_6; 
x_6 = l_String_OldIterator_hasNext___main(x_3);
if (x_6 == 0)
{
obj* x_8; 
lean::dec(x_1);
x_8 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = l_String_OldIterator_curr___main(x_3);
x_10 = x_0 <= x_9;
if (x_10 == 0)
{
obj* x_12; 
lean::dec(x_1);
x_12 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_12;
}
else
{
uint32 x_13; uint8 x_14; 
x_13 = 56;
x_14 = x_9 < x_13;
if (x_14 == 0)
{
obj* x_16; 
lean::dec(x_1);
x_16 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
x_17 = lean::mk_nat_obj(1u);
x_18 = lean::nat_sub(x_1, x_17);
lean::dec(x_1);
x_20 = lean::string_push(x_2, x_9);
x_21 = l_String_OldIterator_next___main(x_3);
x_1 = x_18;
x_2 = x_20;
x_3 = x_21;
goto _start;
}
}
}
}
else
{
obj* x_24; 
lean::dec(x_1);
x_24 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_24;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseOctLit___spec__2(uint32 x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_String_OldIterator_remaining___main(x_3);
x_6 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_parseOctLit___spec__3(x_0, x_5, x_1, x_3);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_4);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseOctLit___spec__1(uint32 x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_7; 
x_7 = l_String_OldIterator_hasNext___main(x_2);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_18; obj* x_19; 
x_8 = lean::box(0);
x_9 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_10 = l_mjoin___rarg___closed__1;
x_11 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_9, x_10, x_8, x_8, x_1, x_2, x_3);
lean::dec(x_2);
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_11, 1);
lean::inc(x_15);
lean::dec(x_11);
x_18 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_19 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_13);
x_4 = x_19;
x_5 = x_15;
goto lbl_6;
}
else
{
uint32 x_20; uint8 x_21; 
x_20 = l_String_OldIterator_curr___main(x_2);
x_21 = x_0 <= x_20;
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_33; obj* x_36; obj* x_37; 
x_22 = l_Char_quoteCore(x_20);
x_23 = l_Char_HasRepr___closed__1;
x_24 = lean::string_append(x_23, x_22);
lean::dec(x_22);
x_26 = lean::string_append(x_24, x_23);
x_27 = lean::box(0);
x_28 = l_mjoin___rarg___closed__1;
x_29 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_26, x_28, x_27, x_27, x_1, x_2, x_3);
lean::dec(x_2);
x_31 = lean::cnstr_get(x_29, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_29, 1);
lean::inc(x_33);
lean::dec(x_29);
x_36 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_37 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_36, x_31);
x_4 = x_37;
x_5 = x_33;
goto lbl_6;
}
else
{
uint32 x_38; uint8 x_39; 
x_38 = 56;
x_39 = x_20 < x_38;
if (x_39 == 0)
{
obj* x_40; obj* x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_49; obj* x_51; obj* x_54; obj* x_55; 
x_40 = l_Char_quoteCore(x_20);
x_41 = l_Char_HasRepr___closed__1;
x_42 = lean::string_append(x_41, x_40);
lean::dec(x_40);
x_44 = lean::string_append(x_42, x_41);
x_45 = lean::box(0);
x_46 = l_mjoin___rarg___closed__1;
x_47 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_44, x_46, x_45, x_45, x_1, x_2, x_3);
lean::dec(x_2);
x_49 = lean::cnstr_get(x_47, 0);
lean::inc(x_49);
x_51 = lean::cnstr_get(x_47, 1);
lean::inc(x_51);
lean::dec(x_47);
x_54 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_55 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_54, x_49);
x_4 = x_55;
x_5 = x_51;
goto lbl_6;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_56 = l_String_OldIterator_next___main(x_2);
x_57 = lean::box(0);
x_58 = lean::box_uint32(x_20);
x_59 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_56);
lean::cnstr_set(x_59, 2, x_57);
x_4 = x_59;
x_5 = x_3;
goto lbl_6;
}
}
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_60; obj* x_62; obj* x_64; obj* x_67; uint32 x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_73; obj* x_75; obj* x_76; obj* x_77; 
x_60 = lean::cnstr_get(x_4, 0);
lean::inc(x_60);
x_62 = lean::cnstr_get(x_4, 1);
lean::inc(x_62);
x_64 = lean::cnstr_get(x_4, 2);
lean::inc(x_64);
lean::dec(x_4);
x_67 = l_String_splitAux___main___closed__1;
x_68 = lean::unbox_uint32(x_60);
x_69 = lean::string_push(x_67, x_68);
x_70 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseOctLit___spec__2(x_0, x_69, x_1, x_62, x_5);
x_71 = lean::cnstr_get(x_70, 0);
x_73 = lean::cnstr_get(x_70, 1);
if (lean::is_exclusive(x_70)) {
 x_75 = x_70;
} else {
 lean::inc(x_71);
 lean::inc(x_73);
 lean::dec(x_70);
 x_75 = lean::box(0);
}
x_76 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_64, x_71);
if (lean::is_scalar(x_75)) {
 x_77 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_77 = x_75;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_73);
return x_77;
}
else
{
obj* x_78; uint8 x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_78 = lean::cnstr_get(x_4, 0);
x_80 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_81 = x_4;
} else {
 lean::inc(x_78);
 lean::dec(x_4);
 x_81 = lean::box(0);
}
if (lean::is_scalar(x_81)) {
 x_82 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_82 = x_81;
}
lean::cnstr_set(x_82, 0, x_78);
lean::cnstr_set_scalar(x_82, sizeof(void*)*1, x_80);
x_83 = x_82;
x_84 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_5);
return x_84;
}
}
}
}
obj* l_Lean_Parser_parseOctLit(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_3 = 48;
x_7 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_3, x_0, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_13; obj* x_15; uint32 x_18; obj* x_20; obj* x_21; 
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_8, 2);
lean::inc(x_15);
lean::dec(x_8);
x_18 = 111;
lean::inc(x_13);
x_20 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_18, x_0, x_13, x_10);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_24; obj* x_27; 
lean::dec(x_13);
x_24 = lean::cnstr_get(x_20, 1);
lean::inc(x_24);
lean::dec(x_20);
x_27 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_21);
x_4 = x_27;
x_5 = x_24;
goto lbl_6;
}
else
{
obj* x_28; obj* x_31; uint8 x_33; uint32 x_34; 
x_28 = lean::cnstr_get(x_20, 1);
lean::inc(x_28);
lean::dec(x_20);
x_31 = lean::cnstr_get(x_21, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
x_34 = 79;
if (x_33 == 0)
{
obj* x_36; obj* x_37; obj* x_39; obj* x_42; obj* x_43; 
lean::dec(x_21);
x_36 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_34, x_0, x_13, x_28);
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
lean::dec(x_36);
x_42 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_31, x_37);
x_43 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_42);
x_4 = x_43;
x_5 = x_39;
goto lbl_6;
}
else
{
obj* x_46; 
lean::dec(x_13);
lean::dec(x_31);
x_46 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_21);
x_4 = x_46;
x_5 = x_28;
goto lbl_6;
}
}
}
else
{
obj* x_47; obj* x_50; uint8 x_52; obj* x_53; obj* x_54; obj* x_55; 
x_47 = lean::cnstr_get(x_7, 1);
lean::inc(x_47);
lean::dec(x_7);
x_50 = lean::cnstr_get(x_8, 0);
x_52 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_53 = x_8;
} else {
 lean::inc(x_50);
 lean::dec(x_8);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_50);
lean::cnstr_set_scalar(x_54, sizeof(void*)*1, x_52);
x_55 = x_54;
x_4 = x_55;
x_5 = x_47;
goto lbl_6;
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_56; obj* x_58; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_68; 
x_56 = lean::cnstr_get(x_4, 1);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_4, 2);
lean::inc(x_58);
lean::dec(x_4);
x_61 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseOctLit___spec__1(x_3, x_0, x_56, x_5);
x_62 = lean::cnstr_get(x_61, 0);
x_64 = lean::cnstr_get(x_61, 1);
if (lean::is_exclusive(x_61)) {
 x_66 = x_61;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::dec(x_61);
 x_66 = lean::box(0);
}
x_67 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_62);
if (lean::is_scalar(x_66)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_66;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_64);
return x_68;
}
else
{
obj* x_69; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_69 = lean::cnstr_get(x_4, 0);
x_71 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_72 = x_4;
} else {
 lean::inc(x_69);
 lean::dec(x_4);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_69);
lean::cnstr_set_scalar(x_73, sizeof(void*)*1, x_71);
x_74 = x_73;
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_5);
return x_75;
}
}
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_parseOctLit___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_parseOctLit___spec__3(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseOctLit___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_0);
x_6 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseOctLit___spec__2(x_5, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseOctLit___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; 
x_4 = lean::unbox_uint32(x_0);
x_5 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseOctLit___spec__1(x_4, x_1, x_2, x_3);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_parseOctLit___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_parseOctLit(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_parseHexLit___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
obj* x_8; obj* x_9; uint32 x_11; uint8 x_12; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_0, x_8);
lean::dec(x_0);
x_11 = l_String_OldIterator_curr___main(x_2);
x_12 = l_Char_isDigit(x_11);
if (x_12 == 0)
{
uint8 x_13; 
x_13 = l_Char_isAlpha(x_11);
if (x_13 == 0)
{
obj* x_15; 
lean::dec(x_9);
x_15 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_15;
}
else
{
obj* x_16; obj* x_17; 
x_16 = lean::string_push(x_1, x_11);
x_17 = l_String_OldIterator_next___main(x_2);
x_0 = x_9;
x_1 = x_16;
x_2 = x_17;
goto _start;
}
}
else
{
obj* x_19; obj* x_20; 
x_19 = lean::string_push(x_1, x_11);
x_20 = l_String_OldIterator_next___main(x_2);
x_0 = x_9;
x_1 = x_19;
x_2 = x_20;
goto _start;
}
}
}
else
{
obj* x_23; 
lean::dec(x_0);
x_23 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_23;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseHexLit___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_parseHexLit___spec__3(x_4, x_0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseHexLit___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; uint8 x_6; 
x_6 = l_String_OldIterator_hasNext___main(x_1);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_17; obj* x_18; 
x_7 = lean::box(0);
x_8 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_9 = l_mjoin___rarg___closed__1;
x_10 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_8, x_9, x_7, x_7, x_0, x_1, x_2);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_10, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_10, 1);
lean::inc(x_14);
lean::dec(x_10);
x_17 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_18 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_12);
x_3 = x_18;
x_4 = x_14;
goto lbl_5;
}
else
{
uint32 x_19; uint8 x_20; 
x_19 = l_String_OldIterator_curr___main(x_1);
x_20 = l_Char_isDigit(x_19);
if (x_20 == 0)
{
uint8 x_21; 
x_21 = l_Char_isAlpha(x_19);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_31; obj* x_33; obj* x_36; obj* x_37; 
x_22 = l_Char_quoteCore(x_19);
x_23 = l_Char_HasRepr___closed__1;
x_24 = lean::string_append(x_23, x_22);
lean::dec(x_22);
x_26 = lean::string_append(x_24, x_23);
x_27 = lean::box(0);
x_28 = l_mjoin___rarg___closed__1;
x_29 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_26, x_28, x_27, x_27, x_0, x_1, x_2);
lean::dec(x_1);
x_31 = lean::cnstr_get(x_29, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_29, 1);
lean::inc(x_33);
lean::dec(x_29);
x_36 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_37 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_36, x_31);
x_3 = x_37;
x_4 = x_33;
goto lbl_5;
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_38 = l_String_OldIterator_next___main(x_1);
x_39 = lean::box(0);
x_40 = lean::box_uint32(x_19);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_38);
lean::cnstr_set(x_41, 2, x_39);
x_3 = x_41;
x_4 = x_2;
goto lbl_5;
}
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_42 = l_String_OldIterator_next___main(x_1);
x_43 = lean::box(0);
x_44 = lean::box_uint32(x_19);
x_45 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_42);
lean::cnstr_set(x_45, 2, x_43);
x_3 = x_45;
x_4 = x_2;
goto lbl_5;
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_46; obj* x_48; obj* x_50; obj* x_53; uint32 x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_59; obj* x_61; obj* x_62; obj* x_63; 
x_46 = lean::cnstr_get(x_3, 0);
lean::inc(x_46);
x_48 = lean::cnstr_get(x_3, 1);
lean::inc(x_48);
x_50 = lean::cnstr_get(x_3, 2);
lean::inc(x_50);
lean::dec(x_3);
x_53 = l_String_splitAux___main___closed__1;
x_54 = lean::unbox_uint32(x_46);
x_55 = lean::string_push(x_53, x_54);
x_56 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseHexLit___spec__2(x_55, x_0, x_48, x_4);
x_57 = lean::cnstr_get(x_56, 0);
x_59 = lean::cnstr_get(x_56, 1);
if (lean::is_exclusive(x_56)) {
 x_61 = x_56;
} else {
 lean::inc(x_57);
 lean::inc(x_59);
 lean::dec(x_56);
 x_61 = lean::box(0);
}
x_62 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_50, x_57);
if (lean::is_scalar(x_61)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_61;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_59);
return x_63;
}
else
{
obj* x_64; uint8 x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_64 = lean::cnstr_get(x_3, 0);
x_66 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (lean::is_exclusive(x_3)) {
 x_67 = x_3;
} else {
 lean::inc(x_64);
 lean::dec(x_3);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_64);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_66);
x_69 = x_68;
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_4);
return x_70;
}
}
}
}
obj* l_Lean_Parser_parseHexLit(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_3 = 48;
x_7 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_3, x_0, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_13; obj* x_15; uint32 x_18; obj* x_20; obj* x_21; 
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
x_15 = lean::cnstr_get(x_8, 2);
lean::inc(x_15);
lean::dec(x_8);
x_18 = 120;
lean::inc(x_13);
x_20 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_18, x_0, x_13, x_10);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_24; obj* x_27; 
lean::dec(x_13);
x_24 = lean::cnstr_get(x_20, 1);
lean::inc(x_24);
lean::dec(x_20);
x_27 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_21);
x_4 = x_27;
x_5 = x_24;
goto lbl_6;
}
else
{
obj* x_28; obj* x_31; uint8 x_33; uint32 x_34; 
x_28 = lean::cnstr_get(x_20, 1);
lean::inc(x_28);
lean::dec(x_20);
x_31 = lean::cnstr_get(x_21, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
x_34 = 88;
if (x_33 == 0)
{
obj* x_36; obj* x_37; obj* x_39; obj* x_42; obj* x_43; 
lean::dec(x_21);
x_36 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_34, x_0, x_13, x_28);
x_37 = lean::cnstr_get(x_36, 0);
lean::inc(x_37);
x_39 = lean::cnstr_get(x_36, 1);
lean::inc(x_39);
lean::dec(x_36);
x_42 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_31, x_37);
x_43 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_42);
x_4 = x_43;
x_5 = x_39;
goto lbl_6;
}
else
{
obj* x_46; 
lean::dec(x_13);
lean::dec(x_31);
x_46 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_21);
x_4 = x_46;
x_5 = x_28;
goto lbl_6;
}
}
}
else
{
obj* x_47; obj* x_50; uint8 x_52; obj* x_53; obj* x_54; obj* x_55; 
x_47 = lean::cnstr_get(x_7, 1);
lean::inc(x_47);
lean::dec(x_7);
x_50 = lean::cnstr_get(x_8, 0);
x_52 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_53 = x_8;
} else {
 lean::inc(x_50);
 lean::dec(x_8);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_50);
lean::cnstr_set_scalar(x_54, sizeof(void*)*1, x_52);
x_55 = x_54;
x_4 = x_55;
x_5 = x_47;
goto lbl_6;
}
lbl_6:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_56; obj* x_58; obj* x_61; obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_68; 
x_56 = lean::cnstr_get(x_4, 1);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_4, 2);
lean::inc(x_58);
lean::dec(x_4);
x_61 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseHexLit___spec__1(x_0, x_56, x_5);
x_62 = lean::cnstr_get(x_61, 0);
x_64 = lean::cnstr_get(x_61, 1);
if (lean::is_exclusive(x_61)) {
 x_66 = x_61;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::dec(x_61);
 x_66 = lean::box(0);
}
x_67 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_62);
if (lean::is_scalar(x_66)) {
 x_68 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_68 = x_66;
}
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_64);
return x_68;
}
else
{
obj* x_69; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_69 = lean::cnstr_get(x_4, 0);
x_71 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (lean::is_exclusive(x_4)) {
 x_72 = x_4;
} else {
 lean::inc(x_69);
 lean::dec(x_4);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_69);
lean::cnstr_set_scalar(x_73, sizeof(void*)*1, x_71);
x_74 = x_73;
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_5);
return x_75;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseHexLit___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseHexLit___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseHexLit___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseHexLit___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Parser_parseHexLit___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_parseHexLit(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* _init_l_Lean_Parser_number() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("number");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_number_HasView_x_27___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_number_HasView_x_27___lambda__1___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_number_HasView_x_27___lambda__1___closed__3() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_number_HasView_x_27___lambda__1___closed__4() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::box(0);
x_1 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_number_HasView_x_27___lambda__1___closed__5() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_number_HasView_x_27___lambda__1___closed__4;
return x_0;
}
}
obj* _init_l_Lean_Parser_number_HasView_x_27___lambda__1___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("number");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* l_Lean_Parser_number_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_number_HasView_x_27___lambda__1___closed__5;
return x_2;
}
else
{
obj* x_3; obj* x_6; obj* x_8; obj* x_11; uint8 x_12; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_6 = lean::cnstr_get(x_3, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_3, 1);
lean::inc(x_8);
lean::dec(x_3);
x_11 = l_Lean_Parser_number_HasView_x_27___lambda__1___closed__6;
x_12 = lean_name_dec_eq(x_6, x_11);
lean::dec(x_6);
if (x_12 == 0)
{
obj* x_15; 
lean::dec(x_8);
x_15 = l_Lean_Parser_number_HasView_x_27___lambda__1___closed__5;
return x_15;
}
else
{
if (lean::obj_tag(x_8) == 0)
{
obj* x_16; 
x_16 = l_Lean_Parser_number_HasView_x_27___lambda__1___closed__5;
return x_16;
}
else
{
obj* x_17; 
x_17 = lean::cnstr_get(x_8, 1);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_19; obj* x_22; 
x_19 = lean::cnstr_get(x_8, 0);
lean::inc(x_19);
lean::dec(x_8);
x_22 = l_Lean_Parser_Syntax_asNode___main(x_19);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; 
x_23 = l_Lean_Parser_number_HasView_x_27___lambda__1___closed__5;
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; 
x_24 = lean::cnstr_get(x_22, 0);
if (lean::is_exclusive(x_22)) {
 lean::cnstr_set(x_22, 0, lean::box(0));
 x_26 = x_22;
} else {
 lean::inc(x_24);
 lean::dec(x_22);
 x_26 = lean::box(0);
}
x_27 = lean::cnstr_get(x_24, 0);
lean::inc(x_27);
switch (lean::obj_tag(x_27)) {
case 0:
{
obj* x_31; 
lean::dec(x_26);
lean::dec(x_24);
x_31 = l_Lean_Parser_number_HasView_x_27___lambda__1___closed__5;
return x_31;
}
case 1:
{
obj* x_35; 
lean::dec(x_26);
lean::dec(x_27);
lean::dec(x_24);
x_35 = l_Lean_Parser_number_HasView_x_27___lambda__1___closed__5;
return x_35;
}
default:
{
obj* x_36; obj* x_39; obj* x_41; obj* x_44; uint8 x_45; 
x_36 = lean::cnstr_get(x_24, 1);
lean::inc(x_36);
lean::dec(x_24);
x_39 = lean::cnstr_get(x_27, 0);
lean::inc(x_39);
x_41 = lean::cnstr_get(x_27, 1);
lean::inc(x_41);
lean::dec(x_27);
x_44 = lean::box(0);
x_45 = lean_name_dec_eq(x_39, x_44);
lean::dec(x_39);
if (x_45 == 0)
{
obj* x_50; 
lean::dec(x_26);
lean::dec(x_41);
lean::dec(x_36);
x_50 = l_Lean_Parser_number_HasView_x_27___lambda__1___closed__5;
return x_50;
}
else
{
if (lean::obj_tag(x_36) == 0)
{
obj* x_53; 
lean::dec(x_26);
lean::dec(x_41);
x_53 = l_Lean_Parser_number_HasView_x_27___lambda__1___closed__5;
return x_53;
}
else
{
obj* x_54; 
x_54 = lean::cnstr_get(x_36, 1);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_56; obj* x_59; uint8 x_60; 
x_56 = lean::cnstr_get(x_36, 0);
lean::inc(x_56);
lean::dec(x_36);
x_59 = lean::mk_nat_obj(0u);
x_60 = lean::nat_dec_eq(x_41, x_59);
if (x_60 == 0)
{
obj* x_61; uint8 x_62; 
x_61 = lean::mk_nat_obj(1u);
x_62 = lean::nat_dec_eq(x_41, x_61);
if (x_62 == 0)
{
obj* x_63; uint8 x_64; 
x_63 = lean::mk_nat_obj(2u);
x_64 = lean::nat_dec_eq(x_41, x_63);
lean::dec(x_41);
if (x_64 == 0)
{
switch (lean::obj_tag(x_56)) {
case 0:
{
obj* x_66; obj* x_69; obj* x_70; 
x_66 = lean::cnstr_get(x_56, 0);
lean::inc(x_66);
lean::dec(x_56);
if (lean::is_scalar(x_26)) {
 x_69 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_69 = x_26;
}
lean::cnstr_set(x_69, 0, x_66);
x_70 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_70, 0, x_69);
return x_70;
}
case 3:
{
obj* x_72; 
lean::dec(x_26);
x_72 = l_Lean_Parser_number_HasView_x_27___lambda__1___closed__1;
return x_72;
}
default:
{
obj* x_75; 
lean::dec(x_56);
lean::dec(x_26);
x_75 = l_Lean_Parser_number_HasView_x_27___lambda__1___closed__1;
return x_75;
}
}
}
else
{
switch (lean::obj_tag(x_56)) {
case 0:
{
obj* x_76; obj* x_79; obj* x_80; 
x_76 = lean::cnstr_get(x_56, 0);
lean::inc(x_76);
lean::dec(x_56);
if (lean::is_scalar(x_26)) {
 x_79 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_79 = x_26;
}
lean::cnstr_set(x_79, 0, x_76);
x_80 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_80, 0, x_79);
return x_80;
}
case 3:
{
obj* x_82; 
lean::dec(x_26);
x_82 = l_Lean_Parser_number_HasView_x_27___lambda__1___closed__2;
return x_82;
}
default:
{
obj* x_85; 
lean::dec(x_56);
lean::dec(x_26);
x_85 = l_Lean_Parser_number_HasView_x_27___lambda__1___closed__2;
return x_85;
}
}
}
}
else
{
lean::dec(x_41);
switch (lean::obj_tag(x_56)) {
case 0:
{
obj* x_87; obj* x_90; obj* x_91; 
x_87 = lean::cnstr_get(x_56, 0);
lean::inc(x_87);
lean::dec(x_56);
if (lean::is_scalar(x_26)) {
 x_90 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_90 = x_26;
}
lean::cnstr_set(x_90, 0, x_87);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
return x_91;
}
case 3:
{
obj* x_93; 
lean::dec(x_26);
x_93 = l_Lean_Parser_number_HasView_x_27___lambda__1___closed__3;
return x_93;
}
default:
{
obj* x_96; 
lean::dec(x_56);
lean::dec(x_26);
x_96 = l_Lean_Parser_number_HasView_x_27___lambda__1___closed__3;
return x_96;
}
}
}
}
else
{
lean::dec(x_41);
switch (lean::obj_tag(x_56)) {
case 0:
{
obj* x_98; obj* x_101; obj* x_102; 
x_98 = lean::cnstr_get(x_56, 0);
lean::inc(x_98);
lean::dec(x_56);
if (lean::is_scalar(x_26)) {
 x_101 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_101 = x_26;
}
lean::cnstr_set(x_101, 0, x_98);
x_102 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_102, 0, x_101);
return x_102;
}
case 3:
{
obj* x_104; 
lean::dec(x_26);
x_104 = l_Lean_Parser_number_HasView_x_27___lambda__1___closed__4;
return x_104;
}
default:
{
obj* x_107; 
lean::dec(x_56);
lean::dec(x_26);
x_107 = l_Lean_Parser_number_HasView_x_27___lambda__1___closed__4;
return x_107;
}
}
}
}
else
{
obj* x_112; 
lean::dec(x_26);
lean::dec(x_41);
lean::dec(x_54);
lean::dec(x_36);
x_112 = l_Lean_Parser_number_HasView_x_27___lambda__1___closed__5;
return x_112;
}
}
}
}
}
}
}
else
{
obj* x_115; 
lean::dec(x_8);
lean::dec(x_17);
x_115 = l_Lean_Parser_number_HasView_x_27___lambda__1___closed__5;
return x_115;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_number_HasView_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean_name_mk_numeral(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean::box(3);
x_6 = l_Option_getOrElse___main___rarg(x_4, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_Lean_Parser_Syntax_mkNode(x_3, x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_0);
x_10 = l_Lean_Parser_number;
x_11 = l_Lean_Parser_Syntax_mkNode(x_10, x_9);
return x_11;
}
}
obj* _init_l_Lean_Parser_number_HasView_x_27___lambda__2___closed__2() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(1u);
x_3 = lean_name_mk_numeral(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean::box(3);
x_6 = l_Option_getOrElse___main___rarg(x_4, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_Lean_Parser_Syntax_mkNode(x_3, x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_0);
x_10 = l_Lean_Parser_number;
x_11 = l_Lean_Parser_Syntax_mkNode(x_10, x_9);
return x_11;
}
}
obj* _init_l_Lean_Parser_number_HasView_x_27___lambda__2___closed__3() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(2u);
x_3 = lean_name_mk_numeral(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean::box(3);
x_6 = l_Option_getOrElse___main___rarg(x_4, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_Lean_Parser_Syntax_mkNode(x_3, x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_0);
x_10 = l_Lean_Parser_number;
x_11 = l_Lean_Parser_Syntax_mkNode(x_10, x_9);
return x_11;
}
}
obj* _init_l_Lean_Parser_number_HasView_x_27___lambda__2___closed__4() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(2u);
x_2 = lean_name_mk_numeral(x_0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_number_HasView_x_27___lambda__2___closed__5() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(3u);
x_3 = lean_name_mk_numeral(x_1, x_2);
x_4 = lean::box(0);
x_5 = lean::box(3);
x_6 = l_Option_getOrElse___main___rarg(x_4, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_0);
x_8 = l_Lean_Parser_Syntax_mkNode(x_3, x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_0);
x_10 = l_Lean_Parser_number;
x_11 = l_Lean_Parser_Syntax_mkNode(x_10, x_9);
return x_11;
}
}
obj* _init_l_Lean_Parser_number_HasView_x_27___lambda__2___closed__6() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_nat_obj(3u);
x_2 = lean_name_mk_numeral(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Parser_number_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::box(0);
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_0, 0);
lean::inc(x_2);
lean::dec(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_number_HasView_x_27___lambda__2___closed__1;
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_6 = lean::cnstr_get(x_2, 0);
if (lean::is_exclusive(x_2)) {
 x_8 = x_2;
} else {
 lean::inc(x_6);
 lean::dec(x_2);
 x_8 = lean::box(0);
}
x_9 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_9, 0, x_6);
if (lean::is_scalar(x_8)) {
 x_10 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_10 = x_8;
}
lean::cnstr_set(x_10, 0, x_9);
x_11 = lean::box(3);
x_12 = l_Option_getOrElse___main___rarg(x_10, x_11);
lean::dec(x_10);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_1);
x_15 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__1;
x_16 = l_Lean_Parser_Syntax_mkNode(x_15, x_14);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_1);
x_18 = l_Lean_Parser_number;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
return x_19;
}
}
case 1:
{
obj* x_20; 
x_20 = lean::cnstr_get(x_0, 0);
lean::inc(x_20);
lean::dec(x_0);
if (lean::obj_tag(x_20) == 0)
{
obj* x_23; 
x_23 = l_Lean_Parser_number_HasView_x_27___lambda__2___closed__2;
return x_23;
}
else
{
obj* x_24; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_24 = lean::cnstr_get(x_20, 0);
if (lean::is_exclusive(x_20)) {
 x_26 = x_20;
} else {
 lean::inc(x_24);
 lean::dec(x_20);
 x_26 = lean::box(0);
}
x_27 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_27, 0, x_24);
if (lean::is_scalar(x_26)) {
 x_28 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_28 = x_26;
}
lean::cnstr_set(x_28, 0, x_27);
x_29 = lean::box(3);
x_30 = l_Option_getOrElse___main___rarg(x_28, x_29);
lean::dec(x_28);
x_32 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set(x_32, 1, x_1);
x_33 = l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__3;
x_34 = l_Lean_Parser_Syntax_mkNode(x_33, x_32);
x_35 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_1);
x_36 = l_Lean_Parser_number;
x_37 = l_Lean_Parser_Syntax_mkNode(x_36, x_35);
return x_37;
}
}
case 2:
{
obj* x_38; 
x_38 = lean::cnstr_get(x_0, 0);
lean::inc(x_38);
lean::dec(x_0);
if (lean::obj_tag(x_38) == 0)
{
obj* x_41; 
x_41 = l_Lean_Parser_number_HasView_x_27___lambda__2___closed__3;
return x_41;
}
else
{
obj* x_42; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_42 = lean::cnstr_get(x_38, 0);
if (lean::is_exclusive(x_38)) {
 x_44 = x_38;
} else {
 lean::inc(x_42);
 lean::dec(x_38);
 x_44 = lean::box(0);
}
x_45 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_45, 0, x_42);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_45);
x_47 = lean::box(3);
x_48 = l_Option_getOrElse___main___rarg(x_46, x_47);
lean::dec(x_46);
x_50 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_1);
x_51 = l_Lean_Parser_number_HasView_x_27___lambda__2___closed__4;
x_52 = l_Lean_Parser_Syntax_mkNode(x_51, x_50);
x_53 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_1);
x_54 = l_Lean_Parser_number;
x_55 = l_Lean_Parser_Syntax_mkNode(x_54, x_53);
return x_55;
}
}
default:
{
obj* x_56; 
x_56 = lean::cnstr_get(x_0, 0);
lean::inc(x_56);
lean::dec(x_0);
if (lean::obj_tag(x_56) == 0)
{
obj* x_59; 
x_59 = l_Lean_Parser_number_HasView_x_27___lambda__2___closed__5;
return x_59;
}
else
{
obj* x_60; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
x_60 = lean::cnstr_get(x_56, 0);
if (lean::is_exclusive(x_56)) {
 x_62 = x_56;
} else {
 lean::inc(x_60);
 lean::dec(x_56);
 x_62 = lean::box(0);
}
x_63 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_63, 0, x_60);
if (lean::is_scalar(x_62)) {
 x_64 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_64 = x_62;
}
lean::cnstr_set(x_64, 0, x_63);
x_65 = lean::box(3);
x_66 = l_Option_getOrElse___main___rarg(x_64, x_65);
lean::dec(x_64);
x_68 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_68, 0, x_66);
lean::cnstr_set(x_68, 1, x_1);
x_69 = l_Lean_Parser_number_HasView_x_27___lambda__2___closed__6;
x_70 = l_Lean_Parser_Syntax_mkNode(x_69, x_68);
x_71 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_1);
x_72 = l_Lean_Parser_number;
x_73 = l_Lean_Parser_Syntax_mkNode(x_72, x_71);
return x_73;
}
}
}
}
}
obj* _init_l_Lean_Parser_number_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_number_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_number_HasView_x_27;
return x_0;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_number_x_27___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Char_isDigit(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_OldIterator_next___main(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x_27___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_number_x_27___spec__3(x_4, x_0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_number_x_27___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Char_isDigit(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_OldIterator_next___main(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x_27___spec__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_number_x_27___spec__5(x_4, x_0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_number_x_27___spec__7(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_2);
if (x_5 == 0)
{
obj* x_7; 
lean::dec(x_0);
x_7 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_7;
}
else
{
uint32 x_8; uint8 x_9; 
x_8 = l_String_OldIterator_curr___main(x_2);
x_9 = l_Char_isDigit(x_8);
if (x_9 == 0)
{
obj* x_11; 
lean::dec(x_0);
x_11 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_15; obj* x_16; 
x_12 = lean::mk_nat_obj(1u);
x_13 = lean::nat_sub(x_0, x_12);
lean::dec(x_0);
x_15 = lean::string_push(x_1, x_8);
x_16 = l_String_OldIterator_next___main(x_2);
x_0 = x_13;
x_1 = x_15;
x_2 = x_16;
goto _start;
}
}
}
else
{
obj* x_19; 
lean::dec(x_0);
x_19 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_1, x_2);
return x_19;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x_27___spec__6(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_number_x_27___spec__7(x_4, x_0, x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_3);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_number_x_27___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_String_OldIterator_hasNext___main(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; 
x_4 = lean::box(0);
x_5 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_13 = x_7;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_9);
if (lean::obj_tag(x_15) == 0)
{
obj* x_17; obj* x_19; obj* x_21; obj* x_24; uint32 x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_13);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_19 = lean::cnstr_get(x_15, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_15, 2);
lean::inc(x_21);
lean::dec(x_15);
x_24 = l_String_splitAux___main___closed__1;
x_25 = lean::unbox_uint32(x_17);
x_26 = lean::string_push(x_24, x_25);
x_27 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x_27___spec__2(x_26, x_0, x_19, x_11);
x_28 = lean::cnstr_get(x_27, 0);
x_30 = lean::cnstr_get(x_27, 1);
if (lean::is_exclusive(x_27)) {
 x_32 = x_27;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::dec(x_27);
 x_32 = lean::box(0);
}
x_33 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_28);
if (lean::is_scalar(x_32)) {
 x_34 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_34 = x_32;
}
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_30);
return x_34;
}
else
{
obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_35 = lean::cnstr_get(x_15, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 x_38 = x_15;
} else {
 lean::inc(x_35);
 lean::dec(x_15);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_35);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_37);
x_40 = x_39;
if (lean::is_scalar(x_13)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_13;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_11);
return x_41;
}
}
else
{
uint32 x_42; uint8 x_43; 
x_42 = l_String_OldIterator_curr___main(x_1);
x_43 = l_Char_isDigit(x_42);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_53; obj* x_55; obj* x_57; obj* x_58; obj* x_59; 
x_44 = l_Char_quoteCore(x_42);
x_45 = l_Char_HasRepr___closed__1;
x_46 = lean::string_append(x_45, x_44);
lean::dec(x_44);
x_48 = lean::string_append(x_46, x_45);
x_49 = lean::box(0);
x_50 = l_mjoin___rarg___closed__1;
x_51 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_48, x_50, x_49, x_49, x_0, x_1, x_2);
lean::dec(x_1);
x_53 = lean::cnstr_get(x_51, 0);
x_55 = lean::cnstr_get(x_51, 1);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_set(x_51, 0, lean::box(0));
 lean::cnstr_set(x_51, 1, lean::box(0));
 x_57 = x_51;
} else {
 lean::inc(x_53);
 lean::inc(x_55);
 lean::dec(x_51);
 x_57 = lean::box(0);
}
x_58 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_59 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_53);
if (lean::obj_tag(x_59) == 0)
{
obj* x_61; obj* x_63; obj* x_65; obj* x_68; uint32 x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_74; obj* x_76; obj* x_77; obj* x_78; 
lean::dec(x_57);
x_61 = lean::cnstr_get(x_59, 0);
lean::inc(x_61);
x_63 = lean::cnstr_get(x_59, 1);
lean::inc(x_63);
x_65 = lean::cnstr_get(x_59, 2);
lean::inc(x_65);
lean::dec(x_59);
x_68 = l_String_splitAux___main___closed__1;
x_69 = lean::unbox_uint32(x_61);
x_70 = lean::string_push(x_68, x_69);
x_71 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x_27___spec__4(x_70, x_0, x_63, x_55);
x_72 = lean::cnstr_get(x_71, 0);
x_74 = lean::cnstr_get(x_71, 1);
if (lean::is_exclusive(x_71)) {
 x_76 = x_71;
} else {
 lean::inc(x_72);
 lean::inc(x_74);
 lean::dec(x_71);
 x_76 = lean::box(0);
}
x_77 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_65, x_72);
if (lean::is_scalar(x_76)) {
 x_78 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_78 = x_76;
}
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_74);
return x_78;
}
else
{
obj* x_79; uint8 x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_79 = lean::cnstr_get(x_59, 0);
x_81 = lean::cnstr_get_scalar<uint8>(x_59, sizeof(void*)*1);
if (lean::is_exclusive(x_59)) {
 x_82 = x_59;
} else {
 lean::inc(x_79);
 lean::dec(x_59);
 x_82 = lean::box(0);
}
if (lean::is_scalar(x_82)) {
 x_83 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_83 = x_82;
}
lean::cnstr_set(x_83, 0, x_79);
lean::cnstr_set_scalar(x_83, sizeof(void*)*1, x_81);
x_84 = x_83;
if (lean::is_scalar(x_57)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_57;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_55);
return x_85;
}
}
else
{
obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_92; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_86 = l_String_OldIterator_next___main(x_1);
x_87 = l_String_splitAux___main___closed__1;
x_88 = lean::string_push(x_87, x_42);
x_89 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x_27___spec__6(x_88, x_0, x_86, x_2);
x_90 = lean::cnstr_get(x_89, 0);
x_92 = lean::cnstr_get(x_89, 1);
if (lean::is_exclusive(x_89)) {
 x_94 = x_89;
} else {
 lean::inc(x_90);
 lean::inc(x_92);
 lean::dec(x_89);
 x_94 = lean::box(0);
}
x_95 = lean::box(0);
x_96 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_95, x_90);
if (lean::is_scalar(x_94)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_94;
}
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_92);
return x_97;
}
}
}
}
obj* l_List_map___main___at_Lean_Parser_number_x_27___spec__9___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_9; obj* x_10; 
x_4 = lean::cnstr_get(x_0, 0);
lean::inc(x_4);
x_6 = lean::cnstr_get(x_0, 1);
lean::inc(x_6);
lean::dec(x_0);
x_9 = lean::apply_3(x_6, x_1, x_2, x_3);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_12; obj* x_14; obj* x_15; obj* x_17; obj* x_19; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_12 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_14 = x_9;
} else {
 lean::inc(x_12);
 lean::dec(x_9);
 x_14 = lean::box(0);
}
x_15 = lean::cnstr_get(x_10, 0);
x_17 = lean::cnstr_get(x_10, 1);
x_19 = lean::cnstr_get(x_10, 2);
if (lean::is_exclusive(x_10)) {
 x_21 = x_10;
} else {
 lean::inc(x_15);
 lean::inc(x_17);
 lean::inc(x_19);
 lean::dec(x_10);
 x_21 = lean::box(0);
}
x_22 = lean::box(0);
x_23 = lean_name_mk_numeral(x_22, x_4);
x_24 = lean::box(0);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_15);
lean::cnstr_set(x_25, 1, x_24);
x_26 = l_Lean_Parser_Syntax_mkNode(x_23, x_25);
x_27 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_21)) {
 x_28 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_28 = x_21;
}
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_17);
lean::cnstr_set(x_28, 2, x_27);
x_29 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_19, x_28);
if (lean::is_scalar(x_14)) {
 x_30 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_30 = x_14;
}
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_12);
return x_30;
}
else
{
obj* x_32; obj* x_34; obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_4);
x_32 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_34 = x_9;
} else {
 lean::inc(x_32);
 lean::dec(x_9);
 x_34 = lean::box(0);
}
x_35 = lean::cnstr_get(x_10, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 x_38 = x_10;
} else {
 lean::inc(x_35);
 lean::dec(x_10);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_35);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_37);
x_40 = x_39;
if (lean::is_scalar(x_34)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_34;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_32);
return x_41;
}
}
}
obj* l_List_map___main___at_Lean_Parser_number_x_27___spec__9(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::cnstr_get(x_0, 0);
x_4 = lean::cnstr_get(x_0, 1);
if (lean::is_exclusive(x_0)) {
 x_6 = x_0;
} else {
 lean::inc(x_2);
 lean::inc(x_4);
 lean::dec(x_0);
 x_6 = lean::box(0);
}
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_Lean_Parser_number_x_27___spec__9___lambda__1), 4, 1);
lean::closure_set(x_7, 0, x_2);
x_8 = l_List_map___main___at_Lean_Parser_number_x_27___spec__9(x_4);
if (lean::is_scalar(x_6)) {
 x_9 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_9 = x_6;
}
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_number_x_27___spec__11(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_9; obj* x_10; obj* x_13; obj* x_14; 
lean::inc(x_4);
x_13 = lean::apply_3(x_1, x_3, x_4, x_5);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
obj* x_16; obj* x_19; obj* x_21; obj* x_23; obj* x_25; obj* x_26; 
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
lean::dec(x_13);
x_19 = lean::cnstr_get(x_14, 0);
x_21 = lean::cnstr_get(x_14, 1);
x_23 = lean::cnstr_get(x_14, 2);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_set(x_14, 0, lean::box(0));
 lean::cnstr_set(x_14, 1, lean::box(0));
 lean::cnstr_set(x_14, 2, lean::box(0));
 x_25 = x_14;
} else {
 lean::inc(x_19);
 lean::inc(x_21);
 lean::inc(x_23);
 lean::dec(x_14);
 x_25 = lean::box(0);
}
if (lean::obj_tag(x_2) == 0)
{
obj* x_28; 
x_28 = lean::cnstr_get(x_2, 2);
lean::inc(x_28);
if (lean::obj_tag(x_28) == 0)
{
obj* x_31; obj* x_33; obj* x_35; obj* x_37; uint8 x_40; 
lean::dec(x_25);
x_31 = lean::cnstr_get(x_2, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_2, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_21, 1);
lean::inc(x_35);
x_37 = lean::cnstr_get(x_33, 1);
lean::inc(x_37);
lean::dec(x_33);
x_40 = lean::nat_dec_lt(x_35, x_37);
if (x_40 == 0)
{
obj* x_42; uint8 x_43; 
lean::inc(x_2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 lean::cnstr_release(x_2, 1);
 lean::cnstr_release(x_2, 2);
 x_42 = x_2;
} else {
 lean::dec(x_2);
 x_42 = lean::box(0);
}
x_43 = lean::nat_dec_lt(x_37, x_35);
lean::dec(x_35);
lean::dec(x_37);
if (x_43 == 0)
{
obj* x_46; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_46 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_46, 0, x_19);
lean::cnstr_set(x_46, 1, x_31);
lean::inc(x_21);
if (lean::is_scalar(x_42)) {
 x_48 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_48 = x_42;
}
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_21);
lean::cnstr_set(x_48, 2, x_28);
x_49 = l_Lean_Parser_finishCommentBlock___closed__2;
x_50 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set(x_50, 1, x_21);
lean::cnstr_set(x_50, 2, x_49);
x_51 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_23, x_50);
x_9 = x_51;
x_10 = x_16;
goto lbl_11;
}
else
{
obj* x_53; obj* x_54; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_31);
x_53 = lean::box(0);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_19);
lean::cnstr_set(x_54, 1, x_53);
lean::inc(x_21);
if (lean::is_scalar(x_42)) {
 x_56 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_56 = x_42;
}
lean::cnstr_set(x_56, 0, x_54);
lean::cnstr_set(x_56, 1, x_21);
lean::cnstr_set(x_56, 2, x_28);
x_57 = l_Lean_Parser_finishCommentBlock___closed__2;
x_58 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_21);
lean::cnstr_set(x_58, 2, x_57);
x_59 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_23, x_58);
x_9 = x_59;
x_10 = x_16;
goto lbl_11;
}
}
else
{
obj* x_64; obj* x_66; obj* x_67; 
lean::dec(x_35);
lean::dec(x_37);
lean::dec(x_19);
lean::dec(x_31);
x_64 = l_Lean_Parser_finishCommentBlock___closed__2;
lean::inc(x_2);
x_66 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_66, 0, x_2);
lean::cnstr_set(x_66, 1, x_21);
lean::cnstr_set(x_66, 2, x_64);
x_67 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_23, x_66);
x_9 = x_67;
x_10 = x_16;
goto lbl_11;
}
}
else
{
obj* x_69; 
lean::dec(x_28);
x_69 = lean::box(0);
x_26 = x_69;
goto lbl_27;
}
}
else
{
obj* x_70; 
x_70 = lean::box(0);
x_26 = x_70;
goto lbl_27;
}
lbl_27:
{
obj* x_72; obj* x_73; obj* x_74; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_26);
x_72 = lean::box(0);
x_73 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_73, 0, x_19);
lean::cnstr_set(x_73, 1, x_72);
x_74 = lean::box(0);
lean::inc(x_21);
if (lean::is_scalar(x_25)) {
 x_76 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_76 = x_25;
}
lean::cnstr_set(x_76, 0, x_73);
lean::cnstr_set(x_76, 1, x_21);
lean::cnstr_set(x_76, 2, x_74);
x_77 = l_Lean_Parser_finishCommentBlock___closed__2;
x_78 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_78, 0, x_76);
lean::cnstr_set(x_78, 1, x_21);
lean::cnstr_set(x_78, 2, x_77);
x_79 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_23, x_78);
x_9 = x_79;
x_10 = x_16;
goto lbl_11;
}
}
else
{
obj* x_80; obj* x_83; uint8 x_85; obj* x_86; obj* x_87; obj* x_88; 
x_80 = lean::cnstr_get(x_13, 1);
lean::inc(x_80);
lean::dec(x_13);
x_83 = lean::cnstr_get(x_14, 0);
x_85 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 x_86 = x_14;
} else {
 lean::inc(x_83);
 lean::dec(x_14);
 x_86 = lean::box(0);
}
if (lean::is_scalar(x_86)) {
 x_87 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_87 = x_86;
}
lean::cnstr_set(x_87, 0, x_83);
lean::cnstr_set_scalar(x_87, sizeof(void*)*1, x_85);
x_88 = x_87;
x_9 = x_88;
x_10 = x_80;
goto lbl_11;
}
lbl_8:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_89; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_89 = lean::cnstr_get(x_6, 0);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_91 = x_6;
} else {
 lean::inc(x_89);
 lean::dec(x_6);
 x_91 = lean::box(0);
}
x_92 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_91)) {
 x_93 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_93 = x_91;
}
lean::cnstr_set(x_93, 0, x_89);
lean::cnstr_set(x_93, 1, x_4);
lean::cnstr_set(x_93, 2, x_92);
x_94 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_7);
return x_94;
}
else
{
obj* x_96; 
lean::dec(x_4);
x_96 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_96, 0, x_6);
lean::cnstr_set(x_96, 1, x_7);
return x_96;
}
}
lbl_11:
{
if (lean::obj_tag(x_9) == 0)
{
lean::dec(x_2);
x_6 = x_9;
x_7 = x_10;
goto lbl_8;
}
else
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_98; obj* x_101; obj* x_104; obj* x_105; 
x_98 = lean::cnstr_get(x_9, 0);
lean::inc(x_98);
lean::dec(x_9);
x_101 = lean::cnstr_get(x_98, 0);
lean::inc(x_101);
lean::dec(x_98);
x_104 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_105 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_105, 0, x_2);
lean::cnstr_set(x_105, 1, x_101);
lean::cnstr_set(x_105, 2, x_104);
x_6 = x_105;
x_7 = x_10;
goto lbl_8;
}
else
{
obj* x_106; obj* x_109; obj* x_111; obj* x_113; obj* x_115; obj* x_117; uint8 x_120; 
x_106 = lean::cnstr_get(x_9, 0);
lean::inc(x_106);
lean::dec(x_9);
x_109 = lean::cnstr_get(x_106, 0);
lean::inc(x_109);
x_111 = lean::cnstr_get(x_2, 0);
lean::inc(x_111);
x_113 = lean::cnstr_get(x_109, 1);
lean::inc(x_113);
x_115 = lean::cnstr_get(x_111, 0);
lean::inc(x_115);
x_117 = lean::cnstr_get(x_115, 1);
lean::inc(x_117);
lean::dec(x_115);
x_120 = lean::nat_dec_lt(x_113, x_117);
if (x_120 == 0)
{
obj* x_121; uint8 x_122; 
if (lean::is_exclusive(x_2)) {
 lean::cnstr_release(x_2, 0);
 x_121 = x_2;
} else {
 lean::dec(x_2);
 x_121 = lean::box(0);
}
x_122 = lean::nat_dec_lt(x_117, x_113);
lean::dec(x_117);
if (x_122 == 0)
{
obj* x_124; obj* x_125; uint8 x_126; obj* x_128; obj* x_129; obj* x_130; obj* x_131; 
x_124 = l_Lean_Parser_ParsecT_merge___rarg(x_106, x_111);
x_125 = lean::cnstr_get(x_0, 1);
x_126 = lean::nat_dec_lt(x_125, x_113);
lean::dec(x_113);
if (lean::is_scalar(x_121)) {
 x_128 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_128 = x_121;
}
lean::cnstr_set(x_128, 0, x_124);
lean::cnstr_set_scalar(x_128, sizeof(void*)*1, x_126);
x_129 = x_128;
x_130 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_131 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_131, 0, x_129);
lean::cnstr_set(x_131, 1, x_109);
lean::cnstr_set(x_131, 2, x_130);
x_6 = x_131;
x_7 = x_10;
goto lbl_8;
}
else
{
uint8 x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; 
lean::dec(x_111);
lean::dec(x_113);
x_134 = 1;
if (lean::is_scalar(x_121)) {
 x_135 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_135 = x_121;
}
lean::cnstr_set(x_135, 0, x_106);
lean::cnstr_set_scalar(x_135, sizeof(void*)*1, x_134);
x_136 = x_135;
x_137 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_138 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_138, 0, x_136);
lean::cnstr_set(x_138, 1, x_109);
lean::cnstr_set(x_138, 2, x_137);
x_6 = x_138;
x_7 = x_10;
goto lbl_8;
}
}
else
{
obj* x_143; obj* x_144; 
lean::dec(x_111);
lean::dec(x_117);
lean::dec(x_113);
lean::dec(x_106);
x_143 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_144 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_144, 0, x_2);
lean::cnstr_set(x_144, 1, x_109);
lean::cnstr_set(x_144, 2, x_143);
x_6 = x_144;
x_7 = x_10;
goto lbl_8;
}
}
}
}
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_number_x_27___spec__12___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; 
x_5 = l_Option_getOrElse___main___rarg(x_2, x_4);
x_6 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_0);
lean::cnstr_set(x_6, 2, x_1);
lean::cnstr_set(x_6, 3, x_3);
x_7 = 0;
x_8 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set_scalar(x_8, sizeof(void*)*1, x_7);
x_9 = x_8;
return x_9;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_number_x_27___spec__12(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___at_Lean_Parser_number_x_27___spec__12___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_List_mfoldr___main___at_Lean_Parser_number_x_27___spec__13(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
x_7 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_8 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_8, 0, x_1);
lean::cnstr_set(x_8, 1, x_4);
lean::cnstr_set(x_8, 2, x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_5);
return x_9;
}
else
{
obj* x_10; obj* x_12; obj* x_16; obj* x_17; 
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_2, 1);
lean::inc(x_12);
lean::dec(x_2);
lean::inc(x_3);
x_16 = l_List_mfoldr___main___at_Lean_Parser_number_x_27___spec__13(x_0, x_1, x_12, x_3, x_4, x_5);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
if (lean::obj_tag(x_17) == 0)
{
obj* x_19; obj* x_22; obj* x_24; obj* x_26; obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_35; obj* x_36; 
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
lean::dec(x_16);
x_22 = lean::cnstr_get(x_17, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_17, 1);
lean::inc(x_24);
x_26 = lean::cnstr_get(x_17, 2);
lean::inc(x_26);
lean::dec(x_17);
x_29 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_number_x_27___spec__11(x_0, x_10, x_22, x_3, x_24, x_19);
x_30 = lean::cnstr_get(x_29, 0);
x_32 = lean::cnstr_get(x_29, 1);
if (lean::is_exclusive(x_29)) {
 x_34 = x_29;
} else {
 lean::inc(x_30);
 lean::inc(x_32);
 lean::dec(x_29);
 x_34 = lean::box(0);
}
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_26, x_30);
if (lean::is_scalar(x_34)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_34;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_32);
return x_36;
}
else
{
obj* x_39; obj* x_41; obj* x_42; uint8 x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
lean::dec(x_3);
lean::dec(x_10);
x_39 = lean::cnstr_get(x_16, 1);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_41 = x_16;
} else {
 lean::inc(x_39);
 lean::dec(x_16);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_17, 0);
x_44 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*1);
if (lean::is_exclusive(x_17)) {
 x_45 = x_17;
} else {
 lean::inc(x_42);
 lean::dec(x_17);
 x_45 = lean::box(0);
}
if (lean::is_scalar(x_45)) {
 x_46 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_46 = x_45;
}
lean::cnstr_set(x_46, 0, x_42);
lean::cnstr_set_scalar(x_46, sizeof(void*)*1, x_44);
x_47 = x_46;
if (lean::is_scalar(x_41)) {
 x_48 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_48 = x_41;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_39);
return x_48;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_longestMatch___at_Lean_Parser_number_x_27___spec__10(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; 
x_4 = lean::box(0);
x_5 = l_Lean_Parser_MonadParsec_longestMatch___rarg___lambda__2___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_number_x_27___spec__12___rarg(x_5, x_6, x_4, x_4, x_2);
lean::inc(x_2);
x_9 = l_List_mfoldr___main___at_Lean_Parser_number_x_27___spec__13(x_2, x_7, x_0, x_1, x_2, x_3);
lean::dec(x_2);
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_15; obj* x_16; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_13 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_15 = x_9;
} else {
 lean::inc(x_13);
 lean::dec(x_9);
 x_15 = lean::box(0);
}
x_16 = lean::cnstr_get(x_11, 0);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_11, 2);
lean::inc(x_18);
lean::dec(x_11);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_16);
x_22 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_23 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_21);
if (lean::is_scalar(x_15)) {
 x_24 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_24 = x_15;
}
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_13);
return x_24;
}
else
{
obj* x_25; obj* x_27; obj* x_28; uint8 x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_25 = lean::cnstr_get(x_9, 1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_27 = x_9;
} else {
 lean::inc(x_25);
 lean::dec(x_9);
 x_27 = lean::box(0);
}
x_28 = lean::cnstr_get(x_11, 0);
x_30 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 x_31 = x_11;
} else {
 lean::inc(x_28);
 lean::dec(x_11);
 x_31 = lean::box(0);
}
if (lean::is_scalar(x_31)) {
 x_32 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_32 = x_31;
}
lean::cnstr_set(x_32, 0, x_28);
lean::cnstr_set_scalar(x_32, sizeof(void*)*1, x_30);
x_33 = x_32;
x_34 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_34, x_33);
if (lean::is_scalar(x_27)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_27;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_25);
return x_36;
}
}
}
obj* l_Lean_Parser_Combinators_longestChoice___at_Lean_Parser_number_x_27___spec__8(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
x_4 = lean::mk_nat_obj(0u);
x_5 = l_List_enumFrom___main___rarg(x_4, x_0);
x_6 = l_List_map___main___at_Lean_Parser_number_x_27___spec__9(x_5);
lean::inc(x_1);
x_8 = l_Lean_Parser_MonadParsec_longestMatch___at_Lean_Parser_number_x_27___spec__10(x_6, x_1, x_2, x_3);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; 
x_11 = lean::cnstr_get(x_9, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_16; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_27; obj* x_29; obj* x_31; obj* x_32; obj* x_33; 
x_13 = lean::cnstr_get(x_8, 1);
lean::inc(x_13);
lean::dec(x_8);
x_16 = lean::cnstr_get(x_9, 1);
lean::inc(x_16);
x_18 = lean::cnstr_get(x_9, 2);
lean::inc(x_18);
lean::dec(x_9);
x_21 = lean::box(0);
x_22 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
x_23 = l_mjoin___rarg___closed__1;
x_24 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_22, x_23, x_21, x_21, x_1, x_16, x_13);
lean::dec(x_16);
lean::dec(x_1);
x_27 = lean::cnstr_get(x_24, 0);
x_29 = lean::cnstr_get(x_24, 1);
if (lean::is_exclusive(x_24)) {
 x_31 = x_24;
} else {
 lean::inc(x_27);
 lean::inc(x_29);
 lean::dec(x_24);
 x_31 = lean::box(0);
}
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_27);
if (lean::is_scalar(x_31)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_31;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_29);
return x_33;
}
else
{
obj* x_35; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
lean::dec(x_1);
x_35 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_37 = x_8;
} else {
 lean::inc(x_35);
 lean::dec(x_8);
 x_37 = lean::box(0);
}
x_38 = lean::cnstr_get(x_9, 1);
x_40 = lean::cnstr_get(x_9, 2);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_42 = x_9;
} else {
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_9);
 x_42 = lean::box(0);
}
x_43 = lean::cnstr_get(x_11, 0);
lean::inc(x_43);
lean::dec(x_11);
x_46 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_42)) {
 x_47 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_47 = x_42;
}
lean::cnstr_set(x_47, 0, x_43);
lean::cnstr_set(x_47, 1, x_38);
lean::cnstr_set(x_47, 2, x_46);
x_48 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_40, x_47);
if (lean::is_scalar(x_37)) {
 x_49 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_49 = x_37;
}
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_35);
return x_49;
}
}
else
{
obj* x_51; obj* x_53; obj* x_54; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_1);
x_51 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_53 = x_8;
} else {
 lean::inc(x_51);
 lean::dec(x_8);
 x_53 = lean::box(0);
}
x_54 = lean::cnstr_get(x_9, 0);
x_56 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_57 = x_9;
} else {
 lean::inc(x_54);
 lean::dec(x_9);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_54);
lean::cnstr_set_scalar(x_58, sizeof(void*)*1, x_56);
x_59 = x_58;
if (lean::is_scalar(x_53)) {
 x_60 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_60 = x_53;
}
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_51);
return x_60;
}
}
}
obj* l_Lean_Parser_number_x_27___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_number_x_27___spec__1(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 1);
x_12 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_14 = x_5;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
lean::inc(x_10);
x_16 = l_Lean_Parser_mkRawRes(x_0, x_10);
x_17 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_14)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_14;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_10);
lean::cnstr_set(x_18, 2, x_17);
x_19 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_18);
if (lean::is_scalar(x_9)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_9;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_7);
return x_20;
}
else
{
obj* x_22; obj* x_24; obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_0);
x_22 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_24 = x_4;
} else {
 lean::inc(x_22);
 lean::dec(x_4);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_5, 0);
x_27 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_28 = x_5;
} else {
 lean::inc(x_25);
 lean::dec(x_5);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_27);
x_30 = x_29;
if (lean::is_scalar(x_24)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_24;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_22);
return x_31;
}
}
}
obj* l_Lean_Parser_number_x_27___lambda__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Parser_parseBinLit(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 1);
x_12 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_14 = x_5;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
lean::inc(x_10);
x_16 = l_Lean_Parser_mkRawRes(x_0, x_10);
x_17 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_14)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_14;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_10);
lean::cnstr_set(x_18, 2, x_17);
x_19 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_18);
if (lean::is_scalar(x_9)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_9;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_7);
return x_20;
}
else
{
obj* x_22; obj* x_24; obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_0);
x_22 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_24 = x_4;
} else {
 lean::inc(x_22);
 lean::dec(x_4);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_5, 0);
x_27 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_28 = x_5;
} else {
 lean::inc(x_25);
 lean::dec(x_5);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_27);
x_30 = x_29;
if (lean::is_scalar(x_24)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_24;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_22);
return x_31;
}
}
}
obj* l_Lean_Parser_number_x_27___lambda__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Parser_parseOctLit(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 1);
x_12 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_14 = x_5;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
lean::inc(x_10);
x_16 = l_Lean_Parser_mkRawRes(x_0, x_10);
x_17 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_14)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_14;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_10);
lean::cnstr_set(x_18, 2, x_17);
x_19 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_18);
if (lean::is_scalar(x_9)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_9;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_7);
return x_20;
}
else
{
obj* x_22; obj* x_24; obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_0);
x_22 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_24 = x_4;
} else {
 lean::inc(x_22);
 lean::dec(x_4);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_5, 0);
x_27 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_28 = x_5;
} else {
 lean::inc(x_25);
 lean::dec(x_5);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_27);
x_30 = x_29;
if (lean::is_scalar(x_24)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_24;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_22);
return x_31;
}
}
}
obj* l_Lean_Parser_number_x_27___lambda__4(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Parser_parseHexLit(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 1);
x_12 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_14 = x_5;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
lean::inc(x_10);
x_16 = l_Lean_Parser_mkRawRes(x_0, x_10);
x_17 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_14)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_14;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_10);
lean::cnstr_set(x_18, 2, x_17);
x_19 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_18);
if (lean::is_scalar(x_9)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_9;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_7);
return x_20;
}
else
{
obj* x_22; obj* x_24; obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_0);
x_22 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_24 = x_4;
} else {
 lean::inc(x_22);
 lean::dec(x_4);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_5, 0);
x_27 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_28 = x_5;
} else {
 lean::inc(x_25);
 lean::dec(x_5);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_27);
x_30 = x_29;
if (lean::is_scalar(x_24)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_24;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_22);
return x_31;
}
}
}
obj* _init_l_Lean_Parser_number_x_27___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_4; obj* x_5; obj* x_7; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_x_27___lambda__1___boxed), 4, 0);
lean::inc(x_1);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_4, 0, x_1);
lean::closure_set(x_4, 1, x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_x_27___lambda__2), 4, 0);
lean::inc(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_7, 0, x_1);
lean::closure_set(x_7, 1, x_5);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_x_27___lambda__3___boxed), 4, 0);
lean::inc(x_1);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_10, 0, x_1);
lean::closure_set(x_10, 1, x_8);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_x_27___lambda__4___boxed), 4, 0);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_12, 0, x_1);
lean::closure_set(x_12, 1, x_11);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_10);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_7);
lean::cnstr_set(x_16, 1, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_4);
lean::cnstr_set(x_17, 1, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_longestChoice___at_Lean_Parser_number_x_27___spec__8), 4, 1);
lean::closure_set(x_18, 0, x_17);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_13);
return x_19;
}
}
obj* l_Lean_Parser_number_x_27(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_Parser_number;
x_4 = l_Lean_Parser_number_x_27___closed__1;
x_5 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__15(x_3, x_4, x_0, x_1, x_2);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x_27___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x_27___spec__2(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x_27___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x_27___spec__4(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x_27___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x_27___spec__6(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_number_x_27___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_number_x_27___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_number_x_27___spec__11___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_number_x_27___spec__11(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_number_x_27___spec__12___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_number_x_27___spec__12___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_number_x_27___spec__12___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_number_x_27___spec__12(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_List_mfoldr___main___at_Lean_Parser_number_x_27___spec__13___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_List_mfoldr___main___at_Lean_Parser_number_x_27___spec__13(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_0);
return x_6;
}
}
obj* l_Lean_Parser_number_x_27___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_number_x_27___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_number_x_27___lambda__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_number_x_27___lambda__3(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_number_x_27___lambda__4___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_number_x_27___lambda__4(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_Parser_stringLit() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::mk_string("Lean");
x_2 = lean_name_mk_string(x_0, x_1);
x_3 = lean::mk_string("Parser");
x_4 = lean_name_mk_string(x_2, x_3);
x_5 = lean::mk_string("stringLit");
x_6 = lean_name_mk_string(x_4, x_5);
return x_6;
}
}
obj* l_Lean_Parser_stringLit_HasView_x_27___lambda__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_Syntax_asNode___main(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
else
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::is_exclusive(x_1)) {
 lean::cnstr_set(x_1, 0, lean::box(0));
 x_5 = x_1;
} else {
 lean::inc(x_3);
 lean::dec(x_1);
 x_5 = lean::box(0);
}
x_6 = lean::cnstr_get(x_3, 1);
lean::inc(x_6);
lean::dec(x_3);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
lean::dec(x_5);
x_10 = lean::box(0);
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_6, 0);
lean::inc(x_11);
lean::dec(x_6);
switch (lean::obj_tag(x_11)) {
case 0:
{
obj* x_14; obj* x_17; 
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
lean::dec(x_11);
if (lean::is_scalar(x_5)) {
 x_17 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_17 = x_5;
}
lean::cnstr_set(x_17, 0, x_14);
return x_17;
}
case 3:
{
obj* x_19; 
lean::dec(x_5);
x_19 = lean::box(0);
return x_19;
}
default:
{
obj* x_22; 
lean::dec(x_11);
lean::dec(x_5);
x_22 = lean::box(0);
return x_22;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_stringLit_HasView_x_27___lambda__2___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_0 = lean::box(0);
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = l_Option_getOrElse___main___rarg(x_1, x_2);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_0);
x_5 = l_Lean_Parser_stringLit;
x_6 = l_Lean_Parser_Syntax_mkNode(x_5, x_4);
return x_6;
}
}
obj* l_Lean_Parser_stringLit_HasView_x_27___lambda__2(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = l_Lean_Parser_stringLit_HasView_x_27___lambda__2___closed__1;
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; 
x_2 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 x_4 = x_0;
} else {
 lean::inc(x_2);
 lean::dec(x_0);
 x_4 = lean::box(0);
}
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_2);
if (lean::is_scalar(x_4)) {
 x_7 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_7 = x_4;
}
lean::cnstr_set(x_7, 0, x_6);
x_8 = lean::box(3);
x_9 = l_Option_getOrElse___main___rarg(x_7, x_8);
lean::dec(x_7);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_5);
x_12 = l_Lean_Parser_stringLit;
x_13 = l_Lean_Parser_Syntax_mkNode(x_12, x_11);
return x_13;
}
}
}
obj* _init_l_Lean_Parser_stringLit_HasView_x_27() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_stringLit_HasView_x_27___lambda__1), 1, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_stringLit_HasView_x_27___lambda__2), 1, 0);
x_2 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_2, 0, x_0);
lean::cnstr_set(x_2, 1, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_stringLit_HasView() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_stringLit_HasView_x_27;
return x_0;
}
}
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x_27___spec__4___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_1);
x_6 = lean::box(0);
x_7 = l_mjoin___rarg___closed__1;
x_8 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_0, x_7, x_5, x_6, x_2, x_3, x_4);
lean::dec(x_5);
return x_8;
}
}
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x_27___spec__4(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x_27___spec__4___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_digit___at_Lean_Parser_stringLit_x_27___spec__6(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_String_OldIterator_hasNext___main(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_11; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_4 = lean::box(0);
x_5 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_0, x_1, x_2);
lean::dec(x_1);
x_9 = lean::cnstr_get(x_7, 0);
x_11 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 x_13 = x_7;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_7);
 x_13 = lean::box(0);
}
x_14 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_9);
if (lean::is_scalar(x_13)) {
 x_16 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_16 = x_13;
}
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_11);
return x_16;
}
else
{
uint32 x_17; uint8 x_18; 
x_17 = l_String_OldIterator_curr___main(x_1);
x_18 = l_Char_isDigit(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_19 = l_Char_quoteCore(x_17);
x_20 = l_Char_HasRepr___closed__1;
x_21 = lean::string_append(x_20, x_19);
lean::dec(x_19);
x_23 = lean::string_append(x_21, x_20);
x_24 = lean::box(0);
x_25 = l_mjoin___rarg___closed__1;
x_26 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_23, x_25, x_24, x_24, x_0, x_1, x_2);
lean::dec(x_1);
x_28 = lean::cnstr_get(x_26, 0);
x_30 = lean::cnstr_get(x_26, 1);
if (lean::is_exclusive(x_26)) {
 x_32 = x_26;
} else {
 lean::inc(x_28);
 lean::inc(x_30);
 lean::dec(x_26);
 x_32 = lean::box(0);
}
x_33 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_34 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_33, x_28);
if (lean::is_scalar(x_32)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_32;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_30);
return x_35;
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_36 = l_String_OldIterator_next___main(x_1);
x_37 = lean::box(0);
x_38 = lean::box_uint32(x_17);
x_39 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_36);
lean::cnstr_set(x_39, 2, x_37);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_2);
return x_40;
}
}
}
}
obj* _init_l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = lean::mk_string("hexadecimal");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
return x_1;
}
}
obj* l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_8; 
lean::inc(x_1);
x_7 = l_Lean_Parser_MonadParsec_digit___at_Lean_Parser_stringLit_x_27___spec__6(x_0, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_13; obj* x_15; obj* x_17; obj* x_19; uint32 x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_27; 
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
lean::dec(x_7);
x_13 = lean::cnstr_get(x_8, 0);
x_15 = lean::cnstr_get(x_8, 1);
x_17 = lean::cnstr_get(x_8, 2);
if (lean::is_exclusive(x_8)) {
 x_19 = x_8;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_8);
 x_19 = lean::box(0);
}
x_20 = lean::unbox_uint32(x_13);
x_21 = lean::uint32_to_nat(x_20);
x_22 = l_String_foldlAux___main___at_String_toNat___spec__1___closed__1;
x_23 = lean::nat_sub(x_21, x_22);
lean::dec(x_21);
x_25 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_19)) {
 x_26 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_26 = x_19;
}
lean::cnstr_set(x_26, 0, x_23);
lean::cnstr_set(x_26, 1, x_15);
lean::cnstr_set(x_26, 2, x_25);
x_27 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_26);
x_3 = x_27;
x_4 = x_10;
goto lbl_5;
}
else
{
obj* x_28; obj* x_31; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; 
x_28 = lean::cnstr_get(x_7, 1);
lean::inc(x_28);
lean::dec(x_7);
x_31 = lean::cnstr_get(x_8, 0);
x_33 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_34 = x_8;
} else {
 lean::inc(x_31);
 lean::dec(x_8);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_31);
lean::cnstr_set_scalar(x_35, sizeof(void*)*1, x_33);
x_36 = x_35;
x_3 = x_36;
x_4 = x_28;
goto lbl_5;
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_38; obj* x_39; obj* x_40; 
lean::dec(x_1);
x_38 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5___closed__1;
x_39 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_3, x_38);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_4);
return x_40;
}
else
{
obj* x_41; uint8 x_43; obj* x_44; obj* x_45; obj* x_47; obj* x_48; 
x_41 = lean::cnstr_get(x_3, 0);
lean::inc(x_41);
x_43 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
if (x_43 == 0)
{
uint8 x_51; 
lean::dec(x_3);
x_51 = l_String_OldIterator_hasNext___main(x_1);
if (x_51 == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_58; obj* x_61; obj* x_62; 
x_52 = lean::box(0);
x_53 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_54 = l_mjoin___rarg___closed__1;
x_55 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_53, x_54, x_52, x_52, x_0, x_1, x_4);
x_56 = lean::cnstr_get(x_55, 0);
lean::inc(x_56);
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
lean::dec(x_55);
x_61 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_62 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_61, x_56);
x_47 = x_62;
x_48 = x_58;
goto lbl_49;
}
else
{
uint32 x_63; uint32 x_64; uint8 x_65; 
x_63 = l_String_OldIterator_curr___main(x_1);
x_64 = 97;
x_65 = x_64 <= x_63;
if (x_65 == 0)
{
obj* x_66; obj* x_67; obj* x_68; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_76; obj* x_79; obj* x_80; 
x_66 = l_Char_quoteCore(x_63);
x_67 = l_Char_HasRepr___closed__1;
x_68 = lean::string_append(x_67, x_66);
lean::dec(x_66);
x_70 = lean::string_append(x_68, x_67);
x_71 = lean::box(0);
x_72 = l_mjoin___rarg___closed__1;
x_73 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_70, x_72, x_71, x_71, x_0, x_1, x_4);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
lean::dec(x_73);
x_79 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_80 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_79, x_74);
x_47 = x_80;
x_48 = x_76;
goto lbl_49;
}
else
{
uint32 x_81; uint8 x_82; 
x_81 = 102;
x_82 = x_63 <= x_81;
if (x_82 == 0)
{
obj* x_83; obj* x_84; obj* x_85; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_93; obj* x_96; obj* x_97; 
x_83 = l_Char_quoteCore(x_63);
x_84 = l_Char_HasRepr___closed__1;
x_85 = lean::string_append(x_84, x_83);
lean::dec(x_83);
x_87 = lean::string_append(x_85, x_84);
x_88 = lean::box(0);
x_89 = l_mjoin___rarg___closed__1;
x_90 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_87, x_89, x_88, x_88, x_0, x_1, x_4);
x_91 = lean::cnstr_get(x_90, 0);
lean::inc(x_91);
x_93 = lean::cnstr_get(x_90, 1);
lean::inc(x_93);
lean::dec(x_90);
x_96 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_97 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_96, x_91);
x_47 = x_97;
x_48 = x_93;
goto lbl_49;
}
else
{
obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
lean::inc(x_1);
x_99 = l_String_OldIterator_next___main(x_1);
x_100 = lean::box(0);
x_101 = lean::box_uint32(x_63);
x_102 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_99);
lean::cnstr_set(x_102, 2, x_100);
x_47 = x_102;
x_48 = x_4;
goto lbl_49;
}
}
}
}
else
{
obj* x_105; obj* x_106; obj* x_107; 
lean::dec(x_1);
lean::dec(x_41);
x_105 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5___closed__1;
x_106 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_3, x_105);
x_107 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_4);
return x_107;
}
lbl_46:
{
if (lean::obj_tag(x_44) == 0)
{
obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_1);
x_109 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_41, x_44);
x_110 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5___closed__1;
x_111 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_109, x_110);
x_112 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_45);
return x_112;
}
else
{
obj* x_113; uint8 x_115; obj* x_116; obj* x_117; 
x_113 = lean::cnstr_get(x_44, 0);
lean::inc(x_113);
x_115 = lean::cnstr_get_scalar<uint8>(x_44, sizeof(void*)*1);
if (x_115 == 0)
{
uint8 x_120; 
lean::dec(x_44);
x_120 = l_String_OldIterator_hasNext___main(x_1);
if (x_120 == 0)
{
obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_126; obj* x_128; obj* x_131; obj* x_132; 
x_121 = lean::box(0);
x_122 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_123 = l_mjoin___rarg___closed__1;
x_124 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_122, x_123, x_121, x_121, x_0, x_1, x_45);
lean::dec(x_1);
x_126 = lean::cnstr_get(x_124, 0);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_124, 1);
lean::inc(x_128);
lean::dec(x_124);
x_131 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_132 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_131, x_126);
x_116 = x_132;
x_117 = x_128;
goto lbl_118;
}
else
{
uint32 x_133; uint32 x_134; uint8 x_135; 
x_133 = l_String_OldIterator_curr___main(x_1);
x_134 = 65;
x_135 = x_134 <= x_133;
if (x_135 == 0)
{
obj* x_136; obj* x_137; obj* x_138; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_145; obj* x_147; obj* x_150; obj* x_151; 
x_136 = l_Char_quoteCore(x_133);
x_137 = l_Char_HasRepr___closed__1;
x_138 = lean::string_append(x_137, x_136);
lean::dec(x_136);
x_140 = lean::string_append(x_138, x_137);
x_141 = lean::box(0);
x_142 = l_mjoin___rarg___closed__1;
x_143 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_140, x_142, x_141, x_141, x_0, x_1, x_45);
lean::dec(x_1);
x_145 = lean::cnstr_get(x_143, 0);
lean::inc(x_145);
x_147 = lean::cnstr_get(x_143, 1);
lean::inc(x_147);
lean::dec(x_143);
x_150 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_151 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_150, x_145);
x_116 = x_151;
x_117 = x_147;
goto lbl_118;
}
else
{
uint32 x_152; uint8 x_153; 
x_152 = 70;
x_153 = x_133 <= x_152;
if (x_153 == 0)
{
obj* x_154; obj* x_155; obj* x_156; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_163; obj* x_165; obj* x_168; obj* x_169; 
x_154 = l_Char_quoteCore(x_133);
x_155 = l_Char_HasRepr___closed__1;
x_156 = lean::string_append(x_155, x_154);
lean::dec(x_154);
x_158 = lean::string_append(x_156, x_155);
x_159 = lean::box(0);
x_160 = l_mjoin___rarg___closed__1;
x_161 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_158, x_160, x_159, x_159, x_0, x_1, x_45);
lean::dec(x_1);
x_163 = lean::cnstr_get(x_161, 0);
lean::inc(x_163);
x_165 = lean::cnstr_get(x_161, 1);
lean::inc(x_165);
lean::dec(x_161);
x_168 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_169 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_168, x_163);
x_116 = x_169;
x_117 = x_165;
goto lbl_118;
}
else
{
obj* x_170; obj* x_171; obj* x_172; obj* x_173; 
x_170 = l_String_OldIterator_next___main(x_1);
x_171 = lean::box(0);
x_172 = lean::box_uint32(x_133);
x_173 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_173, 0, x_172);
lean::cnstr_set(x_173, 1, x_170);
lean::cnstr_set(x_173, 2, x_171);
x_116 = x_173;
x_117 = x_45;
goto lbl_118;
}
}
}
}
else
{
obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
lean::dec(x_113);
lean::dec(x_1);
x_176 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_41, x_44);
x_177 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5___closed__1;
x_178 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_176, x_177);
x_179 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_179, 0, x_178);
lean::cnstr_set(x_179, 1, x_45);
return x_179;
}
lbl_118:
{
if (lean::obj_tag(x_116) == 0)
{
obj* x_180; obj* x_182; obj* x_184; obj* x_186; uint32 x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_192; obj* x_193; obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; 
x_180 = lean::cnstr_get(x_116, 0);
x_182 = lean::cnstr_get(x_116, 1);
x_184 = lean::cnstr_get(x_116, 2);
if (lean::is_exclusive(x_116)) {
 x_186 = x_116;
} else {
 lean::inc(x_180);
 lean::inc(x_182);
 lean::inc(x_184);
 lean::dec(x_116);
 x_186 = lean::box(0);
}
x_187 = lean::unbox_uint32(x_180);
x_188 = lean::uint32_to_nat(x_187);
x_189 = l_Lean_Parser_parseHexDigit___rarg___lambda__5___closed__1;
x_190 = lean::nat_sub(x_188, x_189);
lean::dec(x_188);
x_192 = lean::mk_nat_obj(10u);
x_193 = lean::nat_add(x_192, x_190);
lean::dec(x_190);
x_195 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_186)) {
 x_196 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_196 = x_186;
}
lean::cnstr_set(x_196, 0, x_193);
lean::cnstr_set(x_196, 1, x_182);
lean::cnstr_set(x_196, 2, x_195);
x_197 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_184, x_196);
x_198 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_113, x_197);
x_199 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_41, x_198);
x_200 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5___closed__1;
x_201 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_199, x_200);
x_202 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_202, 0, x_201);
lean::cnstr_set(x_202, 1, x_117);
return x_202;
}
else
{
obj* x_203; uint8 x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; 
x_203 = lean::cnstr_get(x_116, 0);
x_205 = lean::cnstr_get_scalar<uint8>(x_116, sizeof(void*)*1);
if (lean::is_exclusive(x_116)) {
 x_206 = x_116;
} else {
 lean::inc(x_203);
 lean::dec(x_116);
 x_206 = lean::box(0);
}
if (lean::is_scalar(x_206)) {
 x_207 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_207 = x_206;
}
lean::cnstr_set(x_207, 0, x_203);
lean::cnstr_set_scalar(x_207, sizeof(void*)*1, x_205);
x_208 = x_207;
x_209 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_113, x_208);
x_210 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_41, x_209);
x_211 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5___closed__1;
x_212 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_210, x_211);
x_213 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_213, 0, x_212);
lean::cnstr_set(x_213, 1, x_117);
return x_213;
}
}
}
}
lbl_49:
{
if (lean::obj_tag(x_47) == 0)
{
obj* x_214; obj* x_216; obj* x_218; obj* x_220; uint32 x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_226; obj* x_227; obj* x_229; obj* x_230; obj* x_231; 
x_214 = lean::cnstr_get(x_47, 0);
x_216 = lean::cnstr_get(x_47, 1);
x_218 = lean::cnstr_get(x_47, 2);
if (lean::is_exclusive(x_47)) {
 x_220 = x_47;
} else {
 lean::inc(x_214);
 lean::inc(x_216);
 lean::inc(x_218);
 lean::dec(x_47);
 x_220 = lean::box(0);
}
x_221 = lean::unbox_uint32(x_214);
x_222 = lean::uint32_to_nat(x_221);
x_223 = l_Lean_Parser_parseHexDigit___rarg___lambda__3___closed__1;
x_224 = lean::nat_sub(x_222, x_223);
lean::dec(x_222);
x_226 = lean::mk_nat_obj(10u);
x_227 = lean::nat_add(x_226, x_224);
lean::dec(x_224);
x_229 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_220)) {
 x_230 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_230 = x_220;
}
lean::cnstr_set(x_230, 0, x_227);
lean::cnstr_set(x_230, 1, x_216);
lean::cnstr_set(x_230, 2, x_229);
x_231 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_218, x_230);
x_44 = x_231;
x_45 = x_48;
goto lbl_46;
}
else
{
obj* x_232; uint8 x_234; obj* x_235; obj* x_236; obj* x_237; 
x_232 = lean::cnstr_get(x_47, 0);
x_234 = lean::cnstr_get_scalar<uint8>(x_47, sizeof(void*)*1);
if (lean::is_exclusive(x_47)) {
 x_235 = x_47;
} else {
 lean::inc(x_232);
 lean::dec(x_47);
 x_235 = lean::box(0);
}
if (lean::is_scalar(x_235)) {
 x_236 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_236 = x_235;
}
lean::cnstr_set(x_236, 0, x_232);
lean::cnstr_set_scalar(x_236, sizeof(void*)*1, x_234);
x_237 = x_236;
x_44 = x_237;
x_45 = x_48;
goto lbl_46;
}
}
}
}
}
}
obj* l_Lean_Parser_parseQuotedChar___at_Lean_Parser_stringLit_x_27___spec__3(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; 
lean::inc(x_1);
x_4 = l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__2(x_0, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; uint32 x_17; uint32 x_18; uint8 x_19; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_set(x_4, 1, lean::box(0));
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 0);
x_12 = lean::cnstr_get(x_5, 1);
x_14 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 lean::cnstr_set(x_5, 1, lean::box(0));
 lean::cnstr_set(x_5, 2, lean::box(0));
 x_16 = x_5;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_5);
 x_16 = lean::box(0);
}
x_17 = 92;
x_18 = lean::unbox_uint32(x_10);
x_19 = x_18 == x_17;
if (x_19 == 0)
{
uint32 x_20; uint8 x_21; 
x_20 = 34;
x_21 = x_18 == x_20;
if (x_21 == 0)
{
uint32 x_22; uint8 x_23; 
x_22 = 39;
x_23 = x_18 == x_22;
if (x_23 == 0)
{
uint32 x_24; uint8 x_25; 
x_24 = 110;
x_25 = x_18 == x_24;
if (x_25 == 0)
{
uint32 x_26; uint8 x_27; 
x_26 = 116;
x_27 = x_18 == x_26;
if (x_27 == 0)
{
uint32 x_30; uint8 x_31; 
lean::dec(x_16);
lean::dec(x_9);
x_30 = 120;
x_31 = x_18 == x_30;
if (x_31 == 0)
{
uint32 x_32; uint8 x_33; 
x_32 = 117;
x_33 = x_18 == x_32;
if (x_33 == 0)
{
obj* x_34; obj* x_35; obj* x_37; obj* x_39; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_34 = l_Lean_Parser_parseQuotedChar___rarg___lambda__7___closed__1;
x_35 = l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x_27___spec__4___rarg(x_34, x_1, x_0, x_12, x_7);
lean::dec(x_12);
x_37 = lean::cnstr_get(x_35, 0);
x_39 = lean::cnstr_get(x_35, 1);
if (lean::is_exclusive(x_35)) {
 x_41 = x_35;
} else {
 lean::inc(x_37);
 lean::inc(x_39);
 lean::dec(x_35);
 x_41 = lean::box(0);
}
x_42 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_37);
x_43 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_44 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_43, x_42);
if (lean::is_scalar(x_41)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_41;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_39);
return x_45;
}
else
{
obj* x_47; obj* x_48; 
lean::dec(x_1);
x_47 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5(x_0, x_12, x_7);
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
if (lean::obj_tag(x_48) == 0)
{
obj* x_50; obj* x_53; obj* x_55; obj* x_57; obj* x_60; obj* x_61; 
x_50 = lean::cnstr_get(x_47, 1);
lean::inc(x_50);
lean::dec(x_47);
x_53 = lean::cnstr_get(x_48, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_48, 1);
lean::inc(x_55);
x_57 = lean::cnstr_get(x_48, 2);
lean::inc(x_57);
lean::dec(x_48);
x_60 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5(x_0, x_55, x_50);
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
if (lean::obj_tag(x_61) == 0)
{
obj* x_63; obj* x_66; obj* x_68; obj* x_70; obj* x_73; obj* x_74; 
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
lean::dec(x_60);
x_66 = lean::cnstr_get(x_61, 0);
lean::inc(x_66);
x_68 = lean::cnstr_get(x_61, 1);
lean::inc(x_68);
x_70 = lean::cnstr_get(x_61, 2);
lean::inc(x_70);
lean::dec(x_61);
x_73 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5(x_0, x_68, x_63);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
if (lean::obj_tag(x_74) == 0)
{
obj* x_76; obj* x_79; obj* x_81; obj* x_83; obj* x_86; obj* x_87; 
x_76 = lean::cnstr_get(x_73, 1);
lean::inc(x_76);
lean::dec(x_73);
x_79 = lean::cnstr_get(x_74, 0);
lean::inc(x_79);
x_81 = lean::cnstr_get(x_74, 1);
lean::inc(x_81);
x_83 = lean::cnstr_get(x_74, 2);
lean::inc(x_83);
lean::dec(x_74);
x_86 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5(x_0, x_81, x_76);
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
if (lean::obj_tag(x_87) == 0)
{
obj* x_89; obj* x_91; obj* x_92; obj* x_94; obj* x_96; obj* x_98; obj* x_99; obj* x_100; obj* x_102; obj* x_105; obj* x_107; obj* x_110; obj* x_112; uint32 x_115; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; 
x_89 = lean::cnstr_get(x_86, 1);
if (lean::is_exclusive(x_86)) {
 lean::cnstr_release(x_86, 0);
 x_91 = x_86;
} else {
 lean::inc(x_89);
 lean::dec(x_86);
 x_91 = lean::box(0);
}
x_92 = lean::cnstr_get(x_87, 0);
x_94 = lean::cnstr_get(x_87, 1);
x_96 = lean::cnstr_get(x_87, 2);
if (lean::is_exclusive(x_87)) {
 x_98 = x_87;
} else {
 lean::inc(x_92);
 lean::inc(x_94);
 lean::inc(x_96);
 lean::dec(x_87);
 x_98 = lean::box(0);
}
x_99 = lean::mk_nat_obj(16u);
x_100 = lean::nat_mul(x_99, x_53);
lean::dec(x_53);
x_102 = lean::nat_add(x_100, x_66);
lean::dec(x_66);
lean::dec(x_100);
x_105 = lean::nat_mul(x_99, x_102);
lean::dec(x_102);
x_107 = lean::nat_add(x_105, x_79);
lean::dec(x_79);
lean::dec(x_105);
x_110 = lean::nat_mul(x_99, x_107);
lean::dec(x_107);
x_112 = lean::nat_add(x_110, x_92);
lean::dec(x_92);
lean::dec(x_110);
x_115 = l_Char_ofNat(x_112);
lean::dec(x_112);
x_117 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_118 = lean::box_uint32(x_115);
if (lean::is_scalar(x_98)) {
 x_119 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_119 = x_98;
}
lean::cnstr_set(x_119, 0, x_118);
lean::cnstr_set(x_119, 1, x_94);
lean::cnstr_set(x_119, 2, x_117);
x_120 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_96, x_119);
x_121 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_83, x_120);
x_122 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_70, x_121);
x_123 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_57, x_122);
x_124 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_123);
x_125 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_117, x_124);
if (lean::is_scalar(x_91)) {
 x_126 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_126 = x_91;
}
lean::cnstr_set(x_126, 0, x_125);
lean::cnstr_set(x_126, 1, x_89);
return x_126;
}
else
{
obj* x_130; obj* x_132; obj* x_133; uint8 x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
lean::dec(x_53);
lean::dec(x_66);
lean::dec(x_79);
x_130 = lean::cnstr_get(x_86, 1);
if (lean::is_exclusive(x_86)) {
 lean::cnstr_release(x_86, 0);
 x_132 = x_86;
} else {
 lean::inc(x_130);
 lean::dec(x_86);
 x_132 = lean::box(0);
}
x_133 = lean::cnstr_get(x_87, 0);
x_135 = lean::cnstr_get_scalar<uint8>(x_87, sizeof(void*)*1);
if (lean::is_exclusive(x_87)) {
 x_136 = x_87;
} else {
 lean::inc(x_133);
 lean::dec(x_87);
 x_136 = lean::box(0);
}
if (lean::is_scalar(x_136)) {
 x_137 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_137 = x_136;
}
lean::cnstr_set(x_137, 0, x_133);
lean::cnstr_set_scalar(x_137, sizeof(void*)*1, x_135);
x_138 = x_137;
x_139 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_83, x_138);
x_140 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_70, x_139);
x_141 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_57, x_140);
x_142 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_141);
x_143 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_144 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_143, x_142);
if (lean::is_scalar(x_132)) {
 x_145 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_145 = x_132;
}
lean::cnstr_set(x_145, 0, x_144);
lean::cnstr_set(x_145, 1, x_130);
return x_145;
}
}
else
{
obj* x_148; obj* x_150; obj* x_151; uint8 x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; 
lean::dec(x_53);
lean::dec(x_66);
x_148 = lean::cnstr_get(x_73, 1);
if (lean::is_exclusive(x_73)) {
 lean::cnstr_release(x_73, 0);
 x_150 = x_73;
} else {
 lean::inc(x_148);
 lean::dec(x_73);
 x_150 = lean::box(0);
}
x_151 = lean::cnstr_get(x_74, 0);
x_153 = lean::cnstr_get_scalar<uint8>(x_74, sizeof(void*)*1);
if (lean::is_exclusive(x_74)) {
 x_154 = x_74;
} else {
 lean::inc(x_151);
 lean::dec(x_74);
 x_154 = lean::box(0);
}
if (lean::is_scalar(x_154)) {
 x_155 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_155 = x_154;
}
lean::cnstr_set(x_155, 0, x_151);
lean::cnstr_set_scalar(x_155, sizeof(void*)*1, x_153);
x_156 = x_155;
x_157 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_70, x_156);
x_158 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_57, x_157);
x_159 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_158);
x_160 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_161 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_160, x_159);
if (lean::is_scalar(x_150)) {
 x_162 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_162 = x_150;
}
lean::cnstr_set(x_162, 0, x_161);
lean::cnstr_set(x_162, 1, x_148);
return x_162;
}
}
else
{
obj* x_164; obj* x_166; obj* x_167; uint8 x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; 
lean::dec(x_53);
x_164 = lean::cnstr_get(x_60, 1);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 x_166 = x_60;
} else {
 lean::inc(x_164);
 lean::dec(x_60);
 x_166 = lean::box(0);
}
x_167 = lean::cnstr_get(x_61, 0);
x_169 = lean::cnstr_get_scalar<uint8>(x_61, sizeof(void*)*1);
if (lean::is_exclusive(x_61)) {
 x_170 = x_61;
} else {
 lean::inc(x_167);
 lean::dec(x_61);
 x_170 = lean::box(0);
}
if (lean::is_scalar(x_170)) {
 x_171 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_171 = x_170;
}
lean::cnstr_set(x_171, 0, x_167);
lean::cnstr_set_scalar(x_171, sizeof(void*)*1, x_169);
x_172 = x_171;
x_173 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_57, x_172);
x_174 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_173);
x_175 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_176 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_175, x_174);
if (lean::is_scalar(x_166)) {
 x_177 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_177 = x_166;
}
lean::cnstr_set(x_177, 0, x_176);
lean::cnstr_set(x_177, 1, x_164);
return x_177;
}
}
else
{
obj* x_178; obj* x_180; obj* x_181; uint8 x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; 
x_178 = lean::cnstr_get(x_47, 1);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 x_180 = x_47;
} else {
 lean::inc(x_178);
 lean::dec(x_47);
 x_180 = lean::box(0);
}
x_181 = lean::cnstr_get(x_48, 0);
x_183 = lean::cnstr_get_scalar<uint8>(x_48, sizeof(void*)*1);
if (lean::is_exclusive(x_48)) {
 x_184 = x_48;
} else {
 lean::inc(x_181);
 lean::dec(x_48);
 x_184 = lean::box(0);
}
if (lean::is_scalar(x_184)) {
 x_185 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_185 = x_184;
}
lean::cnstr_set(x_185, 0, x_181);
lean::cnstr_set_scalar(x_185, sizeof(void*)*1, x_183);
x_186 = x_185;
x_187 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_186);
x_188 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_189 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_188, x_187);
if (lean::is_scalar(x_180)) {
 x_190 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_190 = x_180;
}
lean::cnstr_set(x_190, 0, x_189);
lean::cnstr_set(x_190, 1, x_178);
return x_190;
}
}
}
else
{
obj* x_192; obj* x_193; 
lean::dec(x_1);
x_192 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5(x_0, x_12, x_7);
x_193 = lean::cnstr_get(x_192, 0);
lean::inc(x_193);
if (lean::obj_tag(x_193) == 0)
{
obj* x_195; obj* x_198; obj* x_200; obj* x_202; obj* x_205; obj* x_206; 
x_195 = lean::cnstr_get(x_192, 1);
lean::inc(x_195);
lean::dec(x_192);
x_198 = lean::cnstr_get(x_193, 0);
lean::inc(x_198);
x_200 = lean::cnstr_get(x_193, 1);
lean::inc(x_200);
x_202 = lean::cnstr_get(x_193, 2);
lean::inc(x_202);
lean::dec(x_193);
x_205 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5(x_0, x_200, x_195);
x_206 = lean::cnstr_get(x_205, 0);
lean::inc(x_206);
if (lean::obj_tag(x_206) == 0)
{
obj* x_208; obj* x_210; obj* x_211; obj* x_213; obj* x_215; obj* x_217; obj* x_218; obj* x_219; obj* x_221; uint32 x_224; obj* x_226; obj* x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_232; obj* x_233; 
x_208 = lean::cnstr_get(x_205, 1);
if (lean::is_exclusive(x_205)) {
 lean::cnstr_release(x_205, 0);
 x_210 = x_205;
} else {
 lean::inc(x_208);
 lean::dec(x_205);
 x_210 = lean::box(0);
}
x_211 = lean::cnstr_get(x_206, 0);
x_213 = lean::cnstr_get(x_206, 1);
x_215 = lean::cnstr_get(x_206, 2);
if (lean::is_exclusive(x_206)) {
 x_217 = x_206;
} else {
 lean::inc(x_211);
 lean::inc(x_213);
 lean::inc(x_215);
 lean::dec(x_206);
 x_217 = lean::box(0);
}
x_218 = lean::mk_nat_obj(16u);
x_219 = lean::nat_mul(x_218, x_198);
lean::dec(x_198);
x_221 = lean::nat_add(x_219, x_211);
lean::dec(x_211);
lean::dec(x_219);
x_224 = l_Char_ofNat(x_221);
lean::dec(x_221);
x_226 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_227 = lean::box_uint32(x_224);
if (lean::is_scalar(x_217)) {
 x_228 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_228 = x_217;
}
lean::cnstr_set(x_228, 0, x_227);
lean::cnstr_set(x_228, 1, x_213);
lean::cnstr_set(x_228, 2, x_226);
x_229 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_215, x_228);
x_230 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_202, x_229);
x_231 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_230);
x_232 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_226, x_231);
if (lean::is_scalar(x_210)) {
 x_233 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_233 = x_210;
}
lean::cnstr_set(x_233, 0, x_232);
lean::cnstr_set(x_233, 1, x_208);
return x_233;
}
else
{
obj* x_235; obj* x_237; obj* x_238; uint8 x_240; obj* x_241; obj* x_242; obj* x_243; obj* x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_248; 
lean::dec(x_198);
x_235 = lean::cnstr_get(x_205, 1);
if (lean::is_exclusive(x_205)) {
 lean::cnstr_release(x_205, 0);
 x_237 = x_205;
} else {
 lean::inc(x_235);
 lean::dec(x_205);
 x_237 = lean::box(0);
}
x_238 = lean::cnstr_get(x_206, 0);
x_240 = lean::cnstr_get_scalar<uint8>(x_206, sizeof(void*)*1);
if (lean::is_exclusive(x_206)) {
 x_241 = x_206;
} else {
 lean::inc(x_238);
 lean::dec(x_206);
 x_241 = lean::box(0);
}
if (lean::is_scalar(x_241)) {
 x_242 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_242 = x_241;
}
lean::cnstr_set(x_242, 0, x_238);
lean::cnstr_set_scalar(x_242, sizeof(void*)*1, x_240);
x_243 = x_242;
x_244 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_202, x_243);
x_245 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_244);
x_246 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_247 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_246, x_245);
if (lean::is_scalar(x_237)) {
 x_248 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_248 = x_237;
}
lean::cnstr_set(x_248, 0, x_247);
lean::cnstr_set(x_248, 1, x_235);
return x_248;
}
}
else
{
obj* x_249; obj* x_251; obj* x_252; uint8 x_254; obj* x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; obj* x_260; obj* x_261; 
x_249 = lean::cnstr_get(x_192, 1);
if (lean::is_exclusive(x_192)) {
 lean::cnstr_release(x_192, 0);
 x_251 = x_192;
} else {
 lean::inc(x_249);
 lean::dec(x_192);
 x_251 = lean::box(0);
}
x_252 = lean::cnstr_get(x_193, 0);
x_254 = lean::cnstr_get_scalar<uint8>(x_193, sizeof(void*)*1);
if (lean::is_exclusive(x_193)) {
 x_255 = x_193;
} else {
 lean::inc(x_252);
 lean::dec(x_193);
 x_255 = lean::box(0);
}
if (lean::is_scalar(x_255)) {
 x_256 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_256 = x_255;
}
lean::cnstr_set(x_256, 0, x_252);
lean::cnstr_set_scalar(x_256, sizeof(void*)*1, x_254);
x_257 = x_256;
x_258 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_257);
x_259 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_260 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_259, x_258);
if (lean::is_scalar(x_251)) {
 x_261 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_261 = x_251;
}
lean::cnstr_set(x_261, 0, x_260);
lean::cnstr_set(x_261, 1, x_249);
return x_261;
}
}
}
else
{
uint32 x_263; obj* x_264; obj* x_265; obj* x_266; obj* x_267; obj* x_268; obj* x_269; 
lean::dec(x_1);
x_263 = 9;
x_264 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_265 = lean::box_uint32(x_263);
if (lean::is_scalar(x_16)) {
 x_266 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_266 = x_16;
}
lean::cnstr_set(x_266, 0, x_265);
lean::cnstr_set(x_266, 1, x_12);
lean::cnstr_set(x_266, 2, x_264);
x_267 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_266);
x_268 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_264, x_267);
if (lean::is_scalar(x_9)) {
 x_269 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_269 = x_9;
}
lean::cnstr_set(x_269, 0, x_268);
lean::cnstr_set(x_269, 1, x_7);
return x_269;
}
}
else
{
uint32 x_271; obj* x_272; obj* x_273; obj* x_274; obj* x_275; obj* x_276; obj* x_277; 
lean::dec(x_1);
x_271 = 10;
x_272 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_273 = lean::box_uint32(x_271);
if (lean::is_scalar(x_16)) {
 x_274 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_274 = x_16;
}
lean::cnstr_set(x_274, 0, x_273);
lean::cnstr_set(x_274, 1, x_12);
lean::cnstr_set(x_274, 2, x_272);
x_275 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_274);
x_276 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_272, x_275);
if (lean::is_scalar(x_9)) {
 x_277 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_277 = x_9;
}
lean::cnstr_set(x_277, 0, x_276);
lean::cnstr_set(x_277, 1, x_7);
return x_277;
}
}
else
{
obj* x_279; obj* x_280; obj* x_281; obj* x_282; obj* x_283; obj* x_284; 
lean::dec(x_1);
x_279 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_280 = lean::box_uint32(x_22);
if (lean::is_scalar(x_16)) {
 x_281 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_281 = x_16;
}
lean::cnstr_set(x_281, 0, x_280);
lean::cnstr_set(x_281, 1, x_12);
lean::cnstr_set(x_281, 2, x_279);
x_282 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_281);
x_283 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_279, x_282);
if (lean::is_scalar(x_9)) {
 x_284 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_284 = x_9;
}
lean::cnstr_set(x_284, 0, x_283);
lean::cnstr_set(x_284, 1, x_7);
return x_284;
}
}
else
{
obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; 
lean::dec(x_1);
x_286 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_287 = lean::box_uint32(x_20);
if (lean::is_scalar(x_16)) {
 x_288 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_288 = x_16;
}
lean::cnstr_set(x_288, 0, x_287);
lean::cnstr_set(x_288, 1, x_12);
lean::cnstr_set(x_288, 2, x_286);
x_289 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_288);
x_290 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_286, x_289);
if (lean::is_scalar(x_9)) {
 x_291 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_291 = x_9;
}
lean::cnstr_set(x_291, 0, x_290);
lean::cnstr_set(x_291, 1, x_7);
return x_291;
}
}
else
{
obj* x_293; obj* x_294; obj* x_295; obj* x_296; obj* x_297; obj* x_298; 
lean::dec(x_1);
x_293 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_294 = lean::box_uint32(x_17);
if (lean::is_scalar(x_16)) {
 x_295 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_295 = x_16;
}
lean::cnstr_set(x_295, 0, x_294);
lean::cnstr_set(x_295, 1, x_12);
lean::cnstr_set(x_295, 2, x_293);
x_296 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_295);
x_297 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_293, x_296);
if (lean::is_scalar(x_9)) {
 x_298 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_298 = x_9;
}
lean::cnstr_set(x_298, 0, x_297);
lean::cnstr_set(x_298, 1, x_7);
return x_298;
}
}
else
{
obj* x_300; obj* x_302; obj* x_303; uint8 x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; 
lean::dec(x_1);
x_300 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_302 = x_4;
} else {
 lean::inc(x_300);
 lean::dec(x_4);
 x_302 = lean::box(0);
}
x_303 = lean::cnstr_get(x_5, 0);
x_305 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_306 = x_5;
} else {
 lean::inc(x_303);
 lean::dec(x_5);
 x_306 = lean::box(0);
}
if (lean::is_scalar(x_306)) {
 x_307 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_307 = x_306;
}
lean::cnstr_set(x_307, 0, x_303);
lean::cnstr_set_scalar(x_307, sizeof(void*)*1, x_305);
x_308 = x_307;
x_309 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_310 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_309, x_308);
if (lean::is_scalar(x_302)) {
 x_311 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_311 = x_302;
}
lean::cnstr_set(x_311, 0, x_310);
lean::cnstr_set(x_311, 1, x_300);
return x_311;
}
}
}
obj* l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_x_27___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_0, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; 
x_7 = l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__2(x_2, x_3, x_4);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_10; obj* x_12; obj* x_13; obj* x_15; obj* x_17; obj* x_19; obj* x_20; obj* x_21; uint32 x_22; uint32 x_23; uint8 x_24; 
x_10 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_set(x_7, 1, lean::box(0));
 x_12 = x_7;
} else {
 lean::inc(x_10);
 lean::dec(x_7);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_8, 0);
x_15 = lean::cnstr_get(x_8, 1);
x_17 = lean::cnstr_get(x_8, 2);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_set(x_8, 0, lean::box(0));
 lean::cnstr_set(x_8, 1, lean::box(0));
 lean::cnstr_set(x_8, 2, lean::box(0));
 x_19 = x_8;
} else {
 lean::inc(x_13);
 lean::inc(x_15);
 lean::inc(x_17);
 lean::dec(x_8);
 x_19 = lean::box(0);
}
x_20 = lean::mk_nat_obj(1u);
x_21 = lean::nat_sub(x_0, x_20);
x_22 = 92;
x_23 = lean::unbox_uint32(x_13);
x_24 = x_23 == x_22;
if (x_24 == 0)
{
uint32 x_25; uint8 x_26; 
x_25 = 34;
x_26 = x_23 == x_25;
if (x_26 == 0)
{
obj* x_29; obj* x_30; obj* x_32; obj* x_34; obj* x_36; obj* x_37; obj* x_38; 
lean::dec(x_19);
lean::dec(x_12);
x_29 = lean::string_push(x_1, x_23);
x_30 = l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_x_27___spec__2(x_21, x_29, x_2, x_15, x_10);
lean::dec(x_21);
x_32 = lean::cnstr_get(x_30, 0);
x_34 = lean::cnstr_get(x_30, 1);
if (lean::is_exclusive(x_30)) {
 x_36 = x_30;
} else {
 lean::inc(x_32);
 lean::inc(x_34);
 lean::dec(x_30);
 x_36 = lean::box(0);
}
x_37 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_32);
if (lean::is_scalar(x_36)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_36;
}
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_34);
return x_38;
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::dec(x_21);
x_40 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_19)) {
 x_41 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_41 = x_19;
}
lean::cnstr_set(x_41, 0, x_1);
lean::cnstr_set(x_41, 1, x_15);
lean::cnstr_set(x_41, 2, x_40);
x_42 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_41);
if (lean::is_scalar(x_12)) {
 x_43 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_43 = x_12;
}
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_10);
return x_43;
}
}
else
{
obj* x_46; obj* x_47; 
lean::dec(x_19);
lean::dec(x_12);
x_46 = l_Lean_Parser_parseQuotedChar___at_Lean_Parser_stringLit_x_27___spec__3(x_2, x_15, x_10);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
if (lean::obj_tag(x_47) == 0)
{
obj* x_49; obj* x_52; obj* x_54; obj* x_56; uint32 x_59; obj* x_60; obj* x_61; obj* x_63; obj* x_65; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_49 = lean::cnstr_get(x_46, 1);
lean::inc(x_49);
lean::dec(x_46);
x_52 = lean::cnstr_get(x_47, 0);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_47, 1);
lean::inc(x_54);
x_56 = lean::cnstr_get(x_47, 2);
lean::inc(x_56);
lean::dec(x_47);
x_59 = lean::unbox_uint32(x_52);
x_60 = lean::string_push(x_1, x_59);
x_61 = l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_x_27___spec__2(x_21, x_60, x_2, x_54, x_49);
lean::dec(x_21);
x_63 = lean::cnstr_get(x_61, 0);
x_65 = lean::cnstr_get(x_61, 1);
if (lean::is_exclusive(x_61)) {
 x_67 = x_61;
} else {
 lean::inc(x_63);
 lean::inc(x_65);
 lean::dec(x_61);
 x_67 = lean::box(0);
}
x_68 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_56, x_63);
x_69 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_68);
if (lean::is_scalar(x_67)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_67;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_65);
return x_70;
}
else
{
obj* x_73; obj* x_75; obj* x_76; uint8 x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_1);
lean::dec(x_21);
x_73 = lean::cnstr_get(x_46, 1);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 x_75 = x_46;
} else {
 lean::inc(x_73);
 lean::dec(x_46);
 x_75 = lean::box(0);
}
x_76 = lean::cnstr_get(x_47, 0);
x_78 = lean::cnstr_get_scalar<uint8>(x_47, sizeof(void*)*1);
if (lean::is_exclusive(x_47)) {
 x_79 = x_47;
} else {
 lean::inc(x_76);
 lean::dec(x_47);
 x_79 = lean::box(0);
}
if (lean::is_scalar(x_79)) {
 x_80 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_80 = x_79;
}
lean::cnstr_set(x_80, 0, x_76);
lean::cnstr_set_scalar(x_80, sizeof(void*)*1, x_78);
x_81 = x_80;
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_81);
if (lean::is_scalar(x_75)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_75;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_73);
return x_83;
}
}
}
else
{
obj* x_85; obj* x_87; obj* x_88; uint8 x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
lean::dec(x_1);
x_85 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_87 = x_7;
} else {
 lean::inc(x_85);
 lean::dec(x_7);
 x_87 = lean::box(0);
}
x_88 = lean::cnstr_get(x_8, 0);
x_90 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 x_91 = x_8;
} else {
 lean::inc(x_88);
 lean::dec(x_8);
 x_91 = lean::box(0);
}
if (lean::is_scalar(x_91)) {
 x_92 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_92 = x_91;
}
lean::cnstr_set(x_92, 0, x_88);
lean::cnstr_set_scalar(x_92, sizeof(void*)*1, x_90);
x_93 = x_92;
if (lean::is_scalar(x_87)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_87;
}
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_85);
return x_94;
}
}
else
{
uint32 x_95; obj* x_96; obj* x_97; 
x_95 = 34;
x_96 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_95, x_2, x_3, x_4);
x_97 = lean::cnstr_get(x_96, 0);
lean::inc(x_97);
if (lean::obj_tag(x_97) == 0)
{
obj* x_99; obj* x_101; obj* x_102; obj* x_104; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
x_99 = lean::cnstr_get(x_96, 1);
if (lean::is_exclusive(x_96)) {
 lean::cnstr_release(x_96, 0);
 x_101 = x_96;
} else {
 lean::inc(x_99);
 lean::dec(x_96);
 x_101 = lean::box(0);
}
x_102 = lean::cnstr_get(x_97, 1);
x_104 = lean::cnstr_get(x_97, 2);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_release(x_97, 0);
 x_106 = x_97;
} else {
 lean::inc(x_102);
 lean::inc(x_104);
 lean::dec(x_97);
 x_106 = lean::box(0);
}
x_107 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_106)) {
 x_108 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_108 = x_106;
}
lean::cnstr_set(x_108, 0, x_1);
lean::cnstr_set(x_108, 1, x_102);
lean::cnstr_set(x_108, 2, x_107);
x_109 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_104, x_108);
if (lean::is_scalar(x_101)) {
 x_110 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_110 = x_101;
}
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_99);
return x_110;
}
else
{
obj* x_112; obj* x_114; obj* x_115; uint8 x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; 
lean::dec(x_1);
x_112 = lean::cnstr_get(x_96, 1);
if (lean::is_exclusive(x_96)) {
 lean::cnstr_release(x_96, 0);
 x_114 = x_96;
} else {
 lean::inc(x_112);
 lean::dec(x_96);
 x_114 = lean::box(0);
}
x_115 = lean::cnstr_get(x_97, 0);
x_117 = lean::cnstr_get_scalar<uint8>(x_97, sizeof(void*)*1);
if (lean::is_exclusive(x_97)) {
 x_118 = x_97;
} else {
 lean::inc(x_115);
 lean::dec(x_97);
 x_118 = lean::box(0);
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_115);
lean::cnstr_set_scalar(x_119, sizeof(void*)*1, x_117);
x_120 = x_119;
if (lean::is_scalar(x_114)) {
 x_121 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_121 = x_114;
}
lean::cnstr_set(x_121, 0, x_120);
lean::cnstr_set(x_121, 1, x_112);
return x_121;
}
}
}
}
obj* l_Lean_Parser_parseStringLiteral___at_Lean_Parser_stringLit_x_27___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; obj* x_5; 
x_3 = 34;
x_4 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_3, x_0, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_10; obj* x_12; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
lean::dec(x_4);
x_10 = lean::cnstr_get(x_5, 1);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_5, 2);
lean::inc(x_12);
lean::dec(x_5);
x_15 = l_String_OldIterator_remaining___main(x_10);
x_16 = l_String_splitAux___main___closed__1;
x_17 = l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_x_27___spec__2(x_15, x_16, x_0, x_10, x_7);
lean::dec(x_15);
x_19 = lean::cnstr_get(x_17, 0);
x_21 = lean::cnstr_get(x_17, 1);
if (lean::is_exclusive(x_17)) {
 x_23 = x_17;
} else {
 lean::inc(x_19);
 lean::inc(x_21);
 lean::dec(x_17);
 x_23 = lean::box(0);
}
x_24 = l_Lean_Parser_finishCommentBlock___closed__2;
x_25 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_19);
x_26 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_25);
if (lean::is_scalar(x_23)) {
 x_27 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_27 = x_23;
}
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_21);
return x_27;
}
else
{
obj* x_28; obj* x_30; obj* x_31; uint8 x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_28 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_30 = x_4;
} else {
 lean::inc(x_28);
 lean::dec(x_4);
 x_30 = lean::box(0);
}
x_31 = lean::cnstr_get(x_5, 0);
x_33 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_34 = x_5;
} else {
 lean::inc(x_31);
 lean::dec(x_5);
 x_34 = lean::box(0);
}
if (lean::is_scalar(x_34)) {
 x_35 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_35 = x_34;
}
lean::cnstr_set(x_35, 0, x_31);
lean::cnstr_set_scalar(x_35, sizeof(void*)*1, x_33);
x_36 = x_35;
if (lean::is_scalar(x_30)) {
 x_37 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_37 = x_30;
}
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_28);
return x_37;
}
}
}
obj* l_Lean_Parser_stringLit_x_27___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Parser_parseStringLiteral___at_Lean_Parser_stringLit_x_27___spec__1(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 1);
x_12 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_14 = x_5;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::dec(x_5);
 x_14 = lean::box(0);
}
lean::inc(x_10);
x_16 = l_Lean_Parser_mkRawRes(x_0, x_10);
x_17 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_14)) {
 x_18 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_18 = x_14;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_10);
lean::cnstr_set(x_18, 2, x_17);
x_19 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_18);
if (lean::is_scalar(x_9)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_9;
}
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_7);
return x_20;
}
else
{
obj* x_22; obj* x_24; obj* x_25; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_0);
x_22 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_24 = x_4;
} else {
 lean::inc(x_22);
 lean::dec(x_4);
 x_24 = lean::box(0);
}
x_25 = lean::cnstr_get(x_5, 0);
x_27 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_28 = x_5;
} else {
 lean::inc(x_25);
 lean::dec(x_5);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_25);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_27);
x_30 = x_29;
if (lean::is_scalar(x_24)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_24;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_22);
return x_31;
}
}
}
obj* _init_l_Lean_Parser_stringLit_x_27___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_stringLit_x_27___lambda__1___boxed), 4, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
}
obj* l_Lean_Parser_stringLit_x_27(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_Parser_stringLit;
x_4 = l_Lean_Parser_stringLit_x_27___closed__1;
x_5 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__15(x_3, x_4, x_0, x_1, x_2);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x_27___spec__4___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x_27___spec__4___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x_27___spec__4___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x_27___spec__4(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_digit___at_Lean_Parser_stringLit_x_27___spec__6___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_digit___at_Lean_Parser_stringLit_x_27___spec__6(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Parser_parseQuotedChar___at_Lean_Parser_stringLit_x_27___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_parseQuotedChar___at_Lean_Parser_stringLit_x_27___spec__3(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_x_27___spec__2___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_x_27___spec__2(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_parseStringLiteral___at_Lean_Parser_stringLit_x_27___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_parseStringLiteral___at_Lean_Parser_stringLit_x_27___spec__1(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Parser_stringLit_x_27___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_stringLit_x_27___lambda__1(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_parser_token_5__mkConsumeToken(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_8; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_5 = lean::cnstr_get(x_0, 0);
x_6 = lean::string_length(x_5);
lean::inc(x_1);
x_8 = l_String_OldIterator_nextn___main(x_1, x_6);
lean::inc(x_8);
x_10 = l_Lean_Parser_mkRawRes(x_1, x_8);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_8);
lean::cnstr_set(x_12, 2, x_11);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_4);
return x_13;
}
}
obj* l___private_init_lean_parser_token_5__mkConsumeToken___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_token_5__mkConsumeToken(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_Parser_numberOrStringLit(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_7; obj* x_8; 
x_3 = l_Lean_Parser_number;
x_4 = l_Lean_Parser_number_x_27___closed__1;
lean::inc(x_1);
lean::inc(x_0);
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__15(x_3, x_4, x_0, x_1, x_2);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_12; obj* x_14; obj* x_15; 
lean::dec(x_1);
lean::dec(x_0);
x_12 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_14 = x_7;
} else {
 lean::inc(x_12);
 lean::dec(x_7);
 x_14 = lean::box(0);
}
if (lean::is_scalar(x_14)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_14;
}
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_12);
return x_15;
}
else
{
uint8 x_16; 
x_16 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (x_16 == 0)
{
obj* x_17; obj* x_20; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; 
x_17 = lean::cnstr_get(x_7, 1);
lean::inc(x_17);
lean::dec(x_7);
x_20 = lean::cnstr_get(x_8, 0);
lean::inc(x_20);
lean::dec(x_8);
x_23 = l_Lean_Parser_stringLit;
x_24 = l_Lean_Parser_stringLit_x_27___closed__1;
x_25 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__15(x_23, x_24, x_0, x_1, x_17);
x_26 = lean::cnstr_get(x_25, 0);
x_28 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 x_30 = x_25;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_25);
 x_30 = lean::box(0);
}
x_31 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_20, x_26);
if (lean::is_scalar(x_30)) {
 x_32 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_32 = x_30;
}
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_28);
return x_32;
}
else
{
obj* x_35; obj* x_37; obj* x_38; 
lean::dec(x_1);
lean::dec(x_0);
x_35 = lean::cnstr_get(x_7, 1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_37 = x_7;
} else {
 lean::inc(x_35);
 lean::dec(x_7);
 x_37 = lean::box(0);
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_8);
lean::cnstr_set(x_38, 1, x_35);
return x_38;
}
}
}
}
obj* l_Lean_Parser_tokenCont(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_2);
x_6 = l___private_init_lean_parser_token_4__ident_x_27(x_2, x_3, x_4);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_21; obj* x_23; obj* x_24; obj* x_25; uint8 x_28; 
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_set(x_6, 1, lean::box(0));
 x_11 = x_6;
} else {
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_7, 0);
x_14 = lean::cnstr_get(x_7, 1);
x_16 = lean::cnstr_get(x_7, 2);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 lean::cnstr_set(x_7, 2, lean::box(0));
 x_18 = x_7;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_7);
 x_18 = lean::box(0);
}
x_19 = lean::cnstr_get(x_14, 1);
lean::inc(x_19);
x_21 = lean::cnstr_get(x_0, 1);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_1, 0);
x_24 = lean::string_length(x_23);
x_25 = lean::nat_add(x_21, x_24);
lean::dec(x_24);
lean::dec(x_21);
x_28 = lean::nat_dec_le(x_19, x_25);
lean::dec(x_25);
lean::dec(x_19);
if (x_28 == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_0);
lean::dec(x_2);
x_33 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_18)) {
 x_34 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_34 = x_18;
}
lean::cnstr_set(x_34, 0, x_12);
lean::cnstr_set(x_34, 1, x_14);
lean::cnstr_set(x_34, 2, x_33);
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_34);
if (lean::is_scalar(x_11)) {
 x_36 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_36 = x_11;
}
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_9);
return x_36;
}
else
{
obj* x_40; obj* x_43; obj* x_45; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_12);
lean::dec(x_11);
lean::dec(x_18);
x_40 = l___private_init_lean_parser_token_5__mkConsumeToken(x_1, x_0, x_2, x_14, x_9);
lean::dec(x_14);
lean::dec(x_2);
x_43 = lean::cnstr_get(x_40, 0);
x_45 = lean::cnstr_get(x_40, 1);
if (lean::is_exclusive(x_40)) {
 x_47 = x_40;
} else {
 lean::inc(x_43);
 lean::inc(x_45);
 lean::dec(x_40);
 x_47 = lean::box(0);
}
x_48 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_49 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_48, x_43);
x_50 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_49);
if (lean::is_scalar(x_47)) {
 x_51 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_51 = x_47;
}
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_45);
return x_51;
}
}
else
{
obj* x_54; obj* x_56; obj* x_57; uint8 x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_0);
lean::dec(x_2);
x_54 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_56 = x_6;
} else {
 lean::inc(x_54);
 lean::dec(x_6);
 x_56 = lean::box(0);
}
x_57 = lean::cnstr_get(x_7, 0);
x_59 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_60 = x_7;
} else {
 lean::inc(x_57);
 lean::dec(x_7);
 x_60 = lean::box(0);
}
if (lean::is_scalar(x_60)) {
 x_61 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_61 = x_60;
}
lean::cnstr_set(x_61, 0, x_57);
lean::cnstr_set_scalar(x_61, sizeof(void*)*1, x_59);
x_62 = x_61;
if (lean::is_scalar(x_56)) {
 x_63 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_63 = x_56;
}
lean::cnstr_set(x_63, 0, x_62);
lean::cnstr_set(x_63, 1, x_54);
return x_63;
}
}
}
obj* l_Lean_Parser_tokenCont___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_tokenCont(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_token___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; uint8 x_8; 
x_8 = l_String_OldIterator_hasNext___main(x_3);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_14; obj* x_17; 
x_9 = lean::box(0);
x_10 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_11 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_10, x_0, x_9, x_9, x_2, x_3, x_4);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
lean::dec(x_11);
x_17 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_1, x_12);
if (lean::obj_tag(x_17) == 0)
{
x_5 = x_17;
x_6 = x_14;
goto lbl_7;
}
else
{
uint8 x_18; 
x_18 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*1);
if (x_18 == 0)
{
obj* x_19; uint32 x_22; obj* x_24; obj* x_25; obj* x_27; obj* x_30; 
x_19 = lean::cnstr_get(x_17, 0);
lean::inc(x_19);
lean::dec(x_17);
x_22 = l_Lean_idBeginEscape;
lean::inc(x_3);
x_24 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_22, x_2, x_3, x_14);
x_25 = lean::cnstr_get(x_24, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_24, 1);
lean::inc(x_27);
lean::dec(x_24);
x_30 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_19, x_25);
x_5 = x_30;
x_6 = x_27;
goto lbl_7;
}
else
{
x_5 = x_17;
x_6 = x_14;
goto lbl_7;
}
}
}
else
{
uint32 x_31; uint8 x_32; 
x_31 = l_String_OldIterator_curr___main(x_3);
x_32 = l_Lean_isIdFirst(x_31);
if (x_32 == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_45; 
x_33 = l_Char_quoteCore(x_31);
x_34 = l_Char_HasRepr___closed__1;
x_35 = lean::string_append(x_34, x_33);
lean::dec(x_33);
x_37 = lean::string_append(x_35, x_34);
x_38 = lean::box(0);
x_39 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_37, x_0, x_38, x_38, x_2, x_3, x_4);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
x_42 = lean::cnstr_get(x_39, 1);
lean::inc(x_42);
lean::dec(x_39);
x_45 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_1, x_40);
if (lean::obj_tag(x_45) == 0)
{
x_5 = x_45;
x_6 = x_42;
goto lbl_7;
}
else
{
uint8 x_46; 
x_46 = lean::cnstr_get_scalar<uint8>(x_45, sizeof(void*)*1);
if (x_46 == 0)
{
obj* x_47; uint32 x_50; obj* x_52; obj* x_53; obj* x_55; obj* x_58; 
x_47 = lean::cnstr_get(x_45, 0);
lean::inc(x_47);
lean::dec(x_45);
x_50 = l_Lean_idBeginEscape;
lean::inc(x_3);
x_52 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x_27___spec__11(x_50, x_2, x_3, x_42);
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
lean::dec(x_52);
x_58 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_47, x_53);
x_5 = x_58;
x_6 = x_55;
goto lbl_7;
}
else
{
x_5 = x_45;
x_6 = x_42;
goto lbl_7;
}
}
}
else
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
lean::dec(x_1);
lean::dec(x_0);
lean::inc(x_3);
x_62 = l_String_OldIterator_next___main(x_3);
x_63 = lean::box(0);
x_64 = lean::box_uint32(x_31);
x_65 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_62);
lean::cnstr_set(x_65, 2, x_63);
x_5 = x_65;
x_6 = x_4;
goto lbl_7;
}
}
lbl_7:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_66; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_66 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_68 = x_5;
} else {
 lean::inc(x_66);
 lean::dec(x_5);
 x_68 = lean::box(0);
}
x_69 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_68)) {
 x_70 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_70 = x_68;
}
lean::cnstr_set(x_70, 0, x_66);
lean::cnstr_set(x_70, 1, x_3);
lean::cnstr_set(x_70, 2, x_69);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_6);
return x_71;
}
else
{
obj* x_73; 
lean::dec(x_3);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_5);
lean::cnstr_set(x_73, 1, x_6);
return x_73;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_observing___at_Lean_Parser_token___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_3(x_0, x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_set(x_4, 1, lean::box(0));
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 0);
x_12 = lean::cnstr_get(x_5, 1);
x_14 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 x_16 = x_5;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_5);
 x_16 = lean::box(0);
}
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_10);
x_18 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_16)) {
 x_19 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_19 = x_16;
}
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_12);
lean::cnstr_set(x_19, 2, x_18);
x_20 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_19);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; 
if (lean::is_scalar(x_9)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_9;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_7);
return x_21;
}
else
{
obj* x_22; obj* x_25; obj* x_27; obj* x_28; obj* x_29; 
x_22 = lean::cnstr_get(x_20, 0);
lean::inc(x_22);
lean::dec(x_20);
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
x_27 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_27, 0, x_22);
x_28 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_25);
lean::cnstr_set(x_28, 2, x_18);
if (lean::is_scalar(x_9)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_9;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_7);
return x_29;
}
}
else
{
obj* x_30; obj* x_32; obj* x_33; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_30 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_32 = x_4;
} else {
 lean::inc(x_30);
 lean::dec(x_4);
 x_32 = lean::box(0);
}
x_33 = lean::cnstr_get(x_5, 0);
lean::inc(x_33);
lean::dec(x_5);
x_36 = lean::cnstr_get(x_33, 0);
lean::inc(x_36);
x_38 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_38, 0, x_33);
x_39 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_40 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_36);
lean::cnstr_set(x_40, 2, x_39);
if (lean::is_scalar(x_32)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_32;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_30);
return x_41;
}
}
}
obj* l_Lean_Parser_withTrailing___at_Lean_Parser_token___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_2);
x_5 = l_Lean_Parser_whitespace(x_1, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_8; obj* x_10; obj* x_11; obj* x_13; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_8 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_set(x_5, 1, lean::box(0));
 x_10 = x_5;
} else {
 lean::inc(x_8);
 lean::dec(x_5);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_6, 1);
x_13 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_15 = x_6;
} else {
 lean::inc(x_11);
 lean::inc(x_13);
 lean::dec(x_6);
 x_15 = lean::box(0);
}
lean::inc(x_11);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_2);
lean::cnstr_set(x_17, 1, x_11);
x_18 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_15)) {
 x_19 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_19 = x_15;
}
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_11);
lean::cnstr_set(x_19, 2, x_18);
x_20 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_19);
x_21 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_20);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_25; obj* x_27; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_23 = lean::cnstr_get(x_22, 0);
x_25 = lean::cnstr_get(x_22, 1);
x_27 = lean::cnstr_get(x_22, 2);
if (lean::is_exclusive(x_22)) {
 x_29 = x_22;
} else {
 lean::inc(x_23);
 lean::inc(x_25);
 lean::inc(x_27);
 lean::dec(x_22);
 x_29 = lean::box(0);
}
x_30 = l___private_init_lean_parser_token_3__updateTrailing___main(x_23, x_0);
if (lean::is_scalar(x_29)) {
 x_31 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_31 = x_29;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_25);
lean::cnstr_set(x_31, 2, x_21);
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_27, x_31);
if (lean::is_scalar(x_10)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_10;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_8);
return x_33;
}
else
{
obj* x_35; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_0);
x_35 = lean::cnstr_get(x_22, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_22, sizeof(void*)*1);
if (lean::is_exclusive(x_22)) {
 x_38 = x_22;
} else {
 lean::inc(x_35);
 lean::dec(x_22);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_35);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_37);
x_40 = x_39;
if (lean::is_scalar(x_10)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_10;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_8);
return x_41;
}
}
else
{
obj* x_43; obj* x_45; obj* x_46; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
lean::dec(x_2);
x_43 = lean::cnstr_get(x_5, 1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_set(x_5, 1, lean::box(0));
 x_45 = x_5;
} else {
 lean::inc(x_43);
 lean::dec(x_5);
 x_45 = lean::box(0);
}
x_46 = lean::cnstr_get(x_6, 0);
x_48 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_49 = x_6;
} else {
 lean::inc(x_46);
 lean::dec(x_6);
 x_49 = lean::box(0);
}
if (lean::is_scalar(x_49)) {
 x_50 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_50 = x_49;
}
lean::cnstr_set(x_50, 0, x_46);
lean::cnstr_set_scalar(x_50, sizeof(void*)*1, x_48);
x_51 = x_50;
x_52 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_51);
if (lean::obj_tag(x_53) == 0)
{
obj* x_54; obj* x_56; obj* x_58; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_54 = lean::cnstr_get(x_53, 0);
x_56 = lean::cnstr_get(x_53, 1);
x_58 = lean::cnstr_get(x_53, 2);
if (lean::is_exclusive(x_53)) {
 x_60 = x_53;
} else {
 lean::inc(x_54);
 lean::inc(x_56);
 lean::inc(x_58);
 lean::dec(x_53);
 x_60 = lean::box(0);
}
x_61 = l___private_init_lean_parser_token_3__updateTrailing___main(x_54, x_0);
if (lean::is_scalar(x_60)) {
 x_62 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_62 = x_60;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_56);
lean::cnstr_set(x_62, 2, x_52);
x_63 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_62);
if (lean::is_scalar(x_45)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_45;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_43);
return x_64;
}
else
{
obj* x_66; uint8 x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_0);
x_66 = lean::cnstr_get(x_53, 0);
x_68 = lean::cnstr_get_scalar<uint8>(x_53, sizeof(void*)*1);
if (lean::is_exclusive(x_53)) {
 x_69 = x_53;
} else {
 lean::inc(x_66);
 lean::dec(x_53);
 x_69 = lean::box(0);
}
if (lean::is_scalar(x_69)) {
 x_70 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_70 = x_69;
}
lean::cnstr_set(x_70, 0, x_66);
lean::cnstr_set_scalar(x_70, sizeof(void*)*1, x_68);
x_71 = x_70;
if (lean::is_scalar(x_45)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_45;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_43);
return x_72;
}
}
}
}
obj* l_Lean_Parser_ParsecT_failure___at_Lean_Parser_token___spec__4___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; uint8 x_6; obj* x_7; obj* x_8; obj* x_9; 
x_2 = lean::box(0);
x_3 = l_Lean_Parser_ParsecT_failure___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
x_5 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_3);
lean::cnstr_set(x_5, 2, x_4);
lean::cnstr_set(x_5, 3, x_2);
x_6 = 0;
x_7 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set_scalar(x_7, sizeof(void*)*1, x_6);
x_8 = x_7;
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_1);
return x_9;
}
}
obj* l_Lean_Parser_ParsecT_failure___at_Lean_Parser_token___spec__4(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_failure___at_Lean_Parser_token___spec__4___rarg), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_token___closed__1() {
_start:
{
obj* x_0; obj* x_2; obj* x_3; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
lean::inc(x_0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_token___spec__1___boxed), 5, 2);
lean::closure_set(x_3, 0, x_0);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_token___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::mk_string("token: not implemented");
return x_0;
}
}
obj* l_Lean_Parser_token(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; 
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; obj* x_11; obj* x_13; obj* x_16; obj* x_17; 
lean::inc(x_2);
lean::inc(x_1);
x_10 = l_Lean_Parser_ParsecT_failure___at_Lean_Parser_token___spec__4___rarg(x_1, x_2);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
lean::dec(x_10);
x_16 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_17 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_11);
x_3 = x_17;
x_4 = x_13;
goto lbl_5;
}
else
{
obj* x_18; obj* x_20; obj* x_22; obj* x_24; uint8 x_27; 
x_18 = lean::cnstr_get(x_6, 0);
lean::inc(x_18);
x_20 = lean::cnstr_get(x_1, 1);
lean::inc(x_20);
x_22 = lean::cnstr_get(x_18, 0);
lean::inc(x_22);
x_24 = lean::cnstr_get(x_22, 1);
lean::inc(x_24);
lean::dec(x_22);
x_27 = lean::nat_dec_eq(x_20, x_24);
lean::dec(x_24);
lean::dec(x_20);
if (x_27 == 0)
{
obj* x_32; obj* x_33; 
lean::inc(x_2);
lean::inc(x_1);
x_32 = l_Lean_Parser_ParsecT_failure___at_Lean_Parser_token___spec__4___rarg(x_1, x_2);
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
if (lean::obj_tag(x_33) == 0)
{
obj* x_36; obj* x_38; obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_32);
x_36 = lean::cnstr_get(x_33, 2);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 lean::cnstr_release(x_33, 1);
 x_38 = x_33;
} else {
 lean::inc(x_36);
 lean::dec(x_33);
 x_38 = lean::box(0);
}
x_39 = lean::cnstr_get(x_18, 1);
lean::inc(x_39);
x_41 = lean::box(0);
x_42 = lean::cnstr_get(x_2, 1);
lean::inc(x_42);
x_44 = lean::mk_nat_obj(1u);
x_45 = lean::nat_add(x_42, x_44);
lean::dec(x_42);
x_47 = lean::cnstr_get(x_2, 2);
lean::inc(x_47);
x_49 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_49, 0, x_6);
lean::cnstr_set(x_49, 1, x_45);
lean::cnstr_set(x_49, 2, x_47);
x_50 = lean::cnstr_get(x_18, 2);
lean::inc(x_50);
lean::dec(x_18);
if (lean::is_scalar(x_38)) {
 x_53 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_53 = x_38;
}
lean::cnstr_set(x_53, 0, x_50);
lean::cnstr_set(x_53, 1, x_39);
lean::cnstr_set(x_53, 2, x_41);
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_36, x_53);
x_55 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_56 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_55, x_54);
x_3 = x_56;
x_4 = x_49;
goto lbl_5;
}
else
{
obj* x_59; obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_6);
lean::dec(x_18);
x_59 = lean::cnstr_get(x_32, 1);
lean::inc(x_59);
lean::dec(x_32);
x_62 = lean::cnstr_get(x_33, 0);
x_64 = lean::cnstr_get_scalar<uint8>(x_33, sizeof(void*)*1);
if (lean::is_exclusive(x_33)) {
 x_65 = x_33;
} else {
 lean::inc(x_62);
 lean::dec(x_33);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_62);
lean::cnstr_set_scalar(x_66, sizeof(void*)*1, x_64);
x_67 = x_66;
x_68 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_69 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_68, x_67);
x_3 = x_69;
x_4 = x_59;
goto lbl_5;
}
}
else
{
obj* x_70; obj* x_72; obj* x_73; obj* x_75; obj* x_76; obj* x_78; obj* x_80; obj* x_81; obj* x_84; 
x_70 = lean::cnstr_get(x_18, 1);
lean::inc(x_70);
x_72 = lean::box(0);
x_73 = lean::cnstr_get(x_2, 1);
lean::inc(x_73);
x_75 = lean::mk_nat_obj(1u);
x_76 = lean::nat_add(x_73, x_75);
lean::dec(x_73);
x_78 = lean::cnstr_get(x_2, 2);
lean::inc(x_78);
x_80 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_80, 0, x_6);
lean::cnstr_set(x_80, 1, x_76);
lean::cnstr_set(x_80, 2, x_78);
x_81 = lean::cnstr_get(x_18, 2);
lean::inc(x_81);
lean::dec(x_18);
x_84 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_84, 0, x_81);
lean::cnstr_set(x_84, 1, x_70);
lean::cnstr_set(x_84, 2, x_72);
x_3 = x_84;
x_4 = x_80;
goto lbl_5;
}
}
lbl_5:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_88 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_89 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_88, x_3);
x_90 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_88, x_89);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_4);
return x_91;
}
else
{
obj* x_92; uint8 x_94; obj* x_96; obj* x_97; obj* x_99; obj* x_102; obj* x_104; obj* x_105; 
x_92 = lean::cnstr_get(x_3, 0);
lean::inc(x_92);
x_94 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
lean::dec(x_3);
x_99 = lean::cnstr_get(x_92, 0);
lean::inc(x_99);
lean::dec(x_92);
x_102 = l_Lean_Parser_token___closed__1;
lean::inc(x_0);
x_104 = l_Lean_Parser_MonadParsec_observing___at_Lean_Parser_token___spec__2(x_102, x_0, x_99, x_4);
x_105 = lean::cnstr_get(x_104, 0);
lean::inc(x_105);
if (lean::obj_tag(x_105) == 0)
{
obj* x_107; obj* x_110; obj* x_112; obj* x_114; obj* x_118; obj* x_119; 
x_107 = lean::cnstr_get(x_104, 1);
lean::inc(x_107);
lean::dec(x_104);
x_110 = lean::cnstr_get(x_105, 0);
lean::inc(x_110);
x_112 = lean::cnstr_get(x_105, 1);
lean::inc(x_112);
x_114 = lean::cnstr_get(x_105, 2);
lean::inc(x_114);
lean::dec(x_105);
lean::inc(x_0);
x_118 = l_Lean_Parser_matchToken(x_0, x_112, x_107);
x_119 = lean::cnstr_get(x_118, 0);
lean::inc(x_119);
if (lean::obj_tag(x_119) == 0)
{
obj* x_121; obj* x_124; obj* x_126; obj* x_128; obj* x_131; obj* x_132; 
x_121 = lean::cnstr_get(x_118, 1);
lean::inc(x_121);
lean::dec(x_118);
x_124 = lean::cnstr_get(x_119, 0);
lean::inc(x_124);
x_126 = lean::cnstr_get(x_119, 1);
lean::inc(x_126);
x_128 = lean::cnstr_get(x_119, 2);
lean::inc(x_128);
lean::dec(x_119);
if (lean::obj_tag(x_124) == 0)
{
if (lean::obj_tag(x_110) == 0)
{
obj* x_136; obj* x_137; obj* x_139; 
lean::dec(x_110);
lean::inc(x_0);
x_136 = l_Lean_Parser_numberOrStringLit(x_0, x_126, x_121);
x_137 = lean::cnstr_get(x_136, 0);
lean::inc(x_137);
x_139 = lean::cnstr_get(x_136, 1);
lean::inc(x_139);
lean::dec(x_136);
x_131 = x_137;
x_132 = x_139;
goto lbl_133;
}
else
{
obj* x_144; obj* x_145; obj* x_147; 
lean::dec(x_110);
lean::inc(x_0);
x_144 = l___private_init_lean_parser_token_4__ident_x_27(x_0, x_126, x_121);
x_145 = lean::cnstr_get(x_144, 0);
lean::inc(x_145);
x_147 = lean::cnstr_get(x_144, 1);
lean::inc(x_147);
lean::dec(x_144);
x_131 = x_145;
x_132 = x_147;
goto lbl_133;
}
}
else
{
obj* x_150; obj* x_153; 
x_150 = lean::cnstr_get(x_124, 0);
lean::inc(x_150);
lean::dec(x_124);
x_153 = lean::cnstr_get(x_150, 2);
lean::inc(x_153);
if (lean::obj_tag(x_153) == 0)
{
if (lean::obj_tag(x_110) == 0)
{
obj* x_157; obj* x_160; obj* x_162; 
lean::dec(x_110);
lean::inc(x_1);
x_157 = l___private_init_lean_parser_token_5__mkConsumeToken(x_150, x_1, x_0, x_126, x_121);
lean::dec(x_126);
lean::dec(x_150);
x_160 = lean::cnstr_get(x_157, 0);
lean::inc(x_160);
x_162 = lean::cnstr_get(x_157, 1);
lean::inc(x_162);
lean::dec(x_157);
x_131 = x_160;
x_132 = x_162;
goto lbl_133;
}
else
{
obj* x_168; obj* x_170; obj* x_172; 
lean::dec(x_110);
lean::inc(x_0);
lean::inc(x_1);
x_168 = l_Lean_Parser_tokenCont(x_1, x_150, x_0, x_126, x_121);
lean::dec(x_150);
x_170 = lean::cnstr_get(x_168, 0);
lean::inc(x_170);
x_172 = lean::cnstr_get(x_168, 1);
lean::inc(x_172);
lean::dec(x_168);
x_131 = x_170;
x_132 = x_172;
goto lbl_133;
}
}
else
{
obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_183; obj* x_185; 
lean::dec(x_153);
lean::dec(x_150);
lean::dec(x_110);
x_178 = lean::box(0);
x_179 = l_Lean_Parser_token___closed__2;
x_180 = l_mjoin___rarg___closed__1;
x_181 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_179, x_180, x_178, x_178, x_0, x_126, x_121);
lean::dec(x_126);
x_183 = lean::cnstr_get(x_181, 0);
lean::inc(x_183);
x_185 = lean::cnstr_get(x_181, 1);
lean::inc(x_185);
lean::dec(x_181);
x_131 = x_183;
x_132 = x_185;
goto lbl_133;
}
}
lbl_133:
{
if (lean::obj_tag(x_131) == 0)
{
obj* x_188; obj* x_190; obj* x_192; obj* x_195; obj* x_197; 
x_188 = lean::cnstr_get(x_131, 0);
lean::inc(x_188);
x_190 = lean::cnstr_get(x_131, 1);
lean::inc(x_190);
x_192 = lean::cnstr_get(x_131, 2);
lean::inc(x_192);
lean::dec(x_131);
x_195 = l_Lean_Parser_withTrailing___at_Lean_Parser_token___spec__3(x_188, x_0, x_190, x_132);
lean::dec(x_0);
x_197 = lean::cnstr_get(x_195, 0);
lean::inc(x_197);
if (lean::obj_tag(x_197) == 0)
{
obj* x_200; obj* x_202; obj* x_204; obj* x_206; obj* x_209; obj* x_210; obj* x_211; obj* x_213; obj* x_216; obj* x_217; obj* x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; 
lean::dec(x_195);
x_200 = lean::cnstr_get(x_197, 0);
x_202 = lean::cnstr_get(x_197, 1);
x_204 = lean::cnstr_get(x_197, 2);
if (lean::is_exclusive(x_197)) {
 x_206 = x_197;
} else {
 lean::inc(x_200);
 lean::inc(x_202);
 lean::inc(x_204);
 lean::dec(x_197);
 x_206 = lean::box(0);
}
lean::inc(x_200);
lean::inc(x_202);
x_209 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_209, 0, x_1);
lean::cnstr_set(x_209, 1, x_202);
lean::cnstr_set(x_209, 2, x_200);
x_210 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_210, 0, x_209);
x_211 = lean::cnstr_get(x_2, 1);
lean::inc(x_211);
x_213 = lean::cnstr_get(x_2, 2);
lean::inc(x_213);
lean::dec(x_2);
x_216 = lean::mk_nat_obj(1u);
x_217 = lean::nat_add(x_213, x_216);
lean::dec(x_213);
x_219 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_219, 0, x_210);
lean::cnstr_set(x_219, 1, x_211);
lean::cnstr_set(x_219, 2, x_217);
x_220 = l_Lean_Parser_matchToken___closed__1;
if (lean::is_scalar(x_206)) {
 x_221 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_221 = x_206;
}
lean::cnstr_set(x_221, 0, x_200);
lean::cnstr_set(x_221, 1, x_202);
lean::cnstr_set(x_221, 2, x_220);
x_222 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_204, x_221);
x_223 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_192, x_222);
x_224 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_128, x_223);
x_225 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_114, x_224);
x_96 = x_225;
x_97 = x_219;
goto lbl_98;
}
else
{
obj* x_228; obj* x_231; uint8 x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; 
lean::dec(x_1);
lean::dec(x_2);
x_228 = lean::cnstr_get(x_195, 1);
lean::inc(x_228);
lean::dec(x_195);
x_231 = lean::cnstr_get(x_197, 0);
x_233 = lean::cnstr_get_scalar<uint8>(x_197, sizeof(void*)*1);
if (lean::is_exclusive(x_197)) {
 x_234 = x_197;
} else {
 lean::inc(x_231);
 lean::dec(x_197);
 x_234 = lean::box(0);
}
if (lean::is_scalar(x_234)) {
 x_235 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_235 = x_234;
}
lean::cnstr_set(x_235, 0, x_231);
lean::cnstr_set_scalar(x_235, sizeof(void*)*1, x_233);
x_236 = x_235;
x_237 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_192, x_236);
x_238 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_128, x_237);
x_239 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_114, x_238);
x_96 = x_239;
x_97 = x_228;
goto lbl_98;
}
}
else
{
obj* x_243; uint8 x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_250; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_243 = lean::cnstr_get(x_131, 0);
x_245 = lean::cnstr_get_scalar<uint8>(x_131, sizeof(void*)*1);
if (lean::is_exclusive(x_131)) {
 x_246 = x_131;
} else {
 lean::inc(x_243);
 lean::dec(x_131);
 x_246 = lean::box(0);
}
if (lean::is_scalar(x_246)) {
 x_247 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_247 = x_246;
}
lean::cnstr_set(x_247, 0, x_243);
lean::cnstr_set_scalar(x_247, sizeof(void*)*1, x_245);
x_248 = x_247;
x_249 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_128, x_248);
x_250 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_114, x_249);
x_96 = x_250;
x_97 = x_132;
goto lbl_98;
}
}
}
else
{
obj* x_255; obj* x_258; uint8 x_260; obj* x_261; obj* x_262; obj* x_263; obj* x_264; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
lean::dec(x_110);
x_255 = lean::cnstr_get(x_118, 1);
lean::inc(x_255);
lean::dec(x_118);
x_258 = lean::cnstr_get(x_119, 0);
x_260 = lean::cnstr_get_scalar<uint8>(x_119, sizeof(void*)*1);
if (lean::is_exclusive(x_119)) {
 x_261 = x_119;
} else {
 lean::inc(x_258);
 lean::dec(x_119);
 x_261 = lean::box(0);
}
if (lean::is_scalar(x_261)) {
 x_262 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_262 = x_261;
}
lean::cnstr_set(x_262, 0, x_258);
lean::cnstr_set_scalar(x_262, sizeof(void*)*1, x_260);
x_263 = x_262;
x_264 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_114, x_263);
x_96 = x_264;
x_97 = x_255;
goto lbl_98;
}
}
else
{
obj* x_268; obj* x_271; uint8 x_273; obj* x_274; obj* x_275; obj* x_276; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_268 = lean::cnstr_get(x_104, 1);
lean::inc(x_268);
lean::dec(x_104);
x_271 = lean::cnstr_get(x_105, 0);
x_273 = lean::cnstr_get_scalar<uint8>(x_105, sizeof(void*)*1);
if (lean::is_exclusive(x_105)) {
 x_274 = x_105;
} else {
 lean::inc(x_271);
 lean::dec(x_105);
 x_274 = lean::box(0);
}
if (lean::is_scalar(x_274)) {
 x_275 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_275 = x_274;
}
lean::cnstr_set(x_275, 0, x_271);
lean::cnstr_set_scalar(x_275, sizeof(void*)*1, x_273);
x_276 = x_275;
x_96 = x_276;
x_97 = x_268;
goto lbl_98;
}
lbl_98:
{
if (lean::obj_tag(x_96) == 0)
{
obj* x_277; obj* x_278; obj* x_279; obj* x_280; 
x_277 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_278 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_277, x_96);
x_279 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_277, x_278);
x_280 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_280, 0, x_279);
lean::cnstr_set(x_280, 1, x_97);
return x_280;
}
else
{
uint8 x_281; 
x_281 = lean::cnstr_get_scalar<uint8>(x_96, sizeof(void*)*1);
if (x_94 == 0)
{
obj* x_282; obj* x_284; obj* x_285; obj* x_286; obj* x_287; obj* x_288; obj* x_289; obj* x_290; 
x_282 = lean::cnstr_get(x_96, 0);
if (lean::is_exclusive(x_96)) {
 x_284 = x_96;
} else {
 lean::inc(x_282);
 lean::dec(x_96);
 x_284 = lean::box(0);
}
if (lean::is_scalar(x_284)) {
 x_285 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_285 = x_284;
}
lean::cnstr_set(x_285, 0, x_282);
lean::cnstr_set_scalar(x_285, sizeof(void*)*1, x_281);
x_286 = x_285;
x_287 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_288 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_287, x_286);
x_289 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_287, x_288);
x_290 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_290, 0, x_289);
lean::cnstr_set(x_290, 1, x_97);
return x_290;
}
else
{
obj* x_291; obj* x_293; uint8 x_294; obj* x_295; obj* x_296; obj* x_297; 
x_291 = lean::cnstr_get(x_96, 0);
if (lean::is_exclusive(x_96)) {
 x_293 = x_96;
} else {
 lean::inc(x_291);
 lean::dec(x_96);
 x_293 = lean::box(0);
}
x_294 = 1;
if (lean::is_scalar(x_293)) {
 x_295 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_295 = x_293;
}
lean::cnstr_set(x_295, 0, x_291);
lean::cnstr_set_scalar(x_295, sizeof(void*)*1, x_294);
x_296 = x_295;
x_297 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_297, 0, x_296);
lean::cnstr_set(x_297, 1, x_97);
return x_297;
}
}
}
}
}
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_token___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_token___spec__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_withTrailing___at_Lean_Parser_token___spec__3___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_withTrailing___at_Lean_Parser_token___spec__3(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_ParsecT_failure___at_Lean_Parser_token___spec__4___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ParsecT_failure___at_Lean_Parser_token___spec__4(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_peekToken___spec__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; 
lean::inc(x_1);
x_4 = l_Lean_Parser_token(x_0, x_1, x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 0);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_12 = x_5;
} else {
 lean::inc(x_10);
 lean::dec(x_5);
 x_12 = lean::box(0);
}
x_13 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_12)) {
 x_14 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_14 = x_12;
}
lean::cnstr_set(x_14, 0, x_10);
lean::cnstr_set(x_14, 1, x_1);
lean::cnstr_set(x_14, 2, x_13);
if (lean::is_scalar(x_9)) {
 x_15 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_15 = x_9;
}
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_7);
return x_15;
}
else
{
obj* x_17; obj* x_19; obj* x_20; 
lean::dec(x_1);
x_17 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_19 = x_4;
} else {
 lean::inc(x_17);
 lean::dec(x_4);
 x_19 = lean::box(0);
}
if (lean::is_scalar(x_19)) {
 x_20 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_20 = x_19;
}
lean::cnstr_set(x_20, 0, x_5);
lean::cnstr_set(x_20, 1, x_17);
return x_20;
}
}
}
obj* l_Lean_Parser_MonadParsec_observing___at_Lean_Parser_peekToken___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::apply_3(x_0, x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_9; obj* x_10; obj* x_12; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_7 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 lean::cnstr_set(x_4, 1, lean::box(0));
 x_9 = x_4;
} else {
 lean::inc(x_7);
 lean::dec(x_4);
 x_9 = lean::box(0);
}
x_10 = lean::cnstr_get(x_5, 0);
x_12 = lean::cnstr_get(x_5, 1);
x_14 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 x_16 = x_5;
} else {
 lean::inc(x_10);
 lean::inc(x_12);
 lean::inc(x_14);
 lean::dec(x_5);
 x_16 = lean::box(0);
}
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_10);
x_18 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_16)) {
 x_19 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_19 = x_16;
}
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_12);
lean::cnstr_set(x_19, 2, x_18);
x_20 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_19);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; 
if (lean::is_scalar(x_9)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_9;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_7);
return x_21;
}
else
{
obj* x_22; obj* x_25; obj* x_27; obj* x_28; obj* x_29; 
x_22 = lean::cnstr_get(x_20, 0);
lean::inc(x_22);
lean::dec(x_20);
x_25 = lean::cnstr_get(x_22, 0);
lean::inc(x_25);
x_27 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_27, 0, x_22);
x_28 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_25);
lean::cnstr_set(x_28, 2, x_18);
if (lean::is_scalar(x_9)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_9;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_7);
return x_29;
}
}
else
{
obj* x_30; obj* x_32; obj* x_33; obj* x_36; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_30 = lean::cnstr_get(x_4, 1);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_32 = x_4;
} else {
 lean::inc(x_30);
 lean::dec(x_4);
 x_32 = lean::box(0);
}
x_33 = lean::cnstr_get(x_5, 0);
lean::inc(x_33);
lean::dec(x_5);
x_36 = lean::cnstr_get(x_33, 0);
lean::inc(x_36);
x_38 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_38, 0, x_33);
x_39 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_40 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_40, 0, x_38);
lean::cnstr_set(x_40, 1, x_36);
lean::cnstr_set(x_40, 2, x_39);
if (lean::is_scalar(x_32)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_32;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_30);
return x_41;
}
}
}
obj* l_Lean_Parser_peekToken___lambda__1(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_10; 
x_3 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_peekToken___spec__1(x_0, x_1, x_2);
x_4 = lean::cnstr_get(x_3, 0);
x_6 = lean::cnstr_get(x_3, 1);
if (lean::is_exclusive(x_3)) {
 x_8 = x_3;
} else {
 lean::inc(x_4);
 lean::inc(x_6);
 lean::dec(x_3);
 x_8 = lean::box(0);
}
x_9 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_4);
if (lean::is_scalar(x_8)) {
 x_10 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_10 = x_8;
}
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_6);
return x_10;
}
}
obj* _init_l_Lean_Parser_peekToken___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_peekToken___lambda__1), 3, 0);
return x_0;
}
}
obj* l_Lean_Parser_peekToken(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_Lean_Parser_peekToken___closed__1;
x_4 = l_Lean_Parser_MonadParsec_observing___at_Lean_Parser_peekToken___spec__2(x_3, x_0, x_1, x_2);
return x_4;
}
}
obj* l_Lean_Parser_symbolCore___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_8; obj* x_9; 
lean::inc(x_4);
lean::inc(x_3);
x_8 = l_Lean_Parser_token(x_3, x_4, x_5);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_13; obj* x_14; obj* x_16; obj* x_18; obj* x_20; obj* x_21; 
x_11 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_set(x_8, 1, lean::box(0));
 x_13 = x_8;
} else {
 lean::inc(x_11);
 lean::dec(x_8);
 x_13 = lean::box(0);
}
x_14 = lean::cnstr_get(x_9, 0);
x_16 = lean::cnstr_get(x_9, 1);
x_18 = lean::cnstr_get(x_9, 2);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 lean::cnstr_set(x_9, 1, lean::box(0));
 lean::cnstr_set(x_9, 2, lean::box(0));
 x_20 = x_9;
} else {
 lean::inc(x_14);
 lean::inc(x_16);
 lean::inc(x_18);
 lean::dec(x_9);
 x_20 = lean::box(0);
}
switch (lean::obj_tag(x_14)) {
case 0:
{
obj* x_23; obj* x_25; uint8 x_28; 
x_23 = lean::cnstr_get(x_14, 0);
lean::inc(x_23);
x_25 = lean::cnstr_get(x_23, 1);
lean::inc(x_25);
lean::dec(x_23);
x_28 = lean::string_dec_eq(x_2, x_25);
if (x_28 == 0)
{
obj* x_31; obj* x_32; obj* x_33; obj* x_37; 
lean::dec(x_13);
lean::dec(x_20);
x_31 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_31, 0, x_4);
x_32 = lean::box(0);
x_33 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_25, x_0, x_31, x_32, x_3, x_16, x_11);
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_31);
x_37 = lean::cnstr_get(x_33, 0);
lean::inc(x_37);
if (lean::obj_tag(x_37) == 0)
{
obj* x_39; obj* x_41; obj* x_42; obj* x_44; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_39 = lean::cnstr_get(x_33, 1);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 x_41 = x_33;
} else {
 lean::inc(x_39);
 lean::dec(x_33);
 x_41 = lean::box(0);
}
x_42 = lean::cnstr_get(x_37, 1);
x_44 = lean::cnstr_get(x_37, 2);
if (lean::is_exclusive(x_37)) {
 lean::cnstr_release(x_37, 0);
 x_46 = x_37;
} else {
 lean::inc(x_42);
 lean::inc(x_44);
 lean::dec(x_37);
 x_46 = lean::box(0);
}
x_47 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_46)) {
 x_48 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_48 = x_46;
}
lean::cnstr_set(x_48, 0, x_14);
lean::cnstr_set(x_48, 1, x_42);
lean::cnstr_set(x_48, 2, x_47);
x_49 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_44, x_48);
x_50 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_49);
x_51 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_47, x_50);
x_52 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_51, x_1);
x_53 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_52);
if (lean::is_scalar(x_41)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_41;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_39);
return x_54;
}
else
{
obj* x_56; obj* x_58; obj* x_59; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
lean::dec(x_14);
x_56 = lean::cnstr_get(x_33, 1);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 x_58 = x_33;
} else {
 lean::inc(x_56);
 lean::dec(x_33);
 x_58 = lean::box(0);
}
x_59 = lean::cnstr_get(x_37, 0);
x_61 = lean::cnstr_get_scalar<uint8>(x_37, sizeof(void*)*1);
if (lean::is_exclusive(x_37)) {
 x_62 = x_37;
} else {
 lean::inc(x_59);
 lean::dec(x_37);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_59);
lean::cnstr_set_scalar(x_63, sizeof(void*)*1, x_61);
x_64 = x_63;
x_65 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_64);
x_66 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_67 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_66, x_65);
x_68 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_67, x_1);
x_69 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_68);
if (lean::is_scalar(x_58)) {
 x_70 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_70 = x_58;
}
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_56);
return x_70;
}
}
else
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_25);
x_75 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_20)) {
 x_76 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_76 = x_20;
}
lean::cnstr_set(x_76, 0, x_14);
lean::cnstr_set(x_76, 1, x_16);
lean::cnstr_set(x_76, 2, x_75);
x_77 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_76);
x_78 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_79 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_78, x_77);
x_80 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_79, x_1);
x_81 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_80);
if (lean::is_scalar(x_13)) {
 x_82 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_82 = x_13;
}
lean::cnstr_set(x_82, 0, x_81);
lean::cnstr_set(x_82, 1, x_11);
return x_82;
}
}
case 3:
{
obj* x_85; 
lean::dec(x_13);
lean::dec(x_20);
x_85 = lean::box(0);
x_21 = x_85;
goto lbl_22;
}
default:
{
obj* x_89; 
lean::dec(x_13);
lean::dec(x_14);
lean::dec(x_20);
x_89 = lean::box(0);
x_21 = x_89;
goto lbl_22;
}
}
lbl_22:
{
obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_98; obj* x_100; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_21);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_4);
x_92 = lean::box(0);
x_93 = l_String_splitAux___main___closed__1;
x_94 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_93, x_0, x_91, x_92, x_3, x_16, x_11);
lean::dec(x_16);
lean::dec(x_3);
lean::dec(x_91);
x_98 = lean::cnstr_get(x_94, 0);
x_100 = lean::cnstr_get(x_94, 1);
if (lean::is_exclusive(x_94)) {
 x_102 = x_94;
} else {
 lean::inc(x_98);
 lean::inc(x_100);
 lean::dec(x_94);
 x_102 = lean::box(0);
}
x_103 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_98);
x_104 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_105 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_104, x_103);
x_106 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_105, x_1);
x_107 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_106);
if (lean::is_scalar(x_102)) {
 x_108 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_108 = x_102;
}
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_100);
return x_108;
}
}
else
{
obj* x_112; obj* x_114; obj* x_115; uint8 x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
x_112 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_114 = x_8;
} else {
 lean::inc(x_112);
 lean::dec(x_8);
 x_114 = lean::box(0);
}
x_115 = lean::cnstr_get(x_9, 0);
x_117 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_118 = x_9;
} else {
 lean::inc(x_115);
 lean::dec(x_9);
 x_118 = lean::box(0);
}
if (lean::is_scalar(x_118)) {
 x_119 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_119 = x_118;
}
lean::cnstr_set(x_119, 0, x_115);
lean::cnstr_set_scalar(x_119, sizeof(void*)*1, x_117);
x_120 = x_119;
x_121 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_122 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_121, x_120);
x_123 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_122, x_1);
x_124 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_123);
if (lean::is_scalar(x_114)) {
 x_125 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_125 = x_114;
}
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_112);
return x_125;
}
}
}
obj* l_Lean_Parser_symbolCore___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
lean::inc(x_1);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_5, 0, x_1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___rarg___lambda__1___boxed), 6, 3);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_1);
x_7 = lean::apply_2(x_0, lean::box(0), x_6);
return x_7;
}
}
obj* l_Lean_Parser_symbolCore(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_Lean_Parser_symbolCore___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_symbolCore___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_symbolCore___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_symbolCore___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_symbolCore___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_symbolCore(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_symbol___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_5; obj* x_6; 
x_3 = l_String_trim(x_1);
lean::inc(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_5, 0, x_3);
x_6 = l_Lean_Parser_symbolCore___rarg(x_0, x_3, x_2, x_5);
return x_6;
}
}
obj* l_Lean_Parser_symbol(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbol___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_symbol___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_symbol___rarg(x_0, x_1, x_2);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_symbol___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_symbol(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_symbol_tokens___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = l_String_trim(x_0);
x_3 = lean::box(0);
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* l_Lean_Parser_symbol_tokens(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbol_tokens___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_symbol_tokens___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_Parser_symbol_tokens___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_symbol_tokens(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_symbol_View___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_Parser_raw_view___rarg___closed__1;
x_4 = l_Lean_Parser_raw_view___rarg___closed__2;
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
return x_5;
}
}
obj* l_Lean_Parser_symbol_View(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbol_View___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_symbol_View___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_symbol_View___rarg(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_symbol_View___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_symbol_View(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_symbol_viewDefault___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
}
obj* l_Lean_Parser_symbol_viewDefault(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbol_viewDefault___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_symbol_viewDefault___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_symbol_viewDefault___rarg(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_symbol_viewDefault___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_symbol_viewDefault(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_tryView___at_Lean_Parser_number_Parser___spec__1(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_Parser_Syntax_isOfKind___main(x_0, x_1);
if (x_2 == 0)
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_9; obj* x_10; 
x_5 = l_Lean_Parser_number_HasView;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
x_9 = lean::apply_1(x_6, x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
}
}
obj* l_Lean_Parser_number_Parser___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_2);
lean::inc(x_1);
x_6 = l_Lean_Parser_token(x_1, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_21; 
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_set(x_6, 1, lean::box(0));
 x_11 = x_6;
} else {
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_7, 0);
x_14 = lean::cnstr_get(x_7, 1);
x_16 = lean::cnstr_get(x_7, 2);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 lean::cnstr_set(x_7, 2, lean::box(0));
 x_18 = x_7;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_7);
 x_18 = lean::box(0);
}
x_19 = l_Lean_Parser_number;
lean::inc(x_12);
x_21 = l_Lean_Parser_tryView___at_Lean_Parser_number_Parser___spec__1(x_19, x_12);
if (lean::obj_tag(x_21) == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_33; obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_11);
lean::dec(x_12);
lean::dec(x_18);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_2);
x_26 = lean::box(0);
x_27 = l_String_splitAux___main___closed__1;
lean::inc(x_0);
x_29 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_27, x_0, x_25, x_26, x_1, x_14, x_9);
lean::dec(x_14);
lean::dec(x_1);
lean::dec(x_25);
x_33 = lean::cnstr_get(x_29, 0);
x_35 = lean::cnstr_get(x_29, 1);
if (lean::is_exclusive(x_29)) {
 x_37 = x_29;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_29);
 x_37 = lean::box(0);
}
x_38 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_39 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_33);
x_40 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_39);
x_41 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_40);
x_42 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_41, x_0);
x_43 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_42);
if (lean::is_scalar(x_37)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_37;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_35);
return x_44;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_21);
x_48 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_18)) {
 x_49 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_49 = x_18;
}
lean::cnstr_set(x_49, 0, x_12);
lean::cnstr_set(x_49, 1, x_14);
lean::cnstr_set(x_49, 2, x_48);
x_50 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_49);
x_51 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_52 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_51, x_50);
x_53 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_52, x_0);
x_54 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_53);
if (lean::is_scalar(x_11)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_11;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_9);
return x_55;
}
}
else
{
obj* x_58; obj* x_60; obj* x_61; uint8 x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
lean::dec(x_1);
lean::dec(x_2);
x_58 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_60 = x_6;
} else {
 lean::inc(x_58);
 lean::dec(x_6);
 x_60 = lean::box(0);
}
x_61 = lean::cnstr_get(x_7, 0);
x_63 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_64 = x_7;
} else {
 lean::inc(x_61);
 lean::dec(x_7);
 x_64 = lean::box(0);
}
if (lean::is_scalar(x_64)) {
 x_65 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_65 = x_64;
}
lean::cnstr_set(x_65, 0, x_61);
lean::cnstr_set_scalar(x_65, sizeof(void*)*1, x_63);
x_66 = x_65;
x_67 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_68 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_67, x_66);
x_69 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_68, x_0);
x_70 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_69);
if (lean::is_scalar(x_60)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_60;
}
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_58);
return x_71;
}
}
}
obj* _init_l_Lean_Parser_number_Parser___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("number");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser___rarg___lambda__1), 4, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Parser_number_Parser___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_number_Parser___rarg___closed__1;
x_2 = lean::apply_2(x_0, lean::box(0), x_1);
return x_2;
}
}
obj* l_Lean_Parser_number_Parser(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_tryView___at_Lean_Parser_number_Parser___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_tryView___at_Lean_Parser_number_Parser___spec__1(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_Parser_number_Parser___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_number_Parser(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_number_Parser_tokens(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_Lean_Parser_number_Parser_tokens___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_number_Parser_tokens(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_number_Parser_view___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_number_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_number_Parser_view___rarg___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_number_HasView;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_number_Parser_view___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_number_Parser_view___rarg___closed__1;
x_2 = l_Lean_Parser_number_Parser_view___rarg___closed__2;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_number_Parser_view(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser_view___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_number_Parser_view___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_number_Parser_view___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_number_Parser_view___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_number_Parser_view(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l___private_init_lean_parser_token_7__toNatCore___main(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_2, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint32 x_9; uint8 x_10; obj* x_11; obj* x_13; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_2, x_6);
lean::dec(x_2);
x_9 = l_String_OldIterator_curr___main(x_1);
x_10 = l_Char_isDigit(x_9);
x_11 = lean::nat_mul(x_3, x_0);
lean::dec(x_3);
x_13 = l_String_OldIterator_next___main(x_1);
if (x_10 == 0)
{
uint32 x_14; uint8 x_15; 
x_14 = 97;
x_15 = x_14 <= x_9;
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_20; 
x_16 = lean::uint32_to_nat(x_9);
x_17 = l_Lean_Parser_parseHexDigit___rarg___lambda__5___closed__1;
x_18 = lean::nat_sub(x_16, x_17);
lean::dec(x_16);
x_20 = lean::nat_add(x_11, x_18);
lean::dec(x_18);
lean::dec(x_11);
x_1 = x_13;
x_2 = x_7;
x_3 = x_20;
goto _start;
}
else
{
uint32 x_24; uint8 x_25; 
x_24 = 102;
x_25 = x_9 <= x_24;
if (x_25 == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_30; 
x_26 = lean::uint32_to_nat(x_9);
x_27 = l_Lean_Parser_parseHexDigit___rarg___lambda__5___closed__1;
x_28 = lean::nat_sub(x_26, x_27);
lean::dec(x_26);
x_30 = lean::nat_add(x_11, x_28);
lean::dec(x_28);
lean::dec(x_11);
x_1 = x_13;
x_2 = x_7;
x_3 = x_30;
goto _start;
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_38; 
x_34 = lean::uint32_to_nat(x_9);
x_35 = l_Lean_Parser_parseHexDigit___rarg___lambda__3___closed__1;
x_36 = lean::nat_sub(x_34, x_35);
lean::dec(x_34);
x_38 = lean::nat_add(x_11, x_36);
lean::dec(x_36);
lean::dec(x_11);
x_1 = x_13;
x_2 = x_7;
x_3 = x_38;
goto _start;
}
}
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_46; 
x_42 = lean::uint32_to_nat(x_9);
x_43 = l_String_foldlAux___main___at_String_toNat___spec__1___closed__1;
x_44 = lean::nat_sub(x_42, x_43);
lean::dec(x_42);
x_46 = lean::nat_add(x_11, x_44);
lean::dec(x_44);
lean::dec(x_11);
x_1 = x_13;
x_2 = x_7;
x_3 = x_46;
goto _start;
}
}
else
{
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
}
obj* l___private_init_lean_parser_token_7__toNatCore___main___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_token_7__toNatCore___main(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l___private_init_lean_parser_token_7__toNatCore(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_token_7__toNatCore___main(x_0, x_1, x_2, x_3);
return x_4;
}
}
obj* l___private_init_lean_parser_token_7__toNatCore___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l___private_init_lean_parser_token_7__toNatCore(x_0, x_1, x_2, x_3);
lean::dec(x_0);
return x_4;
}
}
obj* l___private_init_lean_parser_token_8__toNatBase(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; usize x_3; obj* x_5; obj* x_6; obj* x_7; obj* x_9; 
x_2 = lean::mk_nat_obj(0u);
x_3 = l_String_toSubstring___closed__1;
lean::inc(x_0);
x_5 = lean::alloc_cnstr(0, 2, sizeof(size_t)*1);
lean::cnstr_set(x_5, 0, x_0);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set_scalar(x_5, sizeof(void*)*2, x_3);
x_6 = x_5;
x_7 = lean::string_length(x_0);
lean::dec(x_0);
x_9 = l___private_init_lean_parser_token_7__toNatCore___main(x_1, x_6, x_7, x_2);
return x_9;
}
}
obj* l___private_init_lean_parser_token_8__toNatBase___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l___private_init_lean_parser_token_8__toNatBase(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_number_View_toNat___main(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 0:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_4; 
x_4 = lean::mk_nat_obj(1138u);
return x_4;
}
else
{
obj* x_5; obj* x_8; obj* x_11; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
lean::dec(x_1);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
lean::dec(x_5);
x_11 = l_String_toNat(x_8);
lean::dec(x_8);
return x_11;
}
}
case 1:
{
obj* x_13; 
x_13 = lean::cnstr_get(x_0, 0);
lean::inc(x_13);
lean::dec(x_0);
if (lean::obj_tag(x_13) == 0)
{
obj* x_16; 
x_16 = lean::mk_nat_obj(1138u);
return x_16;
}
else
{
obj* x_17; obj* x_20; obj* x_23; obj* x_24; 
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
lean::dec(x_13);
x_20 = lean::cnstr_get(x_17, 1);
lean::inc(x_20);
lean::dec(x_17);
x_23 = lean::mk_nat_obj(2u);
x_24 = l___private_init_lean_parser_token_8__toNatBase(x_20, x_23);
return x_24;
}
}
case 2:
{
obj* x_25; 
x_25 = lean::cnstr_get(x_0, 0);
lean::inc(x_25);
lean::dec(x_0);
if (lean::obj_tag(x_25) == 0)
{
obj* x_28; 
x_28 = lean::mk_nat_obj(1138u);
return x_28;
}
else
{
obj* x_29; obj* x_32; obj* x_35; obj* x_36; 
x_29 = lean::cnstr_get(x_25, 0);
lean::inc(x_29);
lean::dec(x_25);
x_32 = lean::cnstr_get(x_29, 1);
lean::inc(x_32);
lean::dec(x_29);
x_35 = lean::mk_nat_obj(8u);
x_36 = l___private_init_lean_parser_token_8__toNatBase(x_32, x_35);
return x_36;
}
}
default:
{
obj* x_37; 
x_37 = lean::cnstr_get(x_0, 0);
lean::inc(x_37);
lean::dec(x_0);
if (lean::obj_tag(x_37) == 0)
{
obj* x_40; 
x_40 = lean::mk_nat_obj(1138u);
return x_40;
}
else
{
obj* x_41; obj* x_44; obj* x_47; obj* x_48; 
x_41 = lean::cnstr_get(x_37, 0);
lean::inc(x_41);
lean::dec(x_37);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
lean::dec(x_41);
x_47 = lean::mk_nat_obj(16u);
x_48 = l___private_init_lean_parser_token_8__toNatBase(x_44, x_47);
return x_48;
}
}
}
}
}
obj* l_Lean_Parser_number_View_toNat(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_number_View_toNat___main(x_0);
return x_1;
}
}
obj* l_Lean_Parser_number_View_ofNat(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = l_Nat_repr(x_0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
x_5 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* l_Lean_Parser_tryView___at_Lean_Parser_stringLit_Parser___spec__1(obj* x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_Lean_Parser_Syntax_isOfKind___main(x_0, x_1);
if (x_2 == 0)
{
obj* x_4; 
lean::dec(x_1);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_9; obj* x_10; 
x_5 = l_Lean_Parser_stringLit_HasView;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
lean::dec(x_5);
x_9 = lean::apply_1(x_6, x_1);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_9);
return x_10;
}
}
}
obj* l_Lean_Parser_stringLit_Parser___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_2);
lean::inc(x_1);
x_6 = l_Lean_Parser_token(x_1, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; obj* x_21; 
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_set(x_6, 1, lean::box(0));
 x_11 = x_6;
} else {
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_7, 0);
x_14 = lean::cnstr_get(x_7, 1);
x_16 = lean::cnstr_get(x_7, 2);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 lean::cnstr_set(x_7, 2, lean::box(0));
 x_18 = x_7;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_7);
 x_18 = lean::box(0);
}
x_19 = l_Lean_Parser_stringLit;
lean::inc(x_12);
x_21 = l_Lean_Parser_tryView___at_Lean_Parser_stringLit_Parser___spec__1(x_19, x_12);
if (lean::obj_tag(x_21) == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_29; obj* x_33; obj* x_35; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_11);
lean::dec(x_12);
lean::dec(x_18);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_2);
x_26 = lean::box(0);
x_27 = l_String_splitAux___main___closed__1;
lean::inc(x_0);
x_29 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_27, x_0, x_25, x_26, x_1, x_14, x_9);
lean::dec(x_14);
lean::dec(x_1);
lean::dec(x_25);
x_33 = lean::cnstr_get(x_29, 0);
x_35 = lean::cnstr_get(x_29, 1);
if (lean::is_exclusive(x_29)) {
 x_37 = x_29;
} else {
 lean::inc(x_33);
 lean::inc(x_35);
 lean::dec(x_29);
 x_37 = lean::box(0);
}
x_38 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_39 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_33);
x_40 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_39);
x_41 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_40);
x_42 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_41, x_0);
x_43 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_42);
if (lean::is_scalar(x_37)) {
 x_44 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_44 = x_37;
}
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_35);
return x_44;
}
else
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_21);
x_48 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_18)) {
 x_49 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_49 = x_18;
}
lean::cnstr_set(x_49, 0, x_12);
lean::cnstr_set(x_49, 1, x_14);
lean::cnstr_set(x_49, 2, x_48);
x_50 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_49);
x_51 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_52 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_51, x_50);
x_53 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_52, x_0);
x_54 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_53);
if (lean::is_scalar(x_11)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_11;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_9);
return x_55;
}
}
else
{
obj* x_58; obj* x_60; obj* x_61; uint8 x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
lean::dec(x_1);
lean::dec(x_2);
x_58 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_60 = x_6;
} else {
 lean::inc(x_58);
 lean::dec(x_6);
 x_60 = lean::box(0);
}
x_61 = lean::cnstr_get(x_7, 0);
x_63 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_64 = x_7;
} else {
 lean::inc(x_61);
 lean::dec(x_7);
 x_64 = lean::box(0);
}
if (lean::is_scalar(x_64)) {
 x_65 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_65 = x_64;
}
lean::cnstr_set(x_65, 0, x_61);
lean::cnstr_set_scalar(x_65, sizeof(void*)*1, x_63);
x_66 = x_65;
x_67 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_68 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_67, x_66);
x_69 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_68, x_0);
x_70 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_69);
if (lean::is_scalar(x_60)) {
 x_71 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_71 = x_60;
}
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_58);
return x_71;
}
}
}
obj* _init_l_Lean_Parser_stringLit_Parser___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("String");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_stringLit_Parser___rarg___lambda__1), 4, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Parser_stringLit_Parser___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_stringLit_Parser___rarg___closed__1;
x_2 = lean::apply_2(x_0, lean::box(0), x_1);
return x_2;
}
}
obj* l_Lean_Parser_stringLit_Parser(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_stringLit_Parser___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_tryView___at_Lean_Parser_stringLit_Parser___spec__1___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_tryView___at_Lean_Parser_stringLit_Parser___spec__1(x_0, x_1);
lean::dec(x_0);
return x_2;
}
}
obj* l_Lean_Parser_stringLit_Parser___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_stringLit_Parser(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_stringLit_Parser_tokens(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_Lean_Parser_stringLit_Parser_tokens___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_stringLit_Parser_tokens(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_stringLit_Parser_View___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_stringLit_HasView;
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_stringLit_Parser_View___rarg___closed__2() {
_start:
{
obj* x_0; obj* x_1; 
x_0 = l_Lean_Parser_stringLit_HasView;
x_1 = lean::cnstr_get(x_0, 1);
lean::inc(x_1);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_stringLit_Parser_View___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_stringLit_Parser_View___rarg___closed__1;
x_2 = l_Lean_Parser_stringLit_Parser_View___rarg___closed__2;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_stringLit_Parser_View(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_stringLit_Parser_View___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_stringLit_Parser_View___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_stringLit_Parser_View___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_stringLit_Parser_View___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_stringLit_Parser_View(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; 
x_5 = l_Option_getOrElse___main___rarg(x_2, x_4);
x_6 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_0);
lean::cnstr_set(x_6, 2, x_1);
lean::cnstr_set(x_6, 3, x_3);
x_7 = 0;
x_8 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set_scalar(x_8, sizeof(void*)*1, x_7);
x_9 = x_8;
return x_9;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg___boxed), 5, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_stringLit_View_value___spec__2(uint32 x_0, obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_String_OldIterator_hasNext___main(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_8; obj* x_9; 
x_3 = lean::box(0);
x_4 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_5 = l_mjoin___rarg___closed__1;
x_6 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_4, x_5, x_3, x_3, x_1);
lean::dec(x_1);
x_8 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_9 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_8, x_6);
return x_9;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = l_String_OldIterator_curr___main(x_1);
x_11 = x_10 == x_0;
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_21; obj* x_22; 
x_12 = l_Char_quoteCore(x_10);
x_13 = l_Char_HasRepr___closed__1;
x_14 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_16 = lean::string_append(x_14, x_13);
x_17 = lean::box(0);
x_18 = l_mjoin___rarg___closed__1;
x_19 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_16, x_18, x_17, x_17, x_1);
lean::dec(x_1);
x_21 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_19);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_23 = l_String_OldIterator_next___main(x_1);
x_24 = lean::box(0);
x_25 = lean::box_uint32(x_10);
x_26 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_23);
lean::cnstr_set(x_26, 2, x_24);
return x_26;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_any___at_Lean_Parser_stringLit_View_value___spec__5(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_String_OldIterator_hasNext___main(x_0);
if (x_1 == 0)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_2 = lean::box(0);
x_3 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
x_5 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
lean::dec(x_0);
x_7 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_8 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_7, x_5);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = l_String_OldIterator_curr___main(x_0);
x_10 = l_True_Decidable;
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
x_11 = l_Char_quoteCore(x_9);
x_12 = l_Char_HasRepr___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_15 = lean::string_append(x_13, x_12);
x_16 = lean::box(0);
x_17 = l_mjoin___rarg___closed__1;
x_18 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_15, x_17, x_16, x_16, x_0);
lean::dec(x_0);
x_20 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_20, x_18);
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = l_String_OldIterator_next___main(x_0);
x_23 = lean::box(0);
x_24 = lean::box_uint32(x_9);
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_22);
lean::cnstr_set(x_25, 2, x_23);
return x_25;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_View_value___spec__7___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_1);
x_4 = lean::box(0);
x_5 = l_mjoin___rarg___closed__1;
x_6 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_0, x_5, x_3, x_4, x_2);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_View_value___spec__7(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_View_value___spec__7___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_digit___at_Lean_Parser_stringLit_View_value___spec__9(obj* x_0) {
_start:
{
uint8 x_1; 
x_1 = l_String_OldIterator_hasNext___main(x_0);
if (x_1 == 0)
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_7; obj* x_8; 
x_2 = lean::box(0);
x_3 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_4 = l_mjoin___rarg___closed__1;
x_5 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_3, x_4, x_2, x_2, x_0);
lean::dec(x_0);
x_7 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_8 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_7, x_5);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = l_String_OldIterator_curr___main(x_0);
x_10 = l_Char_isDigit(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_20; obj* x_21; 
x_11 = l_Char_quoteCore(x_9);
x_12 = l_Char_HasRepr___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_15 = lean::string_append(x_13, x_12);
x_16 = lean::box(0);
x_17 = l_mjoin___rarg___closed__1;
x_18 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_15, x_17, x_16, x_16, x_0);
lean::dec(x_0);
x_20 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_20, x_18);
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_22 = l_String_OldIterator_next___main(x_0);
x_23 = lean::box(0);
x_24 = lean::box_uint32(x_9);
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_22);
lean::cnstr_set(x_25, 2, x_23);
return x_25;
}
}
}
}
obj* l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_View_value___spec__8(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; uint8 x_3; obj* x_6; 
lean::inc(x_0);
x_6 = l_Lean_Parser_MonadParsec_digit___at_Lean_Parser_stringLit_View_value___spec__9(x_0);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_9; obj* x_11; obj* x_13; uint32 x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_19; obj* x_20; obj* x_21; 
x_7 = lean::cnstr_get(x_6, 0);
x_9 = lean::cnstr_get(x_6, 1);
x_11 = lean::cnstr_get(x_6, 2);
if (lean::is_exclusive(x_6)) {
 x_13 = x_6;
} else {
 lean::inc(x_7);
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_6);
 x_13 = lean::box(0);
}
x_14 = lean::unbox_uint32(x_7);
x_15 = lean::uint32_to_nat(x_14);
x_16 = l_String_foldlAux___main___at_String_toNat___spec__1___closed__1;
x_17 = lean::nat_sub(x_15, x_16);
lean::dec(x_15);
x_19 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_13)) {
 x_20 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_20 = x_13;
}
lean::cnstr_set(x_20, 0, x_17);
lean::cnstr_set(x_20, 1, x_9);
lean::cnstr_set(x_20, 2, x_19);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_20);
if (lean::obj_tag(x_21) == 0)
{
obj* x_23; obj* x_24; 
lean::dec(x_0);
x_23 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5___closed__1;
x_24 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_21, x_23);
return x_24;
}
else
{
obj* x_25; uint8 x_27; 
x_25 = lean::cnstr_get(x_21, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
x_1 = x_21;
x_2 = x_25;
x_3 = x_27;
goto lbl_4;
}
}
else
{
obj* x_28; uint8 x_30; obj* x_31; obj* x_33; obj* x_34; 
x_28 = lean::cnstr_get(x_6, 0);
x_30 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 x_31 = x_6;
} else {
 lean::inc(x_28);
 lean::dec(x_6);
 x_31 = lean::box(0);
}
lean::inc(x_28);
if (lean::is_scalar(x_31)) {
 x_33 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_33 = x_31;
}
lean::cnstr_set(x_33, 0, x_28);
lean::cnstr_set_scalar(x_33, sizeof(void*)*1, x_30);
x_34 = x_33;
x_1 = x_34;
x_2 = x_28;
x_3 = x_30;
goto lbl_4;
}
lbl_4:
{
obj* x_35; obj* x_36; uint8 x_37; 
if (x_3 == 0)
{
obj* x_40; uint8 x_42; 
lean::dec(x_1);
x_42 = l_String_OldIterator_hasNext___main(x_0);
if (x_42 == 0)
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_43 = lean::box(0);
x_44 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_45 = l_mjoin___rarg___closed__1;
x_46 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_44, x_45, x_43, x_43, x_0);
x_40 = x_46;
goto lbl_41;
}
else
{
uint32 x_47; uint32 x_48; uint8 x_49; 
x_47 = l_String_OldIterator_curr___main(x_0);
x_48 = 97;
x_49 = x_48 <= x_47;
if (x_49 == 0)
{
obj* x_50; obj* x_51; obj* x_52; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_50 = l_Char_quoteCore(x_47);
x_51 = l_Char_HasRepr___closed__1;
x_52 = lean::string_append(x_51, x_50);
lean::dec(x_50);
x_54 = lean::string_append(x_52, x_51);
x_55 = lean::box(0);
x_56 = l_mjoin___rarg___closed__1;
x_57 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_54, x_56, x_55, x_55, x_0);
x_40 = x_57;
goto lbl_41;
}
else
{
uint32 x_58; uint8 x_59; 
x_58 = 102;
x_59 = x_47 <= x_58;
if (x_59 == 0)
{
obj* x_60; obj* x_61; obj* x_62; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_60 = l_Char_quoteCore(x_47);
x_61 = l_Char_HasRepr___closed__1;
x_62 = lean::string_append(x_61, x_60);
lean::dec(x_60);
x_64 = lean::string_append(x_62, x_61);
x_65 = lean::box(0);
x_66 = l_mjoin___rarg___closed__1;
x_67 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_64, x_66, x_65, x_65, x_0);
x_40 = x_67;
goto lbl_41;
}
else
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
lean::inc(x_0);
x_69 = l_String_OldIterator_next___main(x_0);
x_70 = lean::box(0);
x_71 = lean::box_uint32(x_47);
x_72 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_69);
lean::cnstr_set(x_72, 2, x_70);
x_40 = x_72;
goto lbl_41;
}
}
}
lbl_41:
{
obj* x_73; obj* x_74; 
x_73 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_74 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_73, x_40);
if (lean::obj_tag(x_74) == 0)
{
obj* x_75; obj* x_77; obj* x_79; obj* x_81; uint32 x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_87; obj* x_88; obj* x_90; obj* x_91; 
x_75 = lean::cnstr_get(x_74, 0);
x_77 = lean::cnstr_get(x_74, 1);
x_79 = lean::cnstr_get(x_74, 2);
if (lean::is_exclusive(x_74)) {
 x_81 = x_74;
} else {
 lean::inc(x_75);
 lean::inc(x_77);
 lean::inc(x_79);
 lean::dec(x_74);
 x_81 = lean::box(0);
}
x_82 = lean::unbox_uint32(x_75);
x_83 = lean::uint32_to_nat(x_82);
x_84 = l_Lean_Parser_parseHexDigit___rarg___lambda__3___closed__1;
x_85 = lean::nat_sub(x_83, x_84);
lean::dec(x_83);
x_87 = lean::mk_nat_obj(10u);
x_88 = lean::nat_add(x_87, x_85);
lean::dec(x_85);
if (lean::is_scalar(x_81)) {
 x_90 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_90 = x_81;
}
lean::cnstr_set(x_90, 0, x_88);
lean::cnstr_set(x_90, 1, x_77);
lean::cnstr_set(x_90, 2, x_73);
x_91 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_79, x_90);
if (lean::obj_tag(x_91) == 0)
{
obj* x_93; obj* x_94; obj* x_95; 
lean::dec(x_0);
x_93 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_2, x_91);
x_94 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5___closed__1;
x_95 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_93, x_94);
return x_95;
}
else
{
obj* x_96; uint8 x_98; 
x_96 = lean::cnstr_get(x_91, 0);
lean::inc(x_96);
x_98 = lean::cnstr_get_scalar<uint8>(x_91, sizeof(void*)*1);
x_35 = x_91;
x_36 = x_96;
x_37 = x_98;
goto lbl_38;
}
}
else
{
obj* x_99; uint8 x_101; obj* x_102; obj* x_104; obj* x_105; 
x_99 = lean::cnstr_get(x_74, 0);
x_101 = lean::cnstr_get_scalar<uint8>(x_74, sizeof(void*)*1);
if (lean::is_exclusive(x_74)) {
 x_102 = x_74;
} else {
 lean::inc(x_99);
 lean::dec(x_74);
 x_102 = lean::box(0);
}
lean::inc(x_99);
if (lean::is_scalar(x_102)) {
 x_104 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_104 = x_102;
}
lean::cnstr_set(x_104, 0, x_99);
lean::cnstr_set_scalar(x_104, sizeof(void*)*1, x_101);
x_105 = x_104;
x_35 = x_105;
x_36 = x_99;
x_37 = x_101;
goto lbl_38;
}
}
}
else
{
obj* x_108; obj* x_109; 
lean::dec(x_0);
lean::dec(x_2);
x_108 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5___closed__1;
x_109 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_1, x_108);
return x_109;
}
lbl_38:
{
if (x_37 == 0)
{
obj* x_111; uint8 x_113; 
lean::dec(x_35);
x_113 = l_String_OldIterator_hasNext___main(x_0);
if (x_113 == 0)
{
obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
x_114 = lean::box(0);
x_115 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_116 = l_mjoin___rarg___closed__1;
x_117 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_115, x_116, x_114, x_114, x_0);
lean::dec(x_0);
x_111 = x_117;
goto lbl_112;
}
else
{
uint32 x_119; uint32 x_120; uint8 x_121; 
x_119 = l_String_OldIterator_curr___main(x_0);
x_120 = 65;
x_121 = x_120 <= x_119;
if (x_121 == 0)
{
obj* x_122; obj* x_123; obj* x_124; obj* x_126; obj* x_127; obj* x_128; obj* x_129; 
x_122 = l_Char_quoteCore(x_119);
x_123 = l_Char_HasRepr___closed__1;
x_124 = lean::string_append(x_123, x_122);
lean::dec(x_122);
x_126 = lean::string_append(x_124, x_123);
x_127 = lean::box(0);
x_128 = l_mjoin___rarg___closed__1;
x_129 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_126, x_128, x_127, x_127, x_0);
lean::dec(x_0);
x_111 = x_129;
goto lbl_112;
}
else
{
uint32 x_131; uint8 x_132; 
x_131 = 70;
x_132 = x_119 <= x_131;
if (x_132 == 0)
{
obj* x_133; obj* x_134; obj* x_135; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
x_133 = l_Char_quoteCore(x_119);
x_134 = l_Char_HasRepr___closed__1;
x_135 = lean::string_append(x_134, x_133);
lean::dec(x_133);
x_137 = lean::string_append(x_135, x_134);
x_138 = lean::box(0);
x_139 = l_mjoin___rarg___closed__1;
x_140 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_137, x_139, x_138, x_138, x_0);
lean::dec(x_0);
x_111 = x_140;
goto lbl_112;
}
else
{
obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
x_142 = l_String_OldIterator_next___main(x_0);
x_143 = lean::box(0);
x_144 = lean::box_uint32(x_119);
x_145 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_145, 0, x_144);
lean::cnstr_set(x_145, 1, x_142);
lean::cnstr_set(x_145, 2, x_143);
x_111 = x_145;
goto lbl_112;
}
}
}
lbl_112:
{
obj* x_146; obj* x_147; 
x_146 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_147 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_146, x_111);
if (lean::obj_tag(x_147) == 0)
{
obj* x_148; obj* x_150; obj* x_152; obj* x_154; uint32 x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_160; obj* x_161; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
x_148 = lean::cnstr_get(x_147, 0);
x_150 = lean::cnstr_get(x_147, 1);
x_152 = lean::cnstr_get(x_147, 2);
if (lean::is_exclusive(x_147)) {
 x_154 = x_147;
} else {
 lean::inc(x_148);
 lean::inc(x_150);
 lean::inc(x_152);
 lean::dec(x_147);
 x_154 = lean::box(0);
}
x_155 = lean::unbox_uint32(x_148);
x_156 = lean::uint32_to_nat(x_155);
x_157 = l_Lean_Parser_parseHexDigit___rarg___lambda__5___closed__1;
x_158 = lean::nat_sub(x_156, x_157);
lean::dec(x_156);
x_160 = lean::mk_nat_obj(10u);
x_161 = lean::nat_add(x_160, x_158);
lean::dec(x_158);
if (lean::is_scalar(x_154)) {
 x_163 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_163 = x_154;
}
lean::cnstr_set(x_163, 0, x_161);
lean::cnstr_set(x_163, 1, x_150);
lean::cnstr_set(x_163, 2, x_146);
x_164 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_152, x_163);
x_165 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_36, x_164);
x_166 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_2, x_165);
x_167 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5___closed__1;
x_168 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_166, x_167);
return x_168;
}
else
{
obj* x_169; uint8 x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; 
x_169 = lean::cnstr_get(x_147, 0);
x_171 = lean::cnstr_get_scalar<uint8>(x_147, sizeof(void*)*1);
if (lean::is_exclusive(x_147)) {
 x_172 = x_147;
} else {
 lean::inc(x_169);
 lean::dec(x_147);
 x_172 = lean::box(0);
}
if (lean::is_scalar(x_172)) {
 x_173 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_173 = x_172;
}
lean::cnstr_set(x_173, 0, x_169);
lean::cnstr_set_scalar(x_173, sizeof(void*)*1, x_171);
x_174 = x_173;
x_175 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_36, x_174);
x_176 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_2, x_175);
x_177 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5___closed__1;
x_178 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_176, x_177);
return x_178;
}
}
}
else
{
obj* x_181; obj* x_182; obj* x_183; 
lean::dec(x_0);
lean::dec(x_36);
x_181 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_2, x_35);
x_182 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5___closed__1;
x_183 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_181, x_182);
return x_183;
}
}
}
}
}
obj* l_Lean_Parser_parseQuotedChar___at_Lean_Parser_stringLit_View_value___spec__6(obj* x_0) {
_start:
{
obj* x_2; 
lean::inc(x_0);
x_2 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_stringLit_View_value___spec__5(x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_7; obj* x_9; uint32 x_10; uint32 x_11; uint8 x_12; 
x_3 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_7 = lean::cnstr_get(x_2, 2);
if (lean::is_exclusive(x_2)) {
 lean::cnstr_set(x_2, 0, lean::box(0));
 lean::cnstr_set(x_2, 1, lean::box(0));
 lean::cnstr_set(x_2, 2, lean::box(0));
 x_9 = x_2;
} else {
 lean::inc(x_3);
 lean::inc(x_5);
 lean::inc(x_7);
 lean::dec(x_2);
 x_9 = lean::box(0);
}
x_10 = 92;
x_11 = lean::unbox_uint32(x_3);
x_12 = x_11 == x_10;
if (x_12 == 0)
{
uint32 x_13; uint8 x_14; 
x_13 = 34;
x_14 = x_11 == x_13;
if (x_14 == 0)
{
uint32 x_15; uint8 x_16; 
x_15 = 39;
x_16 = x_11 == x_15;
if (x_16 == 0)
{
uint32 x_17; uint8 x_18; 
x_17 = 110;
x_18 = x_11 == x_17;
if (x_18 == 0)
{
uint32 x_19; uint8 x_20; 
x_19 = 116;
x_20 = x_11 == x_19;
if (x_20 == 0)
{
uint32 x_22; uint8 x_23; 
lean::dec(x_9);
x_22 = 120;
x_23 = x_11 == x_22;
if (x_23 == 0)
{
uint32 x_24; uint8 x_25; 
x_24 = 117;
x_25 = x_11 == x_24;
if (x_25 == 0)
{
obj* x_26; obj* x_27; obj* x_29; obj* x_30; obj* x_31; 
x_26 = l_Lean_Parser_parseQuotedChar___rarg___lambda__7___closed__1;
x_27 = l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_View_value___spec__7___rarg(x_26, x_0, x_5);
lean::dec(x_5);
x_29 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_7, x_27);
x_30 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_31 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_30, x_29);
return x_31;
}
else
{
obj* x_33; 
lean::dec(x_0);
x_33 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_View_value___spec__8(x_5);
if (lean::obj_tag(x_33) == 0)
{
obj* x_34; obj* x_36; obj* x_38; obj* x_41; 
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
x_36 = lean::cnstr_get(x_33, 1);
lean::inc(x_36);
x_38 = lean::cnstr_get(x_33, 2);
lean::inc(x_38);
lean::dec(x_33);
x_41 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_View_value___spec__8(x_36);
if (lean::obj_tag(x_41) == 0)
{
obj* x_42; obj* x_44; obj* x_46; obj* x_49; 
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
x_46 = lean::cnstr_get(x_41, 2);
lean::inc(x_46);
lean::dec(x_41);
x_49 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_View_value___spec__8(x_44);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; obj* x_52; obj* x_54; obj* x_57; 
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_52 = lean::cnstr_get(x_49, 1);
lean::inc(x_52);
x_54 = lean::cnstr_get(x_49, 2);
lean::inc(x_54);
lean::dec(x_49);
x_57 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_View_value___spec__8(x_52);
if (lean::obj_tag(x_57) == 0)
{
obj* x_58; obj* x_60; obj* x_62; obj* x_64; obj* x_65; obj* x_66; obj* x_68; obj* x_71; obj* x_73; obj* x_76; obj* x_78; uint32 x_81; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
x_58 = lean::cnstr_get(x_57, 0);
x_60 = lean::cnstr_get(x_57, 1);
x_62 = lean::cnstr_get(x_57, 2);
if (lean::is_exclusive(x_57)) {
 x_64 = x_57;
} else {
 lean::inc(x_58);
 lean::inc(x_60);
 lean::inc(x_62);
 lean::dec(x_57);
 x_64 = lean::box(0);
}
x_65 = lean::mk_nat_obj(16u);
x_66 = lean::nat_mul(x_65, x_34);
lean::dec(x_34);
x_68 = lean::nat_add(x_66, x_42);
lean::dec(x_42);
lean::dec(x_66);
x_71 = lean::nat_mul(x_65, x_68);
lean::dec(x_68);
x_73 = lean::nat_add(x_71, x_50);
lean::dec(x_50);
lean::dec(x_71);
x_76 = lean::nat_mul(x_65, x_73);
lean::dec(x_73);
x_78 = lean::nat_add(x_76, x_58);
lean::dec(x_58);
lean::dec(x_76);
x_81 = l_Char_ofNat(x_78);
lean::dec(x_78);
x_83 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_84 = lean::box_uint32(x_81);
if (lean::is_scalar(x_64)) {
 x_85 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_85 = x_64;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_60);
lean::cnstr_set(x_85, 2, x_83);
x_86 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_62, x_85);
x_87 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_54, x_86);
x_88 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_46, x_87);
x_89 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_88);
x_90 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_7, x_89);
x_91 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_83, x_90);
return x_91;
}
else
{
obj* x_95; uint8 x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
lean::dec(x_42);
lean::dec(x_50);
lean::dec(x_34);
x_95 = lean::cnstr_get(x_57, 0);
x_97 = lean::cnstr_get_scalar<uint8>(x_57, sizeof(void*)*1);
if (lean::is_exclusive(x_57)) {
 x_98 = x_57;
} else {
 lean::inc(x_95);
 lean::dec(x_57);
 x_98 = lean::box(0);
}
if (lean::is_scalar(x_98)) {
 x_99 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_99 = x_98;
}
lean::cnstr_set(x_99, 0, x_95);
lean::cnstr_set_scalar(x_99, sizeof(void*)*1, x_97);
x_100 = x_99;
x_101 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_54, x_100);
x_102 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_46, x_101);
x_103 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_102);
x_104 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_7, x_103);
x_105 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_106 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_105, x_104);
return x_106;
}
}
else
{
obj* x_109; uint8 x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
lean::dec(x_42);
lean::dec(x_34);
x_109 = lean::cnstr_get(x_49, 0);
x_111 = lean::cnstr_get_scalar<uint8>(x_49, sizeof(void*)*1);
if (lean::is_exclusive(x_49)) {
 x_112 = x_49;
} else {
 lean::inc(x_109);
 lean::dec(x_49);
 x_112 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_113 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_113 = x_112;
}
lean::cnstr_set(x_113, 0, x_109);
lean::cnstr_set_scalar(x_113, sizeof(void*)*1, x_111);
x_114 = x_113;
x_115 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_46, x_114);
x_116 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_115);
x_117 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_7, x_116);
x_118 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_119 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_118, x_117);
return x_119;
}
}
else
{
obj* x_121; uint8 x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
lean::dec(x_34);
x_121 = lean::cnstr_get(x_41, 0);
x_123 = lean::cnstr_get_scalar<uint8>(x_41, sizeof(void*)*1);
if (lean::is_exclusive(x_41)) {
 x_124 = x_41;
} else {
 lean::inc(x_121);
 lean::dec(x_41);
 x_124 = lean::box(0);
}
if (lean::is_scalar(x_124)) {
 x_125 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_125 = x_124;
}
lean::cnstr_set(x_125, 0, x_121);
lean::cnstr_set_scalar(x_125, sizeof(void*)*1, x_123);
x_126 = x_125;
x_127 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_126);
x_128 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_7, x_127);
x_129 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_130 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_129, x_128);
return x_130;
}
}
else
{
obj* x_131; uint8 x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; 
x_131 = lean::cnstr_get(x_33, 0);
x_133 = lean::cnstr_get_scalar<uint8>(x_33, sizeof(void*)*1);
if (lean::is_exclusive(x_33)) {
 x_134 = x_33;
} else {
 lean::inc(x_131);
 lean::dec(x_33);
 x_134 = lean::box(0);
}
if (lean::is_scalar(x_134)) {
 x_135 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_135 = x_134;
}
lean::cnstr_set(x_135, 0, x_131);
lean::cnstr_set_scalar(x_135, sizeof(void*)*1, x_133);
x_136 = x_135;
x_137 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_7, x_136);
x_138 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_139 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_138, x_137);
return x_139;
}
}
}
else
{
obj* x_141; 
lean::dec(x_0);
x_141 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_View_value___spec__8(x_5);
if (lean::obj_tag(x_141) == 0)
{
obj* x_142; obj* x_144; obj* x_146; obj* x_149; 
x_142 = lean::cnstr_get(x_141, 0);
lean::inc(x_142);
x_144 = lean::cnstr_get(x_141, 1);
lean::inc(x_144);
x_146 = lean::cnstr_get(x_141, 2);
lean::inc(x_146);
lean::dec(x_141);
x_149 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_View_value___spec__8(x_144);
if (lean::obj_tag(x_149) == 0)
{
obj* x_150; obj* x_152; obj* x_154; obj* x_156; obj* x_157; obj* x_158; obj* x_160; uint32 x_163; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; 
x_150 = lean::cnstr_get(x_149, 0);
x_152 = lean::cnstr_get(x_149, 1);
x_154 = lean::cnstr_get(x_149, 2);
if (lean::is_exclusive(x_149)) {
 x_156 = x_149;
} else {
 lean::inc(x_150);
 lean::inc(x_152);
 lean::inc(x_154);
 lean::dec(x_149);
 x_156 = lean::box(0);
}
x_157 = lean::mk_nat_obj(16u);
x_158 = lean::nat_mul(x_157, x_142);
lean::dec(x_142);
x_160 = lean::nat_add(x_158, x_150);
lean::dec(x_150);
lean::dec(x_158);
x_163 = l_Char_ofNat(x_160);
lean::dec(x_160);
x_165 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_166 = lean::box_uint32(x_163);
if (lean::is_scalar(x_156)) {
 x_167 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_167 = x_156;
}
lean::cnstr_set(x_167, 0, x_166);
lean::cnstr_set(x_167, 1, x_152);
lean::cnstr_set(x_167, 2, x_165);
x_168 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_154, x_167);
x_169 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_146, x_168);
x_170 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_7, x_169);
x_171 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_165, x_170);
return x_171;
}
else
{
obj* x_173; uint8 x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; 
lean::dec(x_142);
x_173 = lean::cnstr_get(x_149, 0);
x_175 = lean::cnstr_get_scalar<uint8>(x_149, sizeof(void*)*1);
if (lean::is_exclusive(x_149)) {
 x_176 = x_149;
} else {
 lean::inc(x_173);
 lean::dec(x_149);
 x_176 = lean::box(0);
}
if (lean::is_scalar(x_176)) {
 x_177 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_177 = x_176;
}
lean::cnstr_set(x_177, 0, x_173);
lean::cnstr_set_scalar(x_177, sizeof(void*)*1, x_175);
x_178 = x_177;
x_179 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_146, x_178);
x_180 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_7, x_179);
x_181 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_182 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_181, x_180);
return x_182;
}
}
else
{
obj* x_183; uint8 x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; 
x_183 = lean::cnstr_get(x_141, 0);
x_185 = lean::cnstr_get_scalar<uint8>(x_141, sizeof(void*)*1);
if (lean::is_exclusive(x_141)) {
 x_186 = x_141;
} else {
 lean::inc(x_183);
 lean::dec(x_141);
 x_186 = lean::box(0);
}
if (lean::is_scalar(x_186)) {
 x_187 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_187 = x_186;
}
lean::cnstr_set(x_187, 0, x_183);
lean::cnstr_set_scalar(x_187, sizeof(void*)*1, x_185);
x_188 = x_187;
x_189 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_7, x_188);
x_190 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_191 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_190, x_189);
return x_191;
}
}
}
else
{
uint32 x_193; obj* x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; 
lean::dec(x_0);
x_193 = 9;
x_194 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_195 = lean::box_uint32(x_193);
if (lean::is_scalar(x_9)) {
 x_196 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_196 = x_9;
}
lean::cnstr_set(x_196, 0, x_195);
lean::cnstr_set(x_196, 1, x_5);
lean::cnstr_set(x_196, 2, x_194);
x_197 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_7, x_196);
x_198 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_194, x_197);
return x_198;
}
}
else
{
uint32 x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; 
lean::dec(x_0);
x_200 = 10;
x_201 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_202 = lean::box_uint32(x_200);
if (lean::is_scalar(x_9)) {
 x_203 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_203 = x_9;
}
lean::cnstr_set(x_203, 0, x_202);
lean::cnstr_set(x_203, 1, x_5);
lean::cnstr_set(x_203, 2, x_201);
x_204 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_7, x_203);
x_205 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_201, x_204);
return x_205;
}
}
else
{
obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; 
lean::dec(x_0);
x_207 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_208 = lean::box_uint32(x_15);
if (lean::is_scalar(x_9)) {
 x_209 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_209 = x_9;
}
lean::cnstr_set(x_209, 0, x_208);
lean::cnstr_set(x_209, 1, x_5);
lean::cnstr_set(x_209, 2, x_207);
x_210 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_7, x_209);
x_211 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_207, x_210);
return x_211;
}
}
else
{
obj* x_213; obj* x_214; obj* x_215; obj* x_216; obj* x_217; 
lean::dec(x_0);
x_213 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_214 = lean::box_uint32(x_13);
if (lean::is_scalar(x_9)) {
 x_215 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_215 = x_9;
}
lean::cnstr_set(x_215, 0, x_214);
lean::cnstr_set(x_215, 1, x_5);
lean::cnstr_set(x_215, 2, x_213);
x_216 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_7, x_215);
x_217 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_213, x_216);
return x_217;
}
}
else
{
obj* x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; 
lean::dec(x_0);
x_219 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_220 = lean::box_uint32(x_10);
if (lean::is_scalar(x_9)) {
 x_221 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_221 = x_9;
}
lean::cnstr_set(x_221, 0, x_220);
lean::cnstr_set(x_221, 1, x_5);
lean::cnstr_set(x_221, 2, x_219);
x_222 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_7, x_221);
x_223 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_219, x_222);
return x_223;
}
}
else
{
obj* x_225; uint8 x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_232; 
lean::dec(x_0);
x_225 = lean::cnstr_get(x_2, 0);
x_227 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_228 = x_2;
} else {
 lean::inc(x_225);
 lean::dec(x_2);
 x_228 = lean::box(0);
}
if (lean::is_scalar(x_228)) {
 x_229 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_229 = x_228;
}
lean::cnstr_set(x_229, 0, x_225);
lean::cnstr_set_scalar(x_229, sizeof(void*)*1, x_227);
x_230 = x_229;
x_231 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_232 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_231, x_230);
return x_232;
}
}
}
obj* l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_View_value___spec__4(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; 
x_3 = lean::mk_nat_obj(0u);
x_4 = lean::nat_dec_eq(x_0, x_3);
if (x_4 == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_stringLit_View_value___spec__5(x_2);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_8; obj* x_10; obj* x_12; obj* x_13; obj* x_14; uint32 x_15; uint32 x_16; uint8 x_17; 
x_6 = lean::cnstr_get(x_5, 0);
x_8 = lean::cnstr_get(x_5, 1);
x_10 = lean::cnstr_get(x_5, 2);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_set(x_5, 0, lean::box(0));
 lean::cnstr_set(x_5, 1, lean::box(0));
 lean::cnstr_set(x_5, 2, lean::box(0));
 x_12 = x_5;
} else {
 lean::inc(x_6);
 lean::inc(x_8);
 lean::inc(x_10);
 lean::dec(x_5);
 x_12 = lean::box(0);
}
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_sub(x_0, x_13);
x_15 = 92;
x_16 = lean::unbox_uint32(x_6);
x_17 = x_16 == x_15;
if (x_17 == 0)
{
uint32 x_18; uint8 x_19; 
x_18 = 34;
x_19 = x_16 == x_18;
if (x_19 == 0)
{
obj* x_21; obj* x_22; obj* x_24; 
lean::dec(x_12);
x_21 = lean::string_push(x_1, x_16);
x_22 = l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_View_value___spec__4(x_14, x_21, x_8);
lean::dec(x_14);
x_24 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_10, x_22);
return x_24;
}
else
{
obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_14);
x_26 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_12)) {
 x_27 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_27 = x_12;
}
lean::cnstr_set(x_27, 0, x_1);
lean::cnstr_set(x_27, 1, x_8);
lean::cnstr_set(x_27, 2, x_26);
x_28 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_10, x_27);
return x_28;
}
}
else
{
obj* x_30; 
lean::dec(x_12);
x_30 = l_Lean_Parser_parseQuotedChar___at_Lean_Parser_stringLit_View_value___spec__6(x_8);
if (lean::obj_tag(x_30) == 0)
{
obj* x_31; obj* x_33; obj* x_35; uint32 x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_43; 
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_33 = lean::cnstr_get(x_30, 1);
lean::inc(x_33);
x_35 = lean::cnstr_get(x_30, 2);
lean::inc(x_35);
lean::dec(x_30);
x_38 = lean::unbox_uint32(x_31);
x_39 = lean::string_push(x_1, x_38);
x_40 = l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_View_value___spec__4(x_14, x_39, x_33);
lean::dec(x_14);
x_42 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_35, x_40);
x_43 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_10, x_42);
return x_43;
}
else
{
obj* x_46; uint8 x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
lean::dec(x_1);
lean::dec(x_14);
x_46 = lean::cnstr_get(x_30, 0);
x_48 = lean::cnstr_get_scalar<uint8>(x_30, sizeof(void*)*1);
if (lean::is_exclusive(x_30)) {
 x_49 = x_30;
} else {
 lean::inc(x_46);
 lean::dec(x_30);
 x_49 = lean::box(0);
}
if (lean::is_scalar(x_49)) {
 x_50 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_50 = x_49;
}
lean::cnstr_set(x_50, 0, x_46);
lean::cnstr_set_scalar(x_50, sizeof(void*)*1, x_48);
x_51 = x_50;
x_52 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_10, x_51);
return x_52;
}
}
}
else
{
obj* x_54; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_1);
x_54 = lean::cnstr_get(x_5, 0);
x_56 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 x_57 = x_5;
} else {
 lean::inc(x_54);
 lean::dec(x_5);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_54);
lean::cnstr_set_scalar(x_58, sizeof(void*)*1, x_56);
x_59 = x_58;
return x_59;
}
}
else
{
uint32 x_60; obj* x_61; 
x_60 = 34;
x_61 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_stringLit_View_value___spec__2(x_60, x_2);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_64; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_62 = lean::cnstr_get(x_61, 1);
x_64 = lean::cnstr_get(x_61, 2);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 x_66 = x_61;
} else {
 lean::inc(x_62);
 lean::inc(x_64);
 lean::dec(x_61);
 x_66 = lean::box(0);
}
x_67 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_66)) {
 x_68 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_68 = x_66;
}
lean::cnstr_set(x_68, 0, x_1);
lean::cnstr_set(x_68, 1, x_62);
lean::cnstr_set(x_68, 2, x_67);
x_69 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_64, x_68);
return x_69;
}
else
{
obj* x_71; uint8 x_73; obj* x_74; obj* x_75; obj* x_76; 
lean::dec(x_1);
x_71 = lean::cnstr_get(x_61, 0);
x_73 = lean::cnstr_get_scalar<uint8>(x_61, sizeof(void*)*1);
if (lean::is_exclusive(x_61)) {
 x_74 = x_61;
} else {
 lean::inc(x_71);
 lean::dec(x_61);
 x_74 = lean::box(0);
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_71);
lean::cnstr_set_scalar(x_75, sizeof(void*)*1, x_73);
x_76 = x_75;
return x_76;
}
}
}
}
obj* l_Lean_Parser_parseStringLiteral___at_Lean_Parser_stringLit_View_value___spec__1(obj* x_0) {
_start:
{
uint32 x_1; obj* x_2; 
x_1 = 34;
x_2 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_stringLit_View_value___spec__2(x_1, x_0);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; obj* x_5; obj* x_8; obj* x_9; obj* x_10; obj* x_12; obj* x_13; obj* x_14; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
x_5 = lean::cnstr_get(x_2, 2);
lean::inc(x_5);
lean::dec(x_2);
x_8 = l_String_OldIterator_remaining___main(x_3);
x_9 = l_String_splitAux___main___closed__1;
x_10 = l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_View_value___spec__4(x_8, x_9, x_3);
lean::dec(x_8);
x_12 = l_Lean_Parser_finishCommentBlock___closed__2;
x_13 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_10);
x_14 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_5, x_13);
return x_14;
}
else
{
obj* x_15; uint8 x_17; obj* x_18; obj* x_19; obj* x_20; 
x_15 = lean::cnstr_get(x_2, 0);
x_17 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
if (lean::is_exclusive(x_2)) {
 x_18 = x_2;
} else {
 lean::inc(x_15);
 lean::dec(x_2);
 x_18 = lean::box(0);
}
if (lean::is_scalar(x_18)) {
 x_19 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_19 = x_18;
}
lean::cnstr_set(x_19, 0, x_15);
lean::cnstr_set_scalar(x_19, sizeof(void*)*1, x_17);
x_20 = x_19;
return x_20;
}
}
}
obj* _init_l_Lean_Parser_stringLit_View_value___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseStringLiteral___at_Lean_Parser_stringLit_View_value___spec__1), 1, 0);
return x_0;
}
}
obj* l_Lean_Parser_stringLit_View_value(obj* x_0) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_1; 
x_1 = lean::box(0);
return x_1;
}
else
{
obj* x_2; obj* x_4; obj* x_5; obj* x_8; obj* x_9; obj* x_10; 
x_2 = lean::cnstr_get(x_0, 0);
if (lean::is_exclusive(x_0)) {
 lean::cnstr_set(x_0, 0, lean::box(0));
 x_4 = x_0;
} else {
 lean::inc(x_2);
 lean::dec(x_0);
 x_4 = lean::box(0);
}
x_5 = lean::cnstr_get(x_2, 1);
lean::inc(x_5);
lean::dec(x_2);
x_8 = l_Lean_Parser_stringLit_View_value___closed__1;
x_9 = l_String_splitAux___main___closed__1;
x_10 = l_Lean_Parser_ParsecT_run___at_Lean_Parser_Parsec_parse___spec__1___rarg(x_8, x_5, x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_13; 
lean::dec(x_10);
lean::dec(x_4);
x_13 = lean::box(0);
return x_13;
}
else
{
obj* x_14; obj* x_17; 
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
lean::dec(x_10);
if (lean::is_scalar(x_4)) {
 x_17 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_17 = x_4;
}
lean::cnstr_set(x_17, 0, x_14);
return x_17;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_stringLit_View_value___spec__2___boxed(obj* x_0, obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = lean::unbox_uint32(x_0);
x_3 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_stringLit_View_value___spec__2(x_2, x_1);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_View_value___spec__7___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_View_value___spec__7___rarg(x_0, x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_View_value___spec__7___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_View_value___spec__7(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_View_value___spec__4___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_View_value___spec__4(x_0, x_1, x_2);
lean::dec(x_0);
return x_3;
}
}
obj* l_Lean_Parser_ident_Parser___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_2);
lean::inc(x_1);
x_6 = l_Lean_Parser_token(x_1, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; 
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_set(x_6, 1, lean::box(0));
 x_11 = x_6;
} else {
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_7, 0);
x_14 = lean::cnstr_get(x_7, 1);
x_16 = lean::cnstr_get(x_7, 2);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 lean::cnstr_set(x_7, 2, lean::box(0));
 x_18 = x_7;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_7);
 x_18 = lean::box(0);
}
switch (lean::obj_tag(x_12)) {
case 1:
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
lean::dec(x_1);
lean::dec(x_2);
x_23 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_18)) {
 x_24 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_24 = x_18;
}
lean::cnstr_set(x_24, 0, x_12);
lean::cnstr_set(x_24, 1, x_14);
lean::cnstr_set(x_24, 2, x_23);
x_25 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_24);
x_26 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_23, x_25);
x_27 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_26, x_0);
x_28 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_27);
if (lean::is_scalar(x_11)) {
 x_29 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_29 = x_11;
}
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_9);
return x_29;
}
case 3:
{
obj* x_32; 
lean::dec(x_11);
lean::dec(x_18);
x_32 = lean::box(0);
x_19 = x_32;
goto lbl_20;
}
default:
{
obj* x_36; 
lean::dec(x_11);
lean::dec(x_12);
lean::dec(x_18);
x_36 = lean::box(0);
x_19 = x_36;
goto lbl_20;
}
}
lbl_20:
{
obj* x_38; obj* x_39; obj* x_40; obj* x_42; obj* x_46; obj* x_48; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::dec(x_19);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_2);
x_39 = lean::box(0);
x_40 = l_String_splitAux___main___closed__1;
lean::inc(x_0);
x_42 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_40, x_0, x_38, x_39, x_1, x_14, x_9);
lean::dec(x_14);
lean::dec(x_1);
lean::dec(x_38);
x_46 = lean::cnstr_get(x_42, 0);
x_48 = lean::cnstr_get(x_42, 1);
if (lean::is_exclusive(x_42)) {
 x_50 = x_42;
} else {
 lean::inc(x_46);
 lean::inc(x_48);
 lean::dec(x_42);
 x_50 = lean::box(0);
}
x_51 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_46);
x_52 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_51);
x_54 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_53, x_0);
x_55 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_54);
if (lean::is_scalar(x_50)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_50;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_48);
return x_56;
}
}
else
{
obj* x_59; obj* x_61; obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
lean::dec(x_1);
lean::dec(x_2);
x_59 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_61 = x_6;
} else {
 lean::inc(x_59);
 lean::dec(x_6);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_7, 0);
x_64 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_65 = x_7;
} else {
 lean::inc(x_62);
 lean::dec(x_7);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_62);
lean::cnstr_set_scalar(x_66, sizeof(void*)*1, x_64);
x_67 = x_66;
x_68 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_69 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_68, x_67);
x_70 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_69, x_0);
x_71 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_70);
if (lean::is_scalar(x_61)) {
 x_72 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_72 = x_61;
}
lean::cnstr_set(x_72, 0, x_71);
lean::cnstr_set(x_72, 1, x_59);
return x_72;
}
}
}
obj* _init_l_Lean_Parser_ident_Parser___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::mk_string("identifier");
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_1, 0, x_0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___rarg___lambda__1), 4, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Parser_ident_Parser___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_ident_Parser___rarg___closed__1;
x_2 = lean::apply_2(x_0, lean::box(0), x_1);
return x_2;
}
}
obj* l_Lean_Parser_ident_Parser(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_ident_Parser___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ident_Parser(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ident_Parser_tokens(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_Lean_Parser_ident_Parser_tokens___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ident_Parser_tokens(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_0 = lean::box(0);
x_1 = lean::mk_string("NOTAnIdent");
lean::inc(x_1);
x_3 = l_Lean_Parser_Substring_ofString(x_1);
x_4 = lean::box(0);
x_5 = lean_name_mk_string(x_4, x_1);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_0);
lean::cnstr_set(x_7, 1, x_3);
lean::cnstr_set(x_7, 2, x_5);
lean::cnstr_set(x_7, 3, x_6);
lean::cnstr_set(x_7, 4, x_6);
return x_7;
}
}
obj* _init_l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__2() {
_start:
{
obj* x_0; 
x_0 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
return x_0;
}
}
obj* l_Lean_Parser_ident_Parser_View___rarg___lambda__1(obj* x_0) {
_start:
{
switch (lean::obj_tag(x_0)) {
case 1:
{
obj* x_1; 
x_1 = lean::cnstr_get(x_0, 0);
lean::inc(x_1);
return x_1;
}
default:
{
obj* x_3; 
x_3 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__2;
return x_3;
}
}
}
}
obj* l_Lean_Parser_ident_Parser_View___rarg___lambda__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_1, 0, x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_ident_Parser_View___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser_View___rarg___lambda__1___boxed), 1, 0);
return x_0;
}
}
obj* _init_l_Lean_Parser_ident_Parser_View___rarg___closed__2() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser_View___rarg___lambda__2), 1, 0);
return x_0;
}
}
obj* l_Lean_Parser_ident_Parser_View___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_ident_Parser_View___rarg___closed__1;
x_2 = l_Lean_Parser_ident_Parser_View___rarg___closed__2;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_ident_Parser_View(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser_View___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_ident_Parser_View___rarg___lambda__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ident_Parser_View___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ident_Parser_View___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_ident_Parser_View___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_ident_Parser_View(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* _init_l_Lean_Parser_rawIdent_Parser___rarg___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_token_4__ident_x_27), 3, 0);
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___at_Lean_Parser_token___spec__3___boxed), 4, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_2, 0, x_0);
lean::closure_set(x_2, 1, x_1);
return x_2;
}
}
obj* l_Lean_Parser_rawIdent_Parser___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_rawIdent_Parser___rarg___closed__1;
x_2 = lean::apply_2(x_0, lean::box(0), x_1);
return x_2;
}
}
obj* l_Lean_Parser_rawIdent_Parser(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_rawIdent_Parser___rarg), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_rawIdent_Parser___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_rawIdent_Parser(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_rawIdent_Parser_tokens(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
return x_2;
}
}
obj* l_Lean_Parser_rawIdent_Parser_tokens___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_rawIdent_Parser_tokens(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_rawIdent_Parser_View___rarg(obj* x_0) {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = l_Lean_Parser_ident_Parser_View___rarg___closed__1;
x_2 = l_Lean_Parser_ident_Parser_View___rarg___closed__2;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_rawIdent_Parser_View(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_rawIdent_Parser_View___rarg___boxed), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_rawIdent_Parser_View___rarg___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_rawIdent_Parser_View___rarg(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_rawIdent_Parser_View___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_rawIdent_Parser_View(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_symbolOrIdent___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_2);
lean::inc(x_1);
x_6 = l_Lean_Parser_token(x_1, x_2, x_3);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; obj* x_11; obj* x_12; obj* x_14; obj* x_16; obj* x_18; obj* x_19; 
x_9 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_set(x_6, 1, lean::box(0));
 x_11 = x_6;
} else {
 lean::inc(x_9);
 lean::dec(x_6);
 x_11 = lean::box(0);
}
x_12 = lean::cnstr_get(x_7, 0);
x_14 = lean::cnstr_get(x_7, 1);
x_16 = lean::cnstr_get(x_7, 2);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_set(x_7, 0, lean::box(0));
 lean::cnstr_set(x_7, 1, lean::box(0));
 lean::cnstr_set(x_7, 2, lean::box(0));
 x_18 = x_7;
} else {
 lean::inc(x_12);
 lean::inc(x_14);
 lean::inc(x_16);
 lean::dec(x_7);
 x_18 = lean::box(0);
}
switch (lean::obj_tag(x_12)) {
case 0:
{
obj* x_21; obj* x_23; obj* x_26; 
x_21 = lean::cnstr_get(x_12, 0);
lean::inc(x_21);
x_23 = lean::cnstr_get(x_21, 1);
lean::inc(x_23);
lean::dec(x_21);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_23);
x_19 = x_26;
goto lbl_20;
}
case 1:
{
obj* x_27; obj* x_29; obj* x_32; obj* x_34; 
x_27 = lean::cnstr_get(x_12, 0);
lean::inc(x_27);
x_29 = lean::cnstr_get(x_27, 1);
lean::inc(x_29);
lean::dec(x_27);
x_32 = l_Lean_Parser_Substring_toString(x_29);
lean::dec(x_29);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_32);
x_19 = x_34;
goto lbl_20;
}
default:
{
obj* x_35; 
x_35 = lean::box(0);
x_19 = x_35;
goto lbl_20;
}
}
lbl_20:
{
uint8 x_36; 
if (lean::obj_tag(x_19) == 0)
{
uint8 x_38; 
x_38 = 1;
x_36 = x_38;
goto lbl_37;
}
else
{
obj* x_39; uint8 x_42; 
x_39 = lean::cnstr_get(x_19, 0);
lean::inc(x_39);
lean::dec(x_19);
x_42 = lean::string_dec_eq(x_39, x_0);
lean::dec(x_39);
if (x_42 == 0)
{
uint8 x_44; 
x_44 = 1;
x_36 = x_44;
goto lbl_37;
}
else
{
uint8 x_45; 
x_45 = 0;
x_36 = x_45;
goto lbl_37;
}
}
lbl_37:
{
if (x_36 == 0)
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_49 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_18)) {
 x_50 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_50 = x_18;
}
lean::cnstr_set(x_50, 0, x_12);
lean::cnstr_set(x_50, 1, x_14);
lean::cnstr_set(x_50, 2, x_49);
x_51 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_50);
x_52 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_51);
x_54 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_53);
if (lean::is_scalar(x_11)) {
 x_55 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_55 = x_11;
}
lean::cnstr_set(x_55, 0, x_54);
lean::cnstr_set(x_55, 1, x_9);
return x_55;
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_67; 
lean::dec(x_11);
lean::dec(x_18);
x_58 = l_String_quote(x_0);
x_59 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_59, 0, x_58);
x_60 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_60, 0, x_2);
x_61 = lean::box(0);
x_62 = l_String_splitAux___main___closed__1;
x_63 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_62, x_59, x_60, x_61, x_1, x_14, x_9);
lean::dec(x_14);
lean::dec(x_1);
lean::dec(x_60);
x_67 = lean::cnstr_get(x_63, 0);
lean::inc(x_67);
if (lean::obj_tag(x_67) == 0)
{
obj* x_69; obj* x_71; obj* x_72; obj* x_74; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_69 = lean::cnstr_get(x_63, 1);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 x_71 = x_63;
} else {
 lean::inc(x_69);
 lean::dec(x_63);
 x_71 = lean::box(0);
}
x_72 = lean::cnstr_get(x_67, 1);
x_74 = lean::cnstr_get(x_67, 2);
if (lean::is_exclusive(x_67)) {
 lean::cnstr_release(x_67, 0);
 x_76 = x_67;
} else {
 lean::inc(x_72);
 lean::inc(x_74);
 lean::dec(x_67);
 x_76 = lean::box(0);
}
x_77 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_76)) {
 x_78 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_78 = x_76;
}
lean::cnstr_set(x_78, 0, x_12);
lean::cnstr_set(x_78, 1, x_72);
lean::cnstr_set(x_78, 2, x_77);
x_79 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_74, x_78);
x_80 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_79);
x_81 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_77, x_80);
x_82 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_81);
if (lean::is_scalar(x_71)) {
 x_83 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_83 = x_71;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_69);
return x_83;
}
else
{
obj* x_85; obj* x_87; obj* x_88; uint8 x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; 
lean::dec(x_12);
x_85 = lean::cnstr_get(x_63, 1);
if (lean::is_exclusive(x_63)) {
 lean::cnstr_release(x_63, 0);
 x_87 = x_63;
} else {
 lean::inc(x_85);
 lean::dec(x_63);
 x_87 = lean::box(0);
}
x_88 = lean::cnstr_get(x_67, 0);
x_90 = lean::cnstr_get_scalar<uint8>(x_67, sizeof(void*)*1);
if (lean::is_exclusive(x_67)) {
 x_91 = x_67;
} else {
 lean::inc(x_88);
 lean::dec(x_67);
 x_91 = lean::box(0);
}
if (lean::is_scalar(x_91)) {
 x_92 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_92 = x_91;
}
lean::cnstr_set(x_92, 0, x_88);
lean::cnstr_set_scalar(x_92, sizeof(void*)*1, x_90);
x_93 = x_92;
x_94 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_93);
x_95 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_96 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_95, x_94);
x_97 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_96);
if (lean::is_scalar(x_87)) {
 x_98 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_98 = x_87;
}
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_85);
return x_98;
}
}
}
}
}
else
{
obj* x_102; obj* x_104; obj* x_105; uint8 x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
lean::dec(x_1);
lean::dec(x_0);
lean::dec(x_2);
x_102 = lean::cnstr_get(x_6, 1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_104 = x_6;
} else {
 lean::inc(x_102);
 lean::dec(x_6);
 x_104 = lean::box(0);
}
x_105 = lean::cnstr_get(x_7, 0);
x_107 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 x_108 = x_7;
} else {
 lean::inc(x_105);
 lean::dec(x_7);
 x_108 = lean::box(0);
}
if (lean::is_scalar(x_108)) {
 x_109 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_109 = x_108;
}
lean::cnstr_set(x_109, 0, x_105);
lean::cnstr_set_scalar(x_109, sizeof(void*)*1, x_107);
x_110 = x_109;
x_111 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_112 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_111, x_110);
x_113 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_112);
if (lean::is_scalar(x_104)) {
 x_114 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_114 = x_104;
}
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_102);
return x_114;
}
}
}
obj* l_Lean_Parser_symbolOrIdent___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___rarg___lambda__1), 4, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::apply_2(x_0, lean::box(0), x_2);
return x_3;
}
}
obj* l_Lean_Parser_symbolOrIdent(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___rarg), 2, 0);
return x_1;
}
}
obj* l_Lean_Parser_symbolOrIdent___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_symbolOrIdent(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_symbolOrIdent_tokens(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
}
obj* l_Lean_Parser_symbolOrIdent_tokens___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_symbolOrIdent_tokens(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_symbolOrIdent_View___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_mjoin___rarg___closed__1;
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_symbolOrIdent_View(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent_View___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Lean_Parser_symbolOrIdent_View___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_symbolOrIdent_View___rarg(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_symbolOrIdent_View___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_symbolOrIdent_View(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_8; obj* x_9; obj* x_11; obj* x_13; obj* x_15; 
lean::inc(x_4);
lean::inc(x_3);
x_8 = l_Lean_Parser_token(x_3, x_4, x_5);
x_9 = lean::cnstr_get(x_8, 0);
x_11 = lean::cnstr_get(x_8, 1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_set(x_8, 0, lean::box(0));
 lean::cnstr_set(x_8, 1, lean::box(0));
 x_13 = x_8;
} else {
 lean::inc(x_9);
 lean::inc(x_11);
 lean::dec(x_8);
 x_13 = lean::box(0);
}
lean::inc(x_0);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_15, 0, x_0);
if (lean::obj_tag(x_9) == 0)
{
obj* x_16; obj* x_18; obj* x_20; obj* x_22; obj* x_23; 
x_16 = lean::cnstr_get(x_9, 0);
x_18 = lean::cnstr_get(x_9, 1);
x_20 = lean::cnstr_get(x_9, 2);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_set(x_9, 0, lean::box(0));
 lean::cnstr_set(x_9, 1, lean::box(0));
 lean::cnstr_set(x_9, 2, lean::box(0));
 x_22 = x_9;
} else {
 lean::inc(x_16);
 lean::inc(x_18);
 lean::inc(x_20);
 lean::dec(x_9);
 x_22 = lean::box(0);
}
switch (lean::obj_tag(x_16)) {
case 0:
{
obj* x_25; obj* x_27; uint8 x_30; 
x_25 = lean::cnstr_get(x_16, 0);
lean::inc(x_25);
x_27 = lean::cnstr_get(x_25, 1);
lean::inc(x_27);
lean::dec(x_25);
x_30 = lean::string_dec_eq(x_0, x_27);
lean::dec(x_0);
if (x_30 == 0)
{
obj* x_34; obj* x_35; obj* x_36; obj* x_40; 
lean::dec(x_13);
lean::dec(x_22);
x_34 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_34, 0, x_4);
x_35 = lean::box(0);
x_36 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_27, x_2, x_34, x_35, x_3, x_18, x_11);
lean::dec(x_18);
lean::dec(x_3);
lean::dec(x_34);
x_40 = lean::cnstr_get(x_36, 0);
lean::inc(x_40);
if (lean::obj_tag(x_40) == 0)
{
obj* x_42; obj* x_44; obj* x_45; obj* x_47; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_42 = lean::cnstr_get(x_36, 1);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_release(x_36, 0);
 x_44 = x_36;
} else {
 lean::inc(x_42);
 lean::dec(x_36);
 x_44 = lean::box(0);
}
x_45 = lean::cnstr_get(x_40, 1);
x_47 = lean::cnstr_get(x_40, 2);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_release(x_40, 0);
 x_49 = x_40;
} else {
 lean::inc(x_45);
 lean::inc(x_47);
 lean::dec(x_40);
 x_49 = lean::box(0);
}
x_50 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_49)) {
 x_51 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_51 = x_49;
}
lean::cnstr_set(x_51, 0, x_16);
lean::cnstr_set(x_51, 1, x_45);
lean::cnstr_set(x_51, 2, x_50);
x_52 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_47, x_51);
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_20, x_52);
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_50, x_53);
x_55 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_54, x_15);
x_56 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_55);
if (lean::is_scalar(x_44)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_44;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_42);
return x_57;
}
else
{
obj* x_59; obj* x_61; obj* x_62; uint8 x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_16);
x_59 = lean::cnstr_get(x_36, 1);
if (lean::is_exclusive(x_36)) {
 lean::cnstr_release(x_36, 0);
 x_61 = x_36;
} else {
 lean::inc(x_59);
 lean::dec(x_36);
 x_61 = lean::box(0);
}
x_62 = lean::cnstr_get(x_40, 0);
x_64 = lean::cnstr_get_scalar<uint8>(x_40, sizeof(void*)*1);
if (lean::is_exclusive(x_40)) {
 x_65 = x_40;
} else {
 lean::inc(x_62);
 lean::dec(x_40);
 x_65 = lean::box(0);
}
if (lean::is_scalar(x_65)) {
 x_66 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_66 = x_65;
}
lean::cnstr_set(x_66, 0, x_62);
lean::cnstr_set_scalar(x_66, sizeof(void*)*1, x_64);
x_67 = x_66;
x_68 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_20, x_67);
x_69 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_70 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_69, x_68);
x_71 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_70, x_15);
x_72 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_71);
if (lean::is_scalar(x_61)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_61;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_59);
return x_73;
}
}
else
{
obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_27);
x_78 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_22)) {
 x_79 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_79 = x_22;
}
lean::cnstr_set(x_79, 0, x_16);
lean::cnstr_set(x_79, 1, x_18);
lean::cnstr_set(x_79, 2, x_78);
x_80 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_20, x_79);
x_81 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_81, x_80);
x_83 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_82, x_15);
x_84 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_83);
if (lean::is_scalar(x_13)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_13;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_11);
return x_85;
}
}
case 3:
{
obj* x_89; 
lean::dec(x_13);
lean::dec(x_0);
lean::dec(x_22);
x_89 = lean::box(0);
x_23 = x_89;
goto lbl_24;
}
default:
{
obj* x_94; 
lean::dec(x_13);
lean::dec(x_0);
lean::dec(x_16);
lean::dec(x_22);
x_94 = lean::box(0);
x_23 = x_94;
goto lbl_24;
}
}
lbl_24:
{
obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_103; obj* x_105; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
lean::dec(x_23);
x_96 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_96, 0, x_4);
x_97 = lean::box(0);
x_98 = l_String_splitAux___main___closed__1;
x_99 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_98, x_2, x_96, x_97, x_3, x_18, x_11);
lean::dec(x_18);
lean::dec(x_3);
lean::dec(x_96);
x_103 = lean::cnstr_get(x_99, 0);
x_105 = lean::cnstr_get(x_99, 1);
if (lean::is_exclusive(x_99)) {
 x_107 = x_99;
} else {
 lean::inc(x_103);
 lean::inc(x_105);
 lean::dec(x_99);
 x_107 = lean::box(0);
}
x_108 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_20, x_103);
x_109 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_110 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_109, x_108);
x_111 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_110, x_15);
x_112 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_111);
if (lean::is_scalar(x_107)) {
 x_113 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_113 = x_107;
}
lean::cnstr_set(x_113, 0, x_112);
lean::cnstr_set(x_113, 1, x_105);
return x_113;
}
}
else
{
obj* x_118; uint8 x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_0);
lean::dec(x_2);
x_118 = lean::cnstr_get(x_9, 0);
x_120 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 x_121 = x_9;
} else {
 lean::inc(x_118);
 lean::dec(x_9);
 x_121 = lean::box(0);
}
if (lean::is_scalar(x_121)) {
 x_122 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_122 = x_121;
}
lean::cnstr_set(x_122, 0, x_118);
lean::cnstr_set_scalar(x_122, sizeof(void*)*1, x_120);
x_123 = x_122;
x_124 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_125 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_124, x_123);
x_126 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_125, x_15);
x_127 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_126);
if (lean::is_scalar(x_13)) {
 x_128 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_128 = x_13;
}
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_11);
return x_128;
}
}
}
obj* l_List_foldl___main___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__3(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; 
x_5 = lean::apply_3(x_0, x_2, x_3, x_4);
return x_5;
}
else
{
obj* x_6; obj* x_8; obj* x_11; 
x_6 = lean::cnstr_get(x_1, 0);
lean::inc(x_6);
x_8 = lean::cnstr_get(x_1, 1);
lean::inc(x_8);
lean::dec(x_1);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_orelse___at_Lean_Parser_parseBinLit___spec__1___rarg), 5, 2);
lean::closure_set(x_11, 0, x_0);
lean::closure_set(x_11, 1, x_6);
x_0 = x_11;
x_1 = x_8;
goto _start;
}
}
}
obj* l_Lean_Parser_Combinators_anyOf___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__2(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::box(0);
x_5 = l_Lean_Parser_Combinators_anyOf___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_5, x_6, x_4, x_4, x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
else
{
obj* x_10; obj* x_12; obj* x_15; 
x_10 = lean::cnstr_get(x_0, 0);
lean::inc(x_10);
x_12 = lean::cnstr_get(x_0, 1);
lean::inc(x_12);
lean::dec(x_0);
x_15 = l_List_foldl___main___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__3(x_10, x_12, x_1, x_2, x_3);
return x_15;
}
}
}
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_9; obj* x_12; obj* x_14; 
lean::inc(x_2);
x_4 = l_Lean_Parser_symbol_tokens___rarg(x_0, x_2);
x_5 = l_Lean_Parser_symbol_tokens___rarg(x_1, x_2);
x_6 = lean::box(0);
x_7 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_6);
lean::dec(x_5);
x_9 = l_Lean_Parser_List_cons_tokens___rarg(x_4, x_7);
lean::dec(x_7);
lean::dec(x_4);
x_12 = l_Lean_Parser_tokens___rarg(x_9);
lean::dec(x_9);
x_14 = l_Lean_Parser_tokens___rarg(x_12);
lean::dec(x_12);
return x_14;
}
}
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1(x_0, x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___rarg(x_0, x_1, x_2);
lean::dec(x_0);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens(x_0, x_1);
lean::dec(x_0);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasView___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_22; 
x_4 = l_String_trim(x_1);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_6, 0, x_4);
lean::inc(x_3);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1___boxed), 6, 3);
lean::closure_set(x_8, 0, x_4);
lean::closure_set(x_8, 1, x_3);
lean::closure_set(x_8, 2, x_6);
x_9 = l_String_trim(x_2);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_11, 0, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1___boxed), 6, 3);
lean::closure_set(x_12, 0, x_9);
lean::closure_set(x_12, 1, x_3);
lean::closure_set(x_12, 2, x_11);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_14);
lean::inc(x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_anyOf___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__2), 4, 1);
lean::closure_set(x_17, 0, x_15);
x_18 = l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
x_19 = l_Lean_Parser_BasicParserM_Alternative;
x_20 = l_Lean_Parser_Combinators_anyOf_view___rarg(x_18, x_19, x_15);
lean::dec(x_15);
x_22 = l_Lean_Parser_Combinators_monadLift_view___rarg(x_0, x_17, x_20);
lean::dec(x_17);
return x_22;
}
}
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasView(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_unicodeSymbol_Lean_Parser_HasView___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasView___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_unicodeSymbol_Lean_Parser_HasView___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasView___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_unicodeSymbol_Lean_Parser_HasView(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_unicodeSymbol___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_6; obj* x_8; obj* x_9; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_4 = l_String_trim(x_1);
lean::inc(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_6, 0, x_4);
lean::inc(x_3);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1___boxed), 6, 3);
lean::closure_set(x_8, 0, x_4);
lean::closure_set(x_8, 1, x_3);
lean::closure_set(x_8, 2, x_6);
x_9 = l_String_trim(x_2);
lean::inc(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___rarg), 2, 1);
lean::closure_set(x_11, 0, x_9);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1___boxed), 6, 3);
lean::closure_set(x_12, 0, x_9);
lean::closure_set(x_12, 1, x_3);
lean::closure_set(x_12, 2, x_11);
x_13 = lean::box(0);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_8);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_anyOf___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__2), 4, 1);
lean::closure_set(x_16, 0, x_15);
x_17 = lean::apply_2(x_0, lean::box(0), x_16);
return x_17;
}
}
obj* l_Lean_Parser_unicodeSymbol(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_unicodeSymbol___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_Lean_Parser_unicodeSymbol___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_unicodeSymbol___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_unicodeSymbol___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_unicodeSymbol(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_unicodeSymbol_viewDefault___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::box(0);
return x_4;
}
}
obj* l_Lean_Parser_unicodeSymbol_viewDefault(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_unicodeSymbol_viewDefault___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_Lean_Parser_unicodeSymbol_viewDefault___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_unicodeSymbol_viewDefault___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_0);
lean::dec(x_1);
lean::dec(x_2);
lean::dec(x_3);
return x_4;
}
}
obj* l_Lean_Parser_unicodeSymbol_viewDefault___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_unicodeSymbol_viewDefault(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__1___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_RBNode_find___main___at_Lean_NameMap_contains___spec__2(x_2, lean::box(0), x_0, x_1);
return x_3;
}
}
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__1(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_find___main___at_Lean_Parser_indexed___spec__1___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2___rarg(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
if (lean::obj_tag(x_0) == 0)
{
obj* x_4; 
x_4 = l_Lean_Parser_ParsecT_failure___at_Lean_Parser_token___spec__4___rarg(x_2, x_3);
return x_4;
}
else
{
obj* x_5; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_0, 0);
lean::inc(x_5);
lean::dec(x_0);
x_8 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_5);
lean::cnstr_set(x_9, 1, x_2);
lean::cnstr_set(x_9, 2, x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
}
obj* l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2___rarg___boxed), 4, 0);
return x_1;
}
}
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__3___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_RBNode_find___main___at_Lean_NameMap_contains___spec__2(x_2, lean::box(0), x_0, x_1);
return x_3;
}
}
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__3(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_find___main___at_Lean_Parser_indexed___spec__3___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__4___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_RBNode_find___main___at_Lean_NameMap_contains___spec__2(x_2, lean::box(0), x_0, x_1);
return x_3;
}
}
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__4(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_find___main___at_Lean_Parser_indexed___spec__4___rarg___boxed), 2, 0);
return x_1;
}
}
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__5___rarg(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = lean::box(0);
x_3 = l_RBNode_find___main___at_Lean_NameMap_contains___spec__2(x_2, lean::box(0), x_0, x_1);
return x_3;
}
}
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__5(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_RBMap_find___main___at_Lean_Parser_indexed___spec__5___rarg___boxed), 2, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_indexed___rarg___lambda__1___closed__1() {
_start:
{
obj* x_0; obj* x_1; obj* x_2; 
x_0 = lean::box(0);
x_1 = lean::mk_string("ident");
x_2 = lean_name_mk_string(x_0, x_1);
return x_2;
}
}
obj* l_Lean_Parser_indexed___rarg___lambda__1(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_1);
lean::dec(x_0);
x_7 = lean::box(0);
x_8 = l_String_splitAux___main___closed__1;
x_9 = l_mjoin___rarg___closed__1;
x_10 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_8, x_9, x_7, x_7, x_2, x_3, x_4);
lean::dec(x_3);
return x_10;
}
else
{
obj* x_12; 
x_12 = lean::cnstr_get(x_1, 0);
lean::inc(x_12);
lean::dec(x_1);
switch (lean::obj_tag(x_12)) {
case 0:
{
obj* x_15; obj* x_18; obj* x_21; obj* x_22; obj* x_23; obj* x_25; obj* x_26; obj* x_28; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
lean::dec(x_12);
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
lean::dec(x_15);
x_21 = lean::box(0);
x_22 = lean_name_mk_string(x_21, x_18);
x_23 = l_RBMap_find___main___at_Lean_Parser_indexed___spec__1___rarg(x_0, x_22);
lean::dec(x_22);
x_25 = l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2___rarg(x_23, x_2, x_3, x_4);
x_26 = lean::cnstr_get(x_25, 0);
x_28 = lean::cnstr_get(x_25, 1);
if (lean::is_exclusive(x_25)) {
 x_30 = x_25;
} else {
 lean::inc(x_26);
 lean::inc(x_28);
 lean::dec(x_25);
 x_30 = lean::box(0);
}
x_31 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_31, x_26);
if (lean::is_scalar(x_30)) {
 x_33 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_33 = x_30;
}
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_28);
return x_33;
}
case 1:
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_40; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
lean::dec(x_12);
x_35 = l_Lean_Parser_indexed___rarg___lambda__1___closed__1;
x_36 = l_RBMap_find___main___at_Lean_Parser_indexed___spec__3___rarg(x_0, x_35);
x_37 = l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2___rarg(x_36, x_2, x_3, x_4);
x_38 = lean::cnstr_get(x_37, 0);
x_40 = lean::cnstr_get(x_37, 1);
if (lean::is_exclusive(x_37)) {
 x_42 = x_37;
} else {
 lean::inc(x_38);
 lean::inc(x_40);
 lean::dec(x_37);
 x_42 = lean::box(0);
}
x_43 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_44 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_43, x_38);
if (lean::is_scalar(x_42)) {
 x_45 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_45 = x_42;
}
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_40);
return x_45;
}
case 2:
{
obj* x_46; obj* x_49; obj* x_52; obj* x_54; obj* x_55; obj* x_57; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_46 = lean::cnstr_get(x_12, 0);
lean::inc(x_46);
lean::dec(x_12);
x_49 = lean::cnstr_get(x_46, 0);
lean::inc(x_49);
lean::dec(x_46);
x_52 = l_RBMap_find___main___at_Lean_Parser_indexed___spec__4___rarg(x_0, x_49);
lean::dec(x_49);
x_54 = l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2___rarg(x_52, x_2, x_3, x_4);
x_55 = lean::cnstr_get(x_54, 0);
x_57 = lean::cnstr_get(x_54, 1);
if (lean::is_exclusive(x_54)) {
 x_59 = x_54;
} else {
 lean::inc(x_55);
 lean::inc(x_57);
 lean::dec(x_54);
 x_59 = lean::box(0);
}
x_60 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_61 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_60, x_55);
if (lean::is_scalar(x_59)) {
 x_62 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_62 = x_59;
}
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_57);
return x_62;
}
default:
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_68; 
x_63 = lean::box(0);
x_64 = l_String_splitAux___main___closed__1;
x_65 = l_mjoin___rarg___closed__1;
x_66 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_64, x_65, x_63, x_63, x_2, x_3, x_4);
lean::dec(x_3);
x_68 = lean::cnstr_get(x_66, 0);
lean::inc(x_68);
if (lean::obj_tag(x_68) == 0)
{
obj* x_70; obj* x_73; obj* x_75; obj* x_77; obj* x_80; obj* x_82; obj* x_83; obj* x_85; obj* x_87; obj* x_88; obj* x_89; 
x_70 = lean::cnstr_get(x_66, 1);
lean::inc(x_70);
lean::dec(x_66);
x_73 = lean::cnstr_get(x_68, 0);
lean::inc(x_73);
x_75 = lean::cnstr_get(x_68, 1);
lean::inc(x_75);
x_77 = lean::cnstr_get(x_68, 2);
lean::inc(x_77);
lean::dec(x_68);
x_80 = l_RBMap_find___main___at_Lean_Parser_indexed___spec__5___rarg(x_0, x_73);
lean::dec(x_73);
x_82 = l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2___rarg(x_80, x_2, x_75, x_70);
x_83 = lean::cnstr_get(x_82, 0);
x_85 = lean::cnstr_get(x_82, 1);
if (lean::is_exclusive(x_82)) {
 x_87 = x_82;
} else {
 lean::inc(x_83);
 lean::inc(x_85);
 lean::dec(x_82);
 x_87 = lean::box(0);
}
x_88 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_77, x_83);
if (lean::is_scalar(x_87)) {
 x_89 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_89 = x_87;
}
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_85);
return x_89;
}
else
{
obj* x_91; obj* x_93; obj* x_94; uint8 x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
lean::dec(x_0);
x_91 = lean::cnstr_get(x_66, 1);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 x_93 = x_66;
} else {
 lean::inc(x_91);
 lean::dec(x_66);
 x_93 = lean::box(0);
}
x_94 = lean::cnstr_get(x_68, 0);
x_96 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
if (lean::is_exclusive(x_68)) {
 x_97 = x_68;
} else {
 lean::inc(x_94);
 lean::dec(x_68);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_94);
lean::cnstr_set_scalar(x_98, sizeof(void*)*1, x_96);
x_99 = x_98;
if (lean::is_scalar(x_93)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_93;
}
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_91);
return x_100;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_indexed___rarg___closed__1() {
_start:
{
obj* x_0; 
x_0 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_peekToken), 3, 0);
return x_0;
}
}
obj* l_Lean_Parser_indexed___rarg(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_indexed___rarg___lambda__1___boxed), 5, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = l_Lean_Parser_indexed___rarg___closed__1;
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_5, 0, x_4);
lean::closure_set(x_5, 1, x_3);
x_6 = lean::apply_2(x_0, lean::box(0), x_5);
return x_6;
}
}
obj* l_Lean_Parser_indexed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_indexed___rarg___boxed), 3, 0);
return x_1;
}
}
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__1___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_find___main___at_Lean_Parser_indexed___spec__1___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__1___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBMap_find___main___at_Lean_Parser_indexed___spec__1(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2___rarg___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2___rarg(x_0, x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__3___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_find___main___at_Lean_Parser_indexed___spec__3___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__3___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBMap_find___main___at_Lean_Parser_indexed___spec__3(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__4___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_find___main___at_Lean_Parser_indexed___spec__4___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__4___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBMap_find___main___at_Lean_Parser_indexed___spec__4(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__5___rarg___boxed(obj* x_0, obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_RBMap_find___main___at_Lean_Parser_indexed___spec__5___rarg(x_0, x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBMap_find___main___at_Lean_Parser_indexed___spec__5___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_RBMap_find___main___at_Lean_Parser_indexed___spec__5(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* l_Lean_Parser_indexed___rarg___lambda__1___boxed(obj* x_0, obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_indexed___rarg___lambda__1(x_0, x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_indexed___rarg___boxed(obj* x_0, obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_indexed___rarg(x_0, x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_indexed___boxed(obj* x_0) {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_indexed(x_0);
lean::dec(x_0);
return x_1;
}
}
obj* initialize_init_lean_parser_combinators(obj*);
obj* initialize_init_lean_parser_stringliteral(obj*);
static bool _G_initialized = false;
obj* initialize_init_lean_parser_token(obj* w) {
 if (_G_initialized) return w;
 _G_initialized = true;
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_combinators(w);
if (io_result_is_error(w)) return w;
w = initialize_init_lean_parser_stringliteral(w);
 l_Lean_Parser_matchToken___closed__1 = _init_l_Lean_Parser_matchToken___closed__1();
lean::mark_persistent(l_Lean_Parser_matchToken___closed__1);
 l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__1 = _init_l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__1();
lean::mark_persistent(l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__1);
 l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__2 = _init_l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__2();
lean::mark_persistent(l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__2);
 l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__3 = _init_l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__3();
lean::mark_persistent(l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__3);
 l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__4 = _init_l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__4();
lean::mark_persistent(l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__4);
 l_Lean_Parser_finishCommentBlock___closed__1 = _init_l_Lean_Parser_finishCommentBlock___closed__1();
lean::mark_persistent(l_Lean_Parser_finishCommentBlock___closed__1);
 l_Lean_Parser_finishCommentBlock___closed__2 = _init_l_Lean_Parser_finishCommentBlock___closed__2();
lean::mark_persistent(l_Lean_Parser_finishCommentBlock___closed__2);
 l___private_init_lean_parser_token_2__whitespaceAux___main___closed__1 = _init_l___private_init_lean_parser_token_2__whitespaceAux___main___closed__1();
lean::mark_persistent(l___private_init_lean_parser_token_2__whitespaceAux___main___closed__1);
 l___private_init_lean_parser_token_2__whitespaceAux___main___closed__2 = _init_l___private_init_lean_parser_token_2__whitespaceAux___main___closed__2();
lean::mark_persistent(l___private_init_lean_parser_token_2__whitespaceAux___main___closed__2);
 l___private_init_lean_parser_token_2__whitespaceAux___main___closed__3 = _init_l___private_init_lean_parser_token_2__whitespaceAux___main___closed__3();
lean::mark_persistent(l___private_init_lean_parser_token_2__whitespaceAux___main___closed__3);
 l___private_init_lean_parser_token_2__whitespaceAux___main___closed__4 = _init_l___private_init_lean_parser_token_2__whitespaceAux___main___closed__4();
lean::mark_persistent(l___private_init_lean_parser_token_2__whitespaceAux___main___closed__4);
 l_Lean_Parser_withTrailing___rarg___closed__1 = _init_l_Lean_Parser_withTrailing___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_withTrailing___rarg___closed__1);
 l_Lean_Parser_raw_view___rarg___lambda__2___closed__1 = _init_l_Lean_Parser_raw_view___rarg___lambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_raw_view___rarg___lambda__2___closed__1);
 l_Lean_Parser_raw_view___rarg___closed__1 = _init_l_Lean_Parser_raw_view___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_raw_view___rarg___closed__1);
 l_Lean_Parser_raw_view___rarg___closed__2 = _init_l_Lean_Parser_raw_view___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_raw_view___rarg___closed__2);
 l_Lean_Parser_detailIdentPartEscaped = _init_l_Lean_Parser_detailIdentPartEscaped();
lean::mark_persistent(l_Lean_Parser_detailIdentPartEscaped);
 l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__1 = _init_l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__1);
 l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__2 = _init_l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__2();
lean::mark_persistent(l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__2);
 l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__3 = _init_l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__3();
lean::mark_persistent(l_Lean_Parser_detailIdentPartEscaped_HasView_x_27___lambda__2___closed__3);
 l_Lean_Parser_detailIdentPartEscaped_HasView_x_27 = _init_l_Lean_Parser_detailIdentPartEscaped_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_detailIdentPartEscaped_HasView_x_27);
 l_Lean_Parser_detailIdentPartEscaped_HasView = _init_l_Lean_Parser_detailIdentPartEscaped_HasView();
lean::mark_persistent(l_Lean_Parser_detailIdentPartEscaped_HasView);
 l_Lean_Parser_detailIdentPart = _init_l_Lean_Parser_detailIdentPart();
lean::mark_persistent(l_Lean_Parser_detailIdentPart);
 l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__1 = _init_l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__1);
 l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__2 = _init_l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__2();
lean::mark_persistent(l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__2);
 l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__3 = _init_l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__3();
lean::mark_persistent(l_Lean_Parser_detailIdentPart_HasView_x_27___lambda__2___closed__3);
 l_Lean_Parser_detailIdentPart_HasView_x_27 = _init_l_Lean_Parser_detailIdentPart_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_detailIdentPart_HasView_x_27);
 l_Lean_Parser_detailIdentPart_HasView = _init_l_Lean_Parser_detailIdentPart_HasView();
lean::mark_persistent(l_Lean_Parser_detailIdentPart_HasView);
 l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView);
 l_Lean_Parser_detailIdentPart_Parser___closed__1 = _init_l_Lean_Parser_detailIdentPart_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_detailIdentPart_Parser___closed__1);
 l_Lean_Parser_detailIdentSuffix = _init_l_Lean_Parser_detailIdentSuffix();
lean::mark_persistent(l_Lean_Parser_detailIdentSuffix);
 l_Lean_Parser_detailIdentSuffix_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_detailIdentSuffix_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_detailIdentSuffix_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_detailIdentSuffix_HasView_x_27 = _init_l_Lean_Parser_detailIdentSuffix_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_detailIdentSuffix_HasView_x_27);
 l_Lean_Parser_detailIdentSuffix_HasView = _init_l_Lean_Parser_detailIdentSuffix_HasView();
lean::mark_persistent(l_Lean_Parser_detailIdentSuffix_HasView);
 l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens = _init_l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens();
lean::mark_persistent(l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens);
 l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView = _init_l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView();
lean::mark_persistent(l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView);
 l_Lean_Parser_detailIdentSuffix_Parser___closed__1 = _init_l_Lean_Parser_detailIdentSuffix_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_detailIdentSuffix_Parser___closed__1);
 l_Lean_Parser_detailIdent = _init_l_Lean_Parser_detailIdent();
lean::mark_persistent(l_Lean_Parser_detailIdent);
 l_Lean_Parser_detailIdent_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_detailIdent_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_detailIdent_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_detailIdent_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_detailIdent_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_detailIdent_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_detailIdent_HasView_x_27___lambda__2___closed__1 = _init_l_Lean_Parser_detailIdent_HasView_x_27___lambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_detailIdent_HasView_x_27___lambda__2___closed__1);
 l_Lean_Parser_detailIdent_HasView_x_27 = _init_l_Lean_Parser_detailIdent_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_detailIdent_HasView_x_27);
 l_Lean_Parser_detailIdent_HasView = _init_l_Lean_Parser_detailIdent_HasView();
lean::mark_persistent(l_Lean_Parser_detailIdent_HasView);
 l_Lean_Parser_detailIdent_x_27___closed__1 = _init_l_Lean_Parser_detailIdent_x_27___closed__1();
lean::mark_persistent(l_Lean_Parser_detailIdent_x_27___closed__1);
 l_Lean_Parser_detailIdent_Parser___closed__1 = _init_l_Lean_Parser_detailIdent_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_detailIdent_Parser___closed__1);
 l___private_init_lean_parser_token_4__ident_x_27___closed__1 = _init_l___private_init_lean_parser_token_4__ident_x_27___closed__1();
lean::mark_persistent(l___private_init_lean_parser_token_4__ident_x_27___closed__1);
 l_Lean_Parser_parseBinLit___closed__1 = _init_l_Lean_Parser_parseBinLit___closed__1();
lean::mark_persistent(l_Lean_Parser_parseBinLit___closed__1);
 l_Lean_Parser_number = _init_l_Lean_Parser_number();
lean::mark_persistent(l_Lean_Parser_number);
 l_Lean_Parser_number_HasView_x_27___lambda__1___closed__1 = _init_l_Lean_Parser_number_HasView_x_27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_number_HasView_x_27___lambda__1___closed__1);
 l_Lean_Parser_number_HasView_x_27___lambda__1___closed__2 = _init_l_Lean_Parser_number_HasView_x_27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_number_HasView_x_27___lambda__1___closed__2);
 l_Lean_Parser_number_HasView_x_27___lambda__1___closed__3 = _init_l_Lean_Parser_number_HasView_x_27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_number_HasView_x_27___lambda__1___closed__3);
 l_Lean_Parser_number_HasView_x_27___lambda__1___closed__4 = _init_l_Lean_Parser_number_HasView_x_27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_number_HasView_x_27___lambda__1___closed__4);
 l_Lean_Parser_number_HasView_x_27___lambda__1___closed__5 = _init_l_Lean_Parser_number_HasView_x_27___lambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_number_HasView_x_27___lambda__1___closed__5);
 l_Lean_Parser_number_HasView_x_27___lambda__1___closed__6 = _init_l_Lean_Parser_number_HasView_x_27___lambda__1___closed__6();
lean::mark_persistent(l_Lean_Parser_number_HasView_x_27___lambda__1___closed__6);
 l_Lean_Parser_number_HasView_x_27___lambda__2___closed__1 = _init_l_Lean_Parser_number_HasView_x_27___lambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_number_HasView_x_27___lambda__2___closed__1);
 l_Lean_Parser_number_HasView_x_27___lambda__2___closed__2 = _init_l_Lean_Parser_number_HasView_x_27___lambda__2___closed__2();
lean::mark_persistent(l_Lean_Parser_number_HasView_x_27___lambda__2___closed__2);
 l_Lean_Parser_number_HasView_x_27___lambda__2___closed__3 = _init_l_Lean_Parser_number_HasView_x_27___lambda__2___closed__3();
lean::mark_persistent(l_Lean_Parser_number_HasView_x_27___lambda__2___closed__3);
 l_Lean_Parser_number_HasView_x_27___lambda__2___closed__4 = _init_l_Lean_Parser_number_HasView_x_27___lambda__2___closed__4();
lean::mark_persistent(l_Lean_Parser_number_HasView_x_27___lambda__2___closed__4);
 l_Lean_Parser_number_HasView_x_27___lambda__2___closed__5 = _init_l_Lean_Parser_number_HasView_x_27___lambda__2___closed__5();
lean::mark_persistent(l_Lean_Parser_number_HasView_x_27___lambda__2___closed__5);
 l_Lean_Parser_number_HasView_x_27___lambda__2___closed__6 = _init_l_Lean_Parser_number_HasView_x_27___lambda__2___closed__6();
lean::mark_persistent(l_Lean_Parser_number_HasView_x_27___lambda__2___closed__6);
 l_Lean_Parser_number_HasView_x_27 = _init_l_Lean_Parser_number_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_number_HasView_x_27);
 l_Lean_Parser_number_HasView = _init_l_Lean_Parser_number_HasView();
lean::mark_persistent(l_Lean_Parser_number_HasView);
 l_Lean_Parser_number_x_27___closed__1 = _init_l_Lean_Parser_number_x_27___closed__1();
lean::mark_persistent(l_Lean_Parser_number_x_27___closed__1);
 l_Lean_Parser_stringLit = _init_l_Lean_Parser_stringLit();
lean::mark_persistent(l_Lean_Parser_stringLit);
 l_Lean_Parser_stringLit_HasView_x_27___lambda__2___closed__1 = _init_l_Lean_Parser_stringLit_HasView_x_27___lambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_stringLit_HasView_x_27___lambda__2___closed__1);
 l_Lean_Parser_stringLit_HasView_x_27 = _init_l_Lean_Parser_stringLit_HasView_x_27();
lean::mark_persistent(l_Lean_Parser_stringLit_HasView_x_27);
 l_Lean_Parser_stringLit_HasView = _init_l_Lean_Parser_stringLit_HasView();
lean::mark_persistent(l_Lean_Parser_stringLit_HasView);
 l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5___closed__1 = _init_l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5___closed__1();
lean::mark_persistent(l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x_27___spec__5___closed__1);
 l_Lean_Parser_stringLit_x_27___closed__1 = _init_l_Lean_Parser_stringLit_x_27___closed__1();
lean::mark_persistent(l_Lean_Parser_stringLit_x_27___closed__1);
 l_Lean_Parser_token___closed__1 = _init_l_Lean_Parser_token___closed__1();
lean::mark_persistent(l_Lean_Parser_token___closed__1);
 l_Lean_Parser_token___closed__2 = _init_l_Lean_Parser_token___closed__2();
lean::mark_persistent(l_Lean_Parser_token___closed__2);
 l_Lean_Parser_peekToken___closed__1 = _init_l_Lean_Parser_peekToken___closed__1();
lean::mark_persistent(l_Lean_Parser_peekToken___closed__1);
 l_Lean_Parser_number_Parser___rarg___closed__1 = _init_l_Lean_Parser_number_Parser___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_number_Parser___rarg___closed__1);
 l_Lean_Parser_number_Parser_view___rarg___closed__1 = _init_l_Lean_Parser_number_Parser_view___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_number_Parser_view___rarg___closed__1);
 l_Lean_Parser_number_Parser_view___rarg___closed__2 = _init_l_Lean_Parser_number_Parser_view___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_number_Parser_view___rarg___closed__2);
 l_Lean_Parser_stringLit_Parser___rarg___closed__1 = _init_l_Lean_Parser_stringLit_Parser___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_stringLit_Parser___rarg___closed__1);
 l_Lean_Parser_stringLit_Parser_View___rarg___closed__1 = _init_l_Lean_Parser_stringLit_Parser_View___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_stringLit_Parser_View___rarg___closed__1);
 l_Lean_Parser_stringLit_Parser_View___rarg___closed__2 = _init_l_Lean_Parser_stringLit_Parser_View___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_stringLit_Parser_View___rarg___closed__2);
 l_Lean_Parser_stringLit_View_value___closed__1 = _init_l_Lean_Parser_stringLit_View_value___closed__1();
lean::mark_persistent(l_Lean_Parser_stringLit_View_value___closed__1);
 l_Lean_Parser_ident_Parser___rarg___closed__1 = _init_l_Lean_Parser_ident_Parser___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_ident_Parser___rarg___closed__1);
 l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1 = _init_l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1);
 l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__2 = _init_l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__2);
 l_Lean_Parser_ident_Parser_View___rarg___closed__1 = _init_l_Lean_Parser_ident_Parser_View___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_ident_Parser_View___rarg___closed__1);
 l_Lean_Parser_ident_Parser_View___rarg___closed__2 = _init_l_Lean_Parser_ident_Parser_View___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_ident_Parser_View___rarg___closed__2);
 l_Lean_Parser_rawIdent_Parser___rarg___closed__1 = _init_l_Lean_Parser_rawIdent_Parser___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_rawIdent_Parser___rarg___closed__1);
 l_Lean_Parser_indexed___rarg___lambda__1___closed__1 = _init_l_Lean_Parser_indexed___rarg___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_indexed___rarg___lambda__1___closed__1);
 l_Lean_Parser_indexed___rarg___closed__1 = _init_l_Lean_Parser_indexed___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_indexed___rarg___closed__1);
return w;
}
