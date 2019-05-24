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
extern obj* l_Lean_Parser_parseHexDigit___rarg___lambda__5___closed__1;
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_withTrailing___rarg___lambda__1(obj*, obj*);
obj* l_Lean_Parser_rawStr_Lean_Parser_HasTokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_Parser_view___rarg___closed__2;
obj* l___private_init_lean_parser_parsec_4__mkStringResult___rarg(obj*, obj*);
obj* l_Lean_Parser_indexed___rarg___closed__1;
obj* l_Lean_Parser_raw_view___rarg(obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_List_mfoldr___main___at_Lean_Parser_number_x27___spec__9(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_rawStr_Lean_Parser_HasView___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_String_foldlAux___main___at_String_toNat___spec__1___closed__1;
obj* l_Lean_Parser_stringLit;
obj* l_fixCore___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x27___spec__4___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_raw_view___rarg___closed__1;
obj* l_Lean_Parser_stringLit_View_value(obj*);
obj* l_Lean_Parser_finishCommentBlock(obj*, obj*, obj*, obj*);
extern "C" uint8 lean_name_dec_eq(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2(obj*);
obj* l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_View_value___spec__8(obj*);
obj* l_Lean_Parser_ident_Parser_View___rarg___lambda__2(obj*);
extern obj* l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
obj* l_Lean_Parser_raw_view___rarg___lambda__1___boxed(obj*);
extern obj* l_Lean_Parser_BasicParserM_Alternative;
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_number_x27___spec__7___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x27___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolOrIdent_View___boxed(obj*);
obj* l_Lean_Parser_raw___boxed(obj*);
obj* l_Lean_Parser_symbol_tokens(obj*, obj*);
obj* l_Lean_Parser_ident_Parser_tokens(obj*, obj*);
obj* l_Lean_Parser_Trie_oldMatchPrefix___rarg(obj*, obj*);
obj* l_Lean_Parser_symbolOrIdent___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__4___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentSuffix_HasView_x27___elambda__2(obj*);
obj* l_DList_singleton___elambda__1___rarg(obj*, obj*);
obj* l_Lean_Parser_rawIdent_Parser_View___boxed(obj*);
obj* l_Lean_Parser_detailIdent_x27___closed__1;
obj* l___private_init_lean_parser_token_4__ident_x27___lambda__2(uint32, uint32, obj*, obj*, obj*);
obj* l_Lean_Parser_symbol_tokens___rarg(obj*, obj*);
namespace lean {
obj* nat_sub(obj*, obj*);
}
obj* l_String_toNat(obj*);
uint8 l_Lean_isIdRest(uint32);
obj* l___private_init_lean_parser_token_4__ident_x27___closed__1;
obj* l_Lean_Parser_stringLit_HasView_x27___elambda__1___closed__1;
obj* l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__1;
obj* l___private_init_lean_parser_token_4__ident_x27(obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_4__ident_x27___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_many1Aux_x27___main___at_Lean_Parser_parseBinLit___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Parser_number_x27___spec__5(obj*);
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_rawStr(obj*);
uint8 l_Lean_isIdEndEscape(uint32);
obj* l_Lean_Parser_stringLit_Parser_tokens(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_curr___at___private_init_lean_parser_token_4__ident_x27___spec__2___rarg(obj*, obj*);
obj* l_Lean_Parser_detailIdentSuffix_Parser(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolOrIdent_View___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___boxed(obj*, obj*);
uint8 l_String_isEmpty(obj*);
obj* l_Lean_Parser_detailIdent_HasView_x27___lambda__1___closed__1;
obj* l___private_init_lean_parser_token_2__whitespaceAux___main___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_7__toNatCore___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_parseHexDigit___rarg___lambda__3___closed__1;
obj* l_Lean_Parser_stringLit_Parser___rarg(obj*);
extern obj* l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1;
obj* l_Lean_Parser_number_HasView_x27___elambda__1___closed__3;
obj* l_ReaderT_bind___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__6(obj*, obj*);
obj* l_Lean_Parser_symbolOrIdent___boxed(obj*);
obj* l_Lean_Parser_parseQuotedChar___at_Lean_Parser_stringLit_x27___spec__3(obj*, obj*, obj*);
obj* l_Lean_Parser_symbol_viewDefault(obj*);
obj* l_Lean_Parser_number_Parser_view(obj*);
obj* l_Lean_Parser_rawStr_viewDefault___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseStringLiteral___at_Lean_Parser_stringLit_x27___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView;
obj* l___private_init_lean_parser_parsec_7__takeWhileAux_x27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__6___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_raw_view(obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseHexLit___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_stringLit_HasView_x27___elambda__2(obj*);
obj* l_Lean_Parser_number_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_detailIdentPartEscaped_HasView;
obj* l_Lean_Parser_indexed___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbol___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbol_View___rarg(obj*, obj*, obj*);
extern obj* l_mjoin___rarg___closed__1;
obj* l_Lean_Parser_asSubstring___boxed(obj*);
obj* l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView;
obj* l_Lean_Parser_raw_view___rarg___closed__2;
extern obj* l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
obj* l_Lean_Parser_number_Parser___rarg___closed__1;
obj* l___private_init_lean_parser_token_2__whitespaceAux___main(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3(obj*);
obj* l_Lean_Parser_finishCommentBlock___closed__2;
obj* l_Lean_Parser_numberOrStringLit(obj*, obj*, obj*);
obj* l_Lean_Parser_raw___rarg___lambda__3___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_BasicParserM_Monad;
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux___main(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_withTrailing___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6(uint32, obj*, obj*, obj*);
obj* l_Lean_Parser_rawStr_Lean_Parser_HasView___boxed(obj*);
obj* l___private_init_lean_parser_token_2__whitespaceAux(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_stringLit_x27___closed__1;
obj* l_Lean_Parser_number_Parser_tokens(obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__5___rarg(obj*, obj*);
uint8 l_Char_isAlpha(uint32);
obj* l_Lean_Parser_rawIdent_Parser___rarg___closed__1;
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_View_value___spec__7___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__3;
obj* l_Function_comp___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_labelsMkRes___rarg(obj*, obj*);
obj* l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__2;
uint32 l_String_OldIterator_curr___main(obj*);
obj* l_List_reverse___rarg(obj*);
obj* l_ReaderT_bind___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__6___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseOctLit___spec__1(uint32, obj*, obj*, obj*);
obj* l_Lean_Parser_token___closed__1;
obj* l_Lean_Parser_ident_Parser_View___rarg___closed__1;
obj* l___private_init_lean_parser_token_5__mkConsumeToken___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_indexed___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_raw___rarg___lambda__2(obj*, uint8, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_HasView_x27___elambda__1___closed__1;
uint8 l_Lean_Parser_Syntax_isOfKind___main(obj*, obj*);
obj* l_ReaderT_orelse___at_Lean_Parser_parseBinLit___spec__1___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__4(obj*);
obj* l_Lean_Parser_detailIdent_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_stringLit_Parser_View___boxed(obj*);
obj* l_Lean_Parser_rawStr_viewDefault___boxed(obj*);
obj* l_Lean_Parser_number_x27___closed__1;
obj* l_id___rarg___boxed(obj*);
obj* l_Lean_Parser_asSubstring___rarg___lambda__3(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_digit___at_Lean_Parser_stringLit_View_value___spec__9(obj*);
obj* l___private_init_lean_parser_parsec_7__takeWhileAux_x27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__6(obj*, uint8, obj*);
obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x27;
obj* l_String_OldIterator_remaining___main(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x27___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdent_HasView_x27___elambda__1___closed__1;
obj* l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_x27___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__4___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_Combinators_node_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_2__whitespaceAux___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_x27___lambda__4___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_withTrailing___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_raw_view___boxed(obj*);
obj* l_Lean_Parser_number_HasView;
obj* l_Lean_Parser_number_HasView_x27___lambda__1___closed__2;
obj* l_Lean_Parser_unicodeSymbol___boxed(obj*);
obj* l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_View_value___spec__4___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbol_viewDefault___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_rawIdent_Parser_tokens___boxed(obj*, obj*);
obj* l_Lean_Parser_Substring_toString(obj*);
obj* l_Lean_Parser_rawStr_Lean_Parser_HasView(obj*);
obj* l_Lean_Parser_stringLit_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_4__ident_x27___spec__7(obj*, obj*, uint32, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_Parser(obj*, obj*, obj*);
obj* l_Lean_Parser_indexed___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseStringLiteral___at_Lean_Parser_stringLit_x27___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_curr___at___private_init_lean_parser_token_4__ident_x27___spec__2(obj*);
obj* l_Lean_Parser_MonadParsec_digit___at_Lean_Parser_stringLit_x27___spec__6___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_asSubstring___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseQuotedChar___at_Lean_Parser_stringLit_x27___spec__3___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_withTrailing___at_Lean_Parser_token___spec__3(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_raw(obj*);
obj* l_String_OldIterator_nextn___main(obj*, obj*);
extern obj* l_Lean_Parser_RecT_runParsec___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_indexed___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseHexLit___spec__1(obj*, obj*, obj*);
namespace lean {
obj* string_push(obj*, uint32);
}
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_updateLast___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__6(obj*);
obj* l_Lean_Parser_detailIdent_x27(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_whitespace(obj*, obj*, obj*);
obj* l_Lean_Parser_Syntax_asNode___main(obj*);
obj* l_Lean_Parser_MonadParsec_whitespace___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_number_x27___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_number_Parser_view___rarg___boxed(obj*);
obj* l_Lean_Parser_symbolOrIdent(obj*);
obj* l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_View_value___spec__4(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
obj* l_Lean_Parser_matchToken(obj*, obj*, obj*);
obj* l_Lean_Parser_finishCommentBlock___boxed(obj*, obj*, obj*, obj*);
obj* l_Nat_repr(obj*);
obj* l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2(obj*);
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___rarg___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__7(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_tokenCont(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_mkRawRes(obj*, obj*);
obj* l_Lean_Parser_withTrailing___rarg___lambda__3(obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_number_x27___spec__7(obj*);
obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_stringLit_Parser_View___rarg___closed__2;
obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_ParsecT_failure___at_Lean_Parser_token___spec__4___rarg(obj*, obj*);
extern obj* l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
obj* l_Lean_Parser_symbol_View___boxed(obj*);
obj* l_Lean_Parser_symbol_viewDefault___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile_x27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__2___boxed(obj*);
obj* l_Lean_Parser_raw_view___rarg___lambda__2(obj*);
obj* l_Lean_Parser_unicodeSymbol___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_stringLit_View_value___spec__2(uint32, obj*);
obj* l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1;
extern obj* l_Lean_Parser_parseQuotedChar___rarg___lambda__7___closed__1;
obj* l___private_init_lean_parser_token_4__ident_x27___lambda__1(obj*, uint32, obj*, obj*, obj*);
obj* l_List_enumFrom___main___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_number_x27___spec__8___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_idPartDefault___at___private_init_lean_parser_token_4__ident_x27___spec__3(obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_2__strAux___main(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ident_Parser___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile_x27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__2(obj*);
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__3___rarg(obj*, obj*);
obj* l_ReaderT_Monad___rarg(obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_number_x27___spec__3(obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_anyOf_view___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_anyOf___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolCore___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_stringLit_Parser(obj*);
obj* l_Lean_Parser_rawIdent_Parser_tokens(obj*, obj*);
obj* l_Lean_Parser_stringLit_x27(obj*, obj*, obj*);
obj* l_Lean_Parser_symbol_viewDefault___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_RecT_Lean_Parser_MonadParsec___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_monadLift_view___rarg(obj*, obj*, obj*);
uint8 l_Lean_isIdBeginEscape(uint32);
obj* l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1(obj*);
obj* l_Lean_Parser_MonadParsec_observing___at_Lean_Parser_peekToken___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseOctLit___spec__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ident_Parser(obj*);
obj* l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_x27___spec__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldl___at___private_init_lean_parser_token_4__ident_x27___spec__8(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_number_x27___spec__8___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number;
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_number_x27___spec__7___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolCore___boxed(obj*);
obj* l___private_init_lean_parser_token_3__updateTrailing(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x27___spec__4(obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg(obj*, obj*);
obj* l_Lean_Parser_stringLit_Parser_View___rarg___boxed(obj*);
obj* l_Lean_Parser_tryView___at_Lean_Parser_stringLit_Parser___spec__1(obj*, obj*);
namespace lean {
obj* string_append(obj*, obj*);
}
obj* l_Lean_Parser_rawStr_viewDefault(obj*);
obj* l_String_OldIterator_next___main(obj*);
obj* l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbol(obj*);
obj* l_Lean_Parser_number_HasView_x27___elambda__1___closed__5;
obj* l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__1;
uint8 l_UInt32_decLe(uint32, uint32);
obj* l_Lean_Parser_rawIdent_Parser_View___rarg___boxed(obj*);
obj* l___private_init_lean_parser_token_5__mkConsumeToken(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentSuffix_HasView_x27___elambda__1___boxed(obj*);
obj* l_Lean_Parser_stringLit_x27___lambda__1___boxed(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Combinators_anyOf___rarg___closed__1;
obj* l_Lean_Parser_stringLit_Parser_View___rarg(obj*);
obj* l_Lean_Parser_raw___rarg___lambda__1(obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_raw_view___rarg___lambda__1(obj*);
obj* l_Lean_Parser_Syntax_mkNode(obj*, obj*);
obj* l_Lean_Parser_symbolCore(obj*);
obj* l_Lean_Parser_raw_view___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_7__toNatCore(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_stringLit_HasView_x27___elambda__1___boxed(obj*);
obj* l_Lean_Parser_ident_Parser___rarg(obj*);
obj* l_Lean_Parser_stringLit_Parser_View(obj*);
obj* l_Lean_Parser_asSubstring(obj*);
obj* l_Lean_Parser_RecT_recurse___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__7(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_updateLast(obj*, obj*, obj*);
namespace lean {
uint8 nat_dec_lt(obj*, obj*);
}
obj* l_Lean_Parser_parseOctLit___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasView___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_HasView_x27___elambda__1___closed__2;
obj* l_Lean_Parser_MonadParsec_whitespace___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens(obj*, obj*);
obj* l_Lean_Parser_asSubstring___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_longestMatch___at_Lean_Parser_number_x27___spec__6(obj*, obj*, obj*, obj*);
extern obj* l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
uint32 l_Char_ofNat(obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_parseOctLit___spec__3(uint32, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdent_Parser___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ident_Parser___rarg___closed__1;
extern obj* l_Char_HasRepr___closed__1;
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser___spec__1(obj*, obj*, uint32, obj*, obj*);
extern obj* l_Lean_Parser_noKind;
obj* l_Lean_Parser_ident_Parser_View___boxed(obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_4__ident_x27___spec__7___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_parseOctLit___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbol_View___rarg___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__5(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_matchToken___closed__1;
obj* l_Lean_Parser_whitespace___boxed(obj*, obj*, obj*);
extern "C" obj* lean_name_mk_string(obj*, obj*);
obj* l_Lean_Parser_rawIdent_Parser(obj*);
extern uint32 l_Lean_idBeginEscape;
obj* l_Lean_Parser_symbolOrIdent_tokens___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_HasView_x27;
obj* l_List_mfoldl___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__5(obj*, obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_Combinators_optional___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_rawIdent_Parser_View(obj*);
obj* l_Char_quoteCore(uint32);
obj* l_Lean_Parser_ParsecT_orelseMkRes___rarg(obj*, obj*);
uint8 l_String_OldIterator_hasNext___main(obj*);
obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__3(uint32, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens;
obj* l___private_init_lean_parser_token_4__ident_x27___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_2__whitespaceAux___main___closed__1;
namespace lean {
obj* nat_add(obj*, obj*);
}
obj* l_Lean_Parser_parseBinLit___closed__1;
obj* l_Lean_Parser_updateLast___main___at___private_init_lean_parser_token_3__updateTrailing___main___spec__1(obj*, obj*);
obj* l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2(obj*, obj*);
obj* l_Lean_Parser_detailIdentPart;
obj* l___private_init_lean_parser_token_8__toNatBase(obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at___private_init_lean_parser_token_4__ident_x27___spec__9___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolCore___rarg___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_tokens___rarg(obj*);
namespace lean {
uint8 nat_dec_eq(obj*, obj*);
}
obj* l_Lean_Parser_raw___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_ident_Parser_tokens___boxed(obj*, obj*);
obj* l_Lean_Parser_symbol_tokens___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_peekToken___closed__1;
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_token___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
uint8 l_UInt32_decLt(uint32, uint32);
obj* l_Lean_Parser_symbol___boxed(obj*);
obj* l_Lean_Parser_ParsecT_tryMkRes___rarg(obj*);
obj* l_Lean_Parser_raw_view___rarg___lambda__2___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__6___boxed(obj*);
obj* l_Lean_Parser_ident_Parser_View___rarg(obj*);
obj* l_Lean_Parser_idPart___at___private_init_lean_parser_token_4__ident_x27___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_Parser_view___rarg(obj*);
obj* l___private_init_lean_parser_parsec_6__mkConsumedResult___rarg(uint8, obj*);
obj* l_Lean_Parser_detailIdent;
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasView___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbol___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_parseHexLit(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__5___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile_x27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__5___boxed(obj*);
obj* l_Lean_Parser_detailIdent_HasView;
obj* l___private_init_lean_parser_token_3__updateTrailing___main(obj*, obj*);
obj* l_Lean_Parser_detailIdent_Parser___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__8(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolCore___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_Parser___closed__1;
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4(obj*);
obj* l_Lean_Parser_detailIdentPartEscaped;
obj* l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_List_mfoldl___main___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__9(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentSuffix_HasView;
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_peekToken___spec__1(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__3;
obj* l_Lean_Parser_symbolOrIdent_View(obj*);
obj* l_Lean_Parser_idPartEscaped___at___private_init_lean_parser_token_4__ident_x27___spec__5___boxed(obj*, obj*, obj*);
namespace lean {
uint8 string_dec_eq(obj*, obj*);
}
obj* l_List_mfoldr___main___at_Lean_Parser_number_x27___spec__9___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__3(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__6___rarg(obj*, obj*);
obj* l_Lean_Parser_number_Parser_view___rarg___closed__1;
obj* l_Lean_Parser_Combinators_seqRight_view___rarg(obj*, obj*, obj*, obj*, obj*, obj*);
uint8 l_UInt32_decEq(uint32, uint32);
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasView(obj*);
obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__1;
obj* l_Lean_Parser_updateLast___main(obj*, obj*);
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_rawIdent_Parser_View___rarg(obj*);
obj* l_Lean_Parser_finishCommentBlock___closed__1;
obj* l_Lean_Parser_MonadParsec_many1Aux_x27___main___at_Lean_Parser_parseBinLit___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_run___at_Lean_Parser_Parsec_parse___spec__1___rarg(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_x27___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_raw_tokens___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_stringLit_View_value___closed__1;
obj* l_Lean_Parser_symbol_View(obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_number_x27___spec__8(obj*);
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux(obj*, obj*, obj*, obj*, obj*);
uint8 l_Char_isDigit(uint32);
obj* l_Lean_Parser_number_Parser_view___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__2___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_stringLit_Parser_tokens___boxed(obj*, obj*);
obj* l_Lean_Parser_idPart___at___private_init_lean_parser_token_4__ident_x27___spec__1___boxed(obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_7__toNatCore___main(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_8__toNatBase___boxed(obj*, obj*);
obj* l_Lean_Parser_ident_Parser_View___rarg___boxed(obj*);
obj* l_Lean_Parser_stringLit_Parser___boxed(obj*);
obj* l_Lean_Parser_parseOctLit(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__3;
obj* l_Lean_Parser_withTrailing___rarg___lambda__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_Parser___rarg(obj*);
obj* l_Lean_Parser_number_HasView_x27___lambda__1___closed__5;
obj* l_Lean_Parser_detailIdent_Parser___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_String_trim(obj*);
obj* l_Lean_Parser_stringLit_x27___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_Parser(obj*);
obj* l_Lean_Parser_ParsecT_bindMkRes___rarg(obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__2;
obj* l_Lean_Parser_peekToken___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdent_Parser___closed__1;
obj* l_Lean_Parser_number_HasView_x27___lambda__1___closed__4;
obj* l_Lean_Parser_ident_Parser___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolOrIdent___rarg(obj*, obj*);
obj* l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens;
obj* l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__1(uint32, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_HasView_x27___elambda__1___closed__6;
obj* l_Lean_Parser_rawStr_Lean_Parser_HasView___rarg(obj*, obj*, obj*, obj*, uint8);
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__8(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_curr___at___private_init_lean_parser_token_4__ident_x27___spec__2___boxed(obj*);
obj* l_Lean_Parser_number_x27___lambda__3(obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_MonadParsec_longestMatch___rarg___lambda__2___closed__1;
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at___private_init_lean_parser_token_4__ident_x27___spec__9(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbol___rarg___boxed(obj*, obj*, obj*);
uint8 l_Lean_Name_quickLt(obj*, obj*);
obj* l_Lean_Parser_symbol_viewDefault___boxed(obj*);
obj* l___private_init_lean_parser_parsec_7__takeWhileAux_x27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__3___boxed(obj*, obj*, obj*);
obj* l_ReaderT_MonadExcept___rarg(obj*);
obj* l_Lean_Parser_ident_Parser_View(obj*);
obj* l_Lean_Parser_raw___rarg(obj*, obj*, obj*, obj*, obj*, uint8);
extern obj* l_Int_repr___main___closed__2;
extern "C" obj* lean_name_mk_numeral(obj*, obj*);
obj* l_Lean_Parser_detailIdent_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile_x27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__2___rarg(obj*, obj*);
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_parseHexLit___spec__3(obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasView___boxed(obj*);
extern obj* l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
obj* l_Lean_Parser_ident_Parser_View___rarg___lambda__1(obj*);
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x27___spec__4___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_token(obj*, obj*, obj*);
obj* l_Lean_Parser_rawStr___rarg(obj*, obj*, obj*, obj*, uint8);
obj* l_Lean_Parser_rawStr___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_2__whitespaceAux___main___closed__2;
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseHexLit___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_stringLit_Parser___rarg___lambda__1(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_List_cons_tokens___rarg(obj*, obj*);
obj* l_Lean_Parser_raw___rarg___lambda__3(uint8, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_withTrailing___at_Lean_Parser_token___spec__3___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_View_ofNat(obj*);
uint8 l_Char_isWhitespace(uint32);
obj* l_Lean_Parser_number_x27(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1(uint32, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__2;
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__4;
obj* l_Lean_Parser_detailIdent_Parser(obj*, obj*, obj*);
obj* l_Lean_Parser_peekToken(obj*, obj*, obj*);
obj* l_Lean_Parser_number_HasView_x27___elambda__1___closed__4;
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__5___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1(obj*);
obj* l_Lean_Parser_detailIdentSuffix_Parser___closed__1;
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__3___rarg___boxed(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_number_x27___spec__1___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentSuffix_HasView_x27___elambda__2___closed__1;
obj* l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6___boxed(obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__4___rarg(obj*, obj*);
obj* l_Lean_Parser_number_HasView_x27;
obj* l_Lean_Parser_MonadParsec_strCore___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolCore___rarg___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x27___spec__4(obj*);
obj* l_Lean_Parser_rawStr___boxed(obj*);
obj* l_Lean_Parser_symbolOrIdent_View___rarg(obj*, obj*);
obj* l_Lean_Parser_withTrailing___boxed(obj*);
obj* l_Lean_Parser_number_HasView_x27___lambda__1___closed__6;
obj* l_Lean_Parser_MonadParsec_takeWhile_x27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__5___rarg(obj*, obj*);
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x27___lambda__1___closed__1;
obj* l_Lean_Parser_detailIdentPart_HasView;
obj* l_Lean_Parser_number_x27___lambda__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_parseQuotedChar___at_Lean_Parser_stringLit_View_value___spec__6(obj*);
extern uint8 l_True_Decidable;
obj* l_Lean_Parser_MonadParsec_observing___at_Lean_Parser_token___spec__2(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_indexed(obj*);
obj* l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5(obj*, obj*, obj*);
obj* l_ReaderT_orelse___at_Lean_Parser_parseBinLit___spec__1(obj*);
extern obj* l_Lean_Name_toString___closed__1;
obj* l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_number_HasView_x27___lambda__1___closed__3;
namespace lean {
uint8 nat_dec_le(obj*, obj*);
}
obj* l___private_init_lean_parser_token_2__whitespaceAux___main___closed__3;
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux___main___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_ReaderT_Alternative___rarg(obj*, obj*);
obj* l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__2(obj*, obj*, obj*);
obj* l_List_map___main___at_Lean_Parser_number_x27___spec__5___lambda__1(obj*, obj*, obj*, obj*);
obj* l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4___rarg(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x27___spec__4___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2___rarg(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_parsec_7__takeWhileAux_x27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__3(obj*, uint8, obj*);
obj* l_Lean_Parser_raw___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdent_Parser___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__3;
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_detailIdent_x27___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_rawIdent_Parser___boxed(obj*);
namespace lean {
obj* uint32_to_nat(uint32);
}
obj* l_Lean_Parser_number_HasView_x27___elambda__1___boxed(obj*);
obj* l_Lean_Parser_tryView___at_Lean_Parser_stringLit_Parser___spec__1___boxed(obj*, obj*);
obj* l_Lean_Parser_number_Parser___boxed(obj*);
obj* l_Lean_Parser_raw_tokens(obj*, obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_token___closed__2;
obj* l_Lean_Parser_ident_Parser_View___rarg___lambda__1___boxed(obj*);
obj* l_Lean_Parser_rawStr_viewDefault___rarg(obj*, obj*, obj*, obj*, uint8);
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__3(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_unicodeSymbol_viewDefault(obj*);
obj* l_Lean_Parser_unicodeSymbol_viewDefault___boxed(obj*);
obj* l_Lean_Parser_ident_Parser_View___rarg___closed__2;
obj* l_Lean_Parser_stringLit_HasView;
obj* l_Lean_Parser_detailIdentSuffix_HasView_x27;
extern uint32 l_Lean_idEndEscape;
obj* l_Lean_Parser_detailIdent_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_Combinators_longestChoice___at_Lean_Parser_number_x27___spec__4(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_x27___lambda__4(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentSuffix;
obj* l_Lean_Parser_asSubstring___rarg___lambda__2(obj*, obj*, obj*, obj*, obj*);
obj* l_List_foldl___main___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__3(obj*, obj*, obj*, obj*, obj*);
obj* l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_idPartDefault___at___private_init_lean_parser_token_4__ident_x27___spec__3___boxed(obj*, obj*, obj*);
obj* l_String_quote(obj*);
obj* l_Lean_Parser_number_x27___lambda__3___boxed(obj*, obj*, obj*, obj*);
obj* l___private_init_lean_parser_token_7__toNatCore___main___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_withTrailing___rarg___lambda__2___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbol_tokens___boxed(obj*, obj*);
obj* l_Lean_Parser_detailIdent_HasView_x27;
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_View_value___spec__7(obj*);
obj* l_Lean_Parser_parseHexLit___boxed(obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_withTrailing___rarg___closed__1;
obj* l_Lean_Parser_tokenCont___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__4(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentSuffix_HasView_x27___elambda__1(obj*);
obj* l_Lean_Parser_indexed___boxed(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhile_x27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__5(obj*);
obj* l_Lean_Parser_Substring_ofString(obj*);
obj* l_Lean_Parser_stringLit_HasView_x27;
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__1(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_symbolOrIdent_tokens(obj*, obj*, obj*);
obj* l_Lean_Parser_idPartEscaped___at___private_init_lean_parser_token_4__ident_x27___spec__5(obj*, obj*, obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseHexLit___spec__2(obj*, obj*, obj*, obj*);
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__5(obj*);
extern obj* l_Lean_Parser_BasicParserM_MonadExcept;
obj* l_Lean_Parser_asSubstring___rarg___lambda__1(obj*, obj*, obj*);
obj* l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed(obj*, obj*, obj*, obj*, obj*);
extern obj* l_Lean_Parser_ParsecT_failure___rarg___closed__1;
uint8 l_Lean_isIdFirst(uint32);
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__1(obj*);
namespace lean {
obj* nat_mul(obj*, obj*);
}
extern obj* l_Lean_Parser_Combinators_many___rarg___closed__1;
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseOctLit___spec__2___boxed(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_Parser_tokens___boxed(obj*, obj*);
obj* l_Lean_Parser_symbol(obj*);
obj* l_Lean_Parser_unicodeSymbol_viewDefault___rarg(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___spec__1(uint32, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_rawIdent_Parser___rarg(obj*);
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseOctLit___spec__2(uint32, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_stringLit_Parser_View___rarg___closed__1;
obj* l___private_init_lean_parser_token_2__whitespaceAux___main___closed__4;
obj* l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__1;
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_detailIdent_x27___spec__1(obj*, uint8, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_raw___rarg___lambda__1___boxed(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_HasView_x27___lambda__1(obj*);
obj* l_Lean_Parser_withTrailing(obj*);
obj* l_Lean_Parser_rawStr_Lean_Parser_HasTokens(obj*, obj*, obj*, obj*, obj*, uint8);
obj* l_Lean_Parser_parseStringLiteral___at_Lean_Parser_stringLit_View_value___spec__1(obj*);
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__3(obj*);
obj* l_Lean_Parser_MonadParsec_digit___at_Lean_Parser_stringLit_x27___spec__6(obj*, obj*, obj*);
obj* l_Lean_Parser_number_HasView_x27___elambda__1(obj*);
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__2;
obj* l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_stringLit_View_value___spec__2___boxed(obj*, obj*);
obj* l_Lean_Parser_number_View_toNat___main(obj*);
obj* l_Lean_Parser_number_View_toNat(obj*);
obj* l_Lean_Parser_number_x27___lambda__1___boxed(obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__2(obj*, obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_Parser___rarg___lambda__1___closed__1;
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_token___spec__1(obj*, obj*, obj*, obj*, obj*);
obj* l_Lean_Parser_number_Parser___rarg___lambda__1(obj*, obj*, obj*);
obj* l_Lean_Parser_parseBinLit(obj*, obj*, obj*);
obj* l_Lean_Parser_stringLit_Parser___rarg___closed__1;
extern obj* l_String_splitAux___main___closed__1;
obj* l_Lean_Parser_MonadParsec_any___at_Lean_Parser_stringLit_View_value___spec__5(obj*);
namespace lean {
obj* string_length(obj*);
}
obj* l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1(obj*);
obj* _init_l_Lean_Parser_matchToken___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
lean::inc(x_1, 2);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_2, 0, x_1);
lean::closure_set(x_2, 1, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
obj* l_Lean_Parser_matchToken(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = lean::cnstr_get(x_1, 1);
lean::inc(x_4);
lean::dec(x_1);
lean::inc(x_2);
x_5 = l_Lean_Parser_Trie_oldMatchPrefix___rarg(x_4, x_2);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_5);
x_6 = lean::box(0);
x_7 = l_Lean_Parser_matchToken___closed__1;
x_8 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_2);
lean::cnstr_set(x_8, 2, x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_3);
return x_9;
}
else
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_5);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_11 = lean::cnstr_get(x_5, 0);
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
lean::dec(x_11);
lean::cnstr_set(x_5, 0, x_12);
x_13 = l_Lean_Parser_matchToken___closed__1;
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_2);
lean::cnstr_set(x_14, 2, x_13);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_14);
lean::cnstr_set(x_15, 1, x_3);
return x_15;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_16 = lean::cnstr_get(x_5, 0);
lean::inc(x_16);
lean::dec(x_5);
x_17 = lean::cnstr_get(x_16, 1);
lean::inc(x_17);
lean::dec(x_16);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
x_19 = l_Lean_Parser_matchToken___closed__1;
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_2);
lean::cnstr_set(x_20, 2, x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_3);
return x_21;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_8; uint8 x_9; obj* x_10; obj* x_11; 
x_8 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_1);
lean::cnstr_set(x_8, 2, x_2);
lean::cnstr_set(x_8, 3, x_4);
x_9 = 0;
x_10 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set_scalar(x_10, sizeof(void*)*1, x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_7);
return x_11;
}
else
{
obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; 
lean::dec(x_6);
x_12 = lean::cnstr_get(x_3, 0);
lean::inc(x_12);
x_13 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_1);
lean::cnstr_set(x_13, 2, x_2);
lean::cnstr_set(x_13, 3, x_4);
x_14 = 0;
x_15 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set_scalar(x_15, sizeof(void*)*1, x_14);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_7);
return x_16;
}
}
}
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg___boxed), 7, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__2(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_String_OldIterator_hasNext___main(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_5 = lean::box(0);
x_6 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_7 = l_mjoin___rarg___closed__1;
x_8 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_6, x_7, x_5, x_5, x_1, x_2, x_3);
x_9 = !lean::is_exclusive(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_8, 0);
x_11 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_12 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_10);
lean::cnstr_set(x_8, 0, x_12);
return x_8;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_13 = lean::cnstr_get(x_8, 0);
x_14 = lean::cnstr_get(x_8, 1);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_8);
x_15 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_16 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_13);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_14);
return x_17;
}
}
else
{
uint32 x_18; uint8 x_19; 
x_18 = l_String_OldIterator_curr___main(x_2);
x_19 = l_True_Decidable;
if (x_19 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; uint8 x_27; 
x_20 = l_Char_quoteCore(x_18);
x_21 = l_Char_HasRepr___closed__1;
x_22 = lean::string_append(x_21, x_20);
lean::dec(x_20);
x_23 = lean::string_append(x_22, x_21);
x_24 = lean::box(0);
x_25 = l_mjoin___rarg___closed__1;
x_26 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_23, x_25, x_24, x_24, x_1, x_2, x_3);
x_27 = !lean::is_exclusive(x_26);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = lean::cnstr_get(x_26, 0);
x_29 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_30 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_29, x_28);
lean::cnstr_set(x_26, 0, x_30);
return x_26;
}
else
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_31 = lean::cnstr_get(x_26, 0);
x_32 = lean::cnstr_get(x_26, 1);
lean::inc(x_32);
lean::inc(x_31);
lean::dec(x_26);
x_33 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_34 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_33, x_31);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_32);
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_36 = l_String_OldIterator_next___main(x_2);
x_37 = lean::box(0);
x_38 = lean::box_uint32(x_18);
x_39 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_36);
lean::cnstr_set(x_39, 2, x_37);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_3);
return x_40;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = l_String_isEmpty(x_1);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::string_length(x_1);
x_8 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_1);
lean::cnstr_set(x_9, 1, x_8);
lean::cnstr_set(x_9, 2, x_8);
lean::inc(x_4);
x_10 = l___private_init_lean_parser_parsec_2__strAux___main(x_7, x_9, x_4);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; 
lean::dec(x_10);
lean::dec(x_1);
x_11 = lean::box(0);
x_12 = l_String_splitAux___main___closed__1;
x_13 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_13, 0, x_4);
lean::cnstr_set(x_13, 1, x_12);
lean::cnstr_set(x_13, 2, x_2);
lean::cnstr_set(x_13, 3, x_11);
x_14 = 0;
x_15 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set_scalar(x_15, sizeof(void*)*1, x_14);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_5);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
lean::dec(x_4);
lean::dec(x_2);
x_17 = lean::cnstr_get(x_10, 0);
lean::inc(x_17);
lean::dec(x_10);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_19, 0, x_1);
lean::cnstr_set(x_19, 1, x_17);
lean::cnstr_set(x_19, 2, x_18);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_5);
return x_20;
}
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
lean::dec(x_2);
lean::dec(x_1);
x_21 = l_String_splitAux___main___closed__1;
x_22 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_4);
lean::cnstr_set(x_23, 2, x_22);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_5);
return x_24;
}
}
}
obj* _init_l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("-/");
return x_1;
}
}
obj* _init_l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_string("-/");
x_2 = l_String_quote(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("/-");
return x_1;
}
}
obj* _init_l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_string("/-");
x_2 = l_String_quote(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_2, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_93; obj* x_94; obj* x_95; obj* x_96; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_2, x_8);
x_10 = lean::nat_add(x_1, x_8);
x_11 = lean::nat_dec_eq(x_1, x_8);
x_93 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__3;
x_94 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__4;
lean::inc(x_4);
x_95 = l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3(x_93, x_94, x_3, x_4, x_5);
x_96 = lean::cnstr_get(x_95, 0);
lean::inc(x_96);
if (lean::obj_tag(x_96) == 0)
{
obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; 
x_97 = lean::cnstr_get(x_95, 1);
lean::inc(x_97);
lean::dec(x_95);
x_98 = lean::cnstr_get(x_96, 1);
lean::inc(x_98);
x_99 = lean::cnstr_get(x_96, 2);
lean::inc(x_99);
lean::dec(x_96);
x_100 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main(x_10, x_9, x_3, x_98, x_97);
lean::dec(x_10);
x_101 = lean::cnstr_get(x_100, 0);
lean::inc(x_101);
x_102 = lean::cnstr_get(x_100, 1);
lean::inc(x_102);
lean::dec(x_100);
x_103 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_99, x_101);
x_12 = x_103;
x_13 = x_102;
goto block_92;
}
else
{
obj* x_104; uint8 x_105; 
lean::dec(x_10);
x_104 = lean::cnstr_get(x_95, 1);
lean::inc(x_104);
lean::dec(x_95);
x_105 = !lean::is_exclusive(x_96);
if (x_105 == 0)
{
x_12 = x_96;
x_13 = x_104;
goto block_92;
}
else
{
obj* x_106; uint8 x_107; obj* x_108; 
x_106 = lean::cnstr_get(x_96, 0);
x_107 = lean::cnstr_get_scalar<uint8>(x_96, sizeof(void*)*1);
lean::inc(x_106);
lean::dec(x_96);
x_108 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_108, 0, x_106);
lean::cnstr_set_scalar(x_108, sizeof(void*)*1, x_107);
x_12 = x_108;
x_13 = x_104;
goto block_92;
}
}
block_92:
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; 
lean::dec(x_9);
lean::dec(x_4);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
else
{
obj* x_15; uint8 x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_12, 0);
lean::inc(x_15);
x_16 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (x_16 == 0)
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_12);
x_61 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__1;
x_62 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__2;
lean::inc(x_4);
x_63 = l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3(x_61, x_62, x_3, x_4, x_13);
x_64 = lean::cnstr_get(x_63, 0);
lean::inc(x_64);
if (lean::obj_tag(x_64) == 0)
{
if (x_11 == 0)
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; 
x_65 = lean::cnstr_get(x_63, 1);
lean::inc(x_65);
lean::dec(x_63);
x_66 = lean::cnstr_get(x_64, 1);
lean::inc(x_66);
x_67 = lean::cnstr_get(x_64, 2);
lean::inc(x_67);
lean::dec(x_64);
x_68 = lean::nat_sub(x_1, x_8);
x_69 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main(x_68, x_9, x_3, x_66, x_65);
lean::dec(x_68);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_69, 1);
lean::inc(x_71);
lean::dec(x_69);
x_72 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_67, x_70);
x_17 = x_72;
x_18 = x_71;
goto block_60;
}
else
{
obj* x_73; uint8 x_74; 
x_73 = lean::cnstr_get(x_63, 1);
lean::inc(x_73);
lean::dec(x_63);
x_74 = !lean::is_exclusive(x_64);
if (x_74 == 0)
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
x_75 = lean::cnstr_get(x_64, 2);
x_76 = lean::cnstr_get(x_64, 0);
lean::dec(x_76);
x_77 = lean::box(0);
x_78 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_64, 2, x_78);
lean::cnstr_set(x_64, 0, x_77);
x_79 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_75, x_64);
x_17 = x_79;
x_18 = x_73;
goto block_60;
}
else
{
obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_80 = lean::cnstr_get(x_64, 1);
x_81 = lean::cnstr_get(x_64, 2);
lean::inc(x_81);
lean::inc(x_80);
lean::dec(x_64);
x_82 = lean::box(0);
x_83 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_84 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_84, 0, x_82);
lean::cnstr_set(x_84, 1, x_80);
lean::cnstr_set(x_84, 2, x_83);
x_85 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_81, x_84);
x_17 = x_85;
x_18 = x_73;
goto block_60;
}
}
}
else
{
obj* x_86; uint8 x_87; 
x_86 = lean::cnstr_get(x_63, 1);
lean::inc(x_86);
lean::dec(x_63);
x_87 = !lean::is_exclusive(x_64);
if (x_87 == 0)
{
x_17 = x_64;
x_18 = x_86;
goto block_60;
}
else
{
obj* x_88; uint8 x_89; obj* x_90; 
x_88 = lean::cnstr_get(x_64, 0);
x_89 = lean::cnstr_get_scalar<uint8>(x_64, sizeof(void*)*1);
lean::inc(x_88);
lean::dec(x_64);
x_90 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_90, 0, x_88);
lean::cnstr_set_scalar(x_90, sizeof(void*)*1, x_89);
x_17 = x_90;
x_18 = x_86;
goto block_60;
}
}
}
else
{
obj* x_91; 
lean::dec(x_15);
lean::dec(x_9);
lean::dec(x_4);
x_91 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_91, 0, x_12);
lean::cnstr_set(x_91, 1, x_13);
return x_91;
}
block_60:
{
if (lean::obj_tag(x_17) == 0)
{
obj* x_19; obj* x_20; 
lean::dec(x_9);
lean::dec(x_4);
x_19 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_15, x_17);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
return x_20;
}
else
{
uint8 x_21; 
x_21 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*1);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = lean::cnstr_get(x_17, 0);
lean::inc(x_22);
lean::dec(x_17);
x_23 = l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__2(x_3, x_4, x_18);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
if (lean::obj_tag(x_24) == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; uint8 x_29; 
x_25 = lean::cnstr_get(x_23, 1);
lean::inc(x_25);
lean::dec(x_23);
x_26 = lean::cnstr_get(x_24, 1);
lean::inc(x_26);
x_27 = lean::cnstr_get(x_24, 2);
lean::inc(x_27);
lean::dec(x_24);
x_28 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main(x_1, x_9, x_3, x_26, x_25);
lean::dec(x_9);
x_29 = !lean::is_exclusive(x_28);
if (x_29 == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_30 = lean::cnstr_get(x_28, 0);
x_31 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_27, x_30);
x_32 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_22, x_31);
x_33 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_15, x_32);
lean::cnstr_set(x_28, 0, x_33);
return x_28;
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_34 = lean::cnstr_get(x_28, 0);
x_35 = lean::cnstr_get(x_28, 1);
lean::inc(x_35);
lean::inc(x_34);
lean::dec(x_28);
x_36 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_27, x_34);
x_37 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_22, x_36);
x_38 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_15, x_37);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_35);
return x_39;
}
}
else
{
uint8 x_40; 
lean::dec(x_9);
x_40 = !lean::is_exclusive(x_23);
if (x_40 == 0)
{
obj* x_41; uint8 x_42; 
x_41 = lean::cnstr_get(x_23, 0);
lean::dec(x_41);
x_42 = !lean::is_exclusive(x_24);
if (x_42 == 0)
{
obj* x_43; obj* x_44; 
x_43 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_22, x_24);
x_44 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_15, x_43);
lean::cnstr_set(x_23, 0, x_44);
return x_23;
}
else
{
obj* x_45; uint8 x_46; obj* x_47; obj* x_48; obj* x_49; 
x_45 = lean::cnstr_get(x_24, 0);
x_46 = lean::cnstr_get_scalar<uint8>(x_24, sizeof(void*)*1);
lean::inc(x_45);
lean::dec(x_24);
x_47 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set_scalar(x_47, sizeof(void*)*1, x_46);
x_48 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_22, x_47);
x_49 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_15, x_48);
lean::cnstr_set(x_23, 0, x_49);
return x_23;
}
}
else
{
obj* x_50; obj* x_51; uint8 x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_50 = lean::cnstr_get(x_23, 1);
lean::inc(x_50);
lean::dec(x_23);
x_51 = lean::cnstr_get(x_24, 0);
lean::inc(x_51);
x_52 = lean::cnstr_get_scalar<uint8>(x_24, sizeof(void*)*1);
if (lean::is_exclusive(x_24)) {
 lean::cnstr_release(x_24, 0);
 x_53 = x_24;
} else {
 lean::dec_ref(x_24);
 x_53 = lean::box(0);
}
if (lean::is_scalar(x_53)) {
 x_54 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_54 = x_53;
}
lean::cnstr_set(x_54, 0, x_51);
lean::cnstr_set_scalar(x_54, sizeof(void*)*1, x_52);
x_55 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_22, x_54);
x_56 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_15, x_55);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_50);
return x_57;
}
}
}
else
{
obj* x_58; obj* x_59; 
lean::dec(x_9);
lean::dec(x_4);
x_58 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_15, x_17);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_18);
return x_59;
}
}
}
}
}
}
else
{
obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_109 = lean::box(0);
x_110 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
x_111 = l_mjoin___rarg___closed__1;
x_112 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_110, x_111, x_109, x_109, x_3, x_4, x_5);
return x_112;
}
}
}
obj* l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; 
x_8 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean::dec(x_5);
lean::dec(x_3);
return x_8;
}
}
obj* l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__2(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
return x_6;
}
}
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main(x_1, x_2, x_3, x_4, x_5);
return x_6;
}
}
obj* l___private_init_lean_parser_token_1__finishCommentBlockAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_parser_token_1__finishCommentBlockAux(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_6;
}
}
obj* _init_l_Lean_Parser_finishCommentBlock___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("end of comment block");
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_finishCommentBlock___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
lean::inc(x_1);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_2, 0, x_1);
lean::closure_set(x_2, 1, x_1);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_Lean_Parser_finishCommentBlock(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_5 = l_String_OldIterator_remaining___main(x_3);
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_add(x_5, x_6);
lean::dec(x_5);
x_8 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main(x_1, x_7, x_2, x_3, x_4);
lean::dec(x_7);
x_9 = !lean::is_exclusive(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_8, 0);
x_11 = l_Lean_Parser_finishCommentBlock___closed__1;
x_12 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_10, x_11);
x_13 = l_Lean_Parser_finishCommentBlock___closed__2;
x_14 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_12);
lean::cnstr_set(x_8, 0, x_14);
return x_8;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_15 = lean::cnstr_get(x_8, 0);
x_16 = lean::cnstr_get(x_8, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_8);
x_17 = l_Lean_Parser_finishCommentBlock___closed__1;
x_18 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_15, x_17);
x_19 = l_Lean_Parser_finishCommentBlock___closed__2;
x_20 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_19, x_18);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_16);
return x_21;
}
}
}
obj* l_Lean_Parser_finishCommentBlock___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_finishCommentBlock(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l___private_init_lean_parser_parsec_7__takeWhileAux_x27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__3(obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_1);
x_8 = l_String_OldIterator_hasNext___main(x_3);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_7);
x_9 = l___private_init_lean_parser_parsec_6__mkConsumedResult___rarg(x_2, x_3);
return x_9;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = l_String_OldIterator_curr___main(x_3);
x_11 = l_Char_isWhitespace(x_10);
if (x_11 == 0)
{
obj* x_12; 
lean::dec(x_7);
x_12 = l___private_init_lean_parser_parsec_6__mkConsumedResult___rarg(x_2, x_3);
return x_12;
}
else
{
obj* x_13; uint8 x_14; obj* x_15; 
x_13 = l_String_OldIterator_next___main(x_3);
x_14 = 1;
x_1 = x_7;
x_2 = x_14;
x_3 = x_13;
goto _start;
}
}
}
else
{
obj* x_16; 
lean::dec(x_1);
x_16 = l___private_init_lean_parser_parsec_6__mkConsumedResult___rarg(x_2, x_3);
return x_16;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile_x27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__2___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; obj* x_5; obj* x_6; 
x_3 = l_String_OldIterator_remaining___main(x_1);
x_4 = 0;
x_5 = l___private_init_lean_parser_parsec_7__takeWhileAux_x27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__3(x_3, x_4, x_1);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile_x27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile_x27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__2___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_whitespace___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhile_x27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__2___rarg(x_2, x_3);
return x_4;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__4(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = l_Int_repr___main___closed__2;
lean::inc(x_4);
x_7 = l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3(x_6, x_2, x_1, x_4, x_5);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_7);
if (x_9 == 0)
{
obj* x_10; uint8 x_11; 
x_10 = lean::cnstr_get(x_7, 0);
lean::dec(x_10);
x_11 = !lean::is_exclusive(x_8);
if (x_11 == 0)
{
obj* x_12; obj* x_13; uint8 x_14; obj* x_15; obj* x_16; 
x_12 = lean::cnstr_get(x_8, 2);
x_13 = lean::cnstr_get(x_8, 0);
lean::dec(x_13);
x_14 = 0;
x_15 = lean::box(x_14);
lean::cnstr_set(x_8, 2, x_3);
lean::cnstr_set(x_8, 0, x_15);
x_16 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_8);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::cnstr_get(x_16, 2);
lean::dec(x_18);
x_19 = lean::cnstr_get(x_16, 1);
lean::dec(x_19);
x_20 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_16, 2, x_20);
lean::cnstr_set(x_16, 1, x_4);
lean::cnstr_set(x_7, 0, x_16);
return x_7;
}
else
{
obj* x_21; obj* x_22; obj* x_23; 
x_21 = lean::cnstr_get(x_16, 0);
lean::inc(x_21);
lean::dec(x_16);
x_22 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_4);
lean::cnstr_set(x_23, 2, x_22);
lean::cnstr_set(x_7, 0, x_23);
return x_7;
}
}
else
{
uint8 x_24; obj* x_25; obj* x_26; obj* x_27; 
lean::dec(x_16);
x_24 = 1;
x_25 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_26 = lean::box(x_24);
x_27 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_4);
lean::cnstr_set(x_27, 2, x_25);
lean::cnstr_set(x_7, 0, x_27);
return x_7;
}
}
else
{
obj* x_28; obj* x_29; uint8 x_30; obj* x_31; obj* x_32; obj* x_33; 
x_28 = lean::cnstr_get(x_8, 1);
x_29 = lean::cnstr_get(x_8, 2);
lean::inc(x_29);
lean::inc(x_28);
lean::dec(x_8);
x_30 = 0;
x_31 = lean::box(x_30);
x_32 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_28);
lean::cnstr_set(x_32, 2, x_3);
x_33 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_29, x_32);
if (lean::obj_tag(x_33) == 0)
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
if (lean::is_exclusive(x_33)) {
 lean::cnstr_release(x_33, 0);
 lean::cnstr_release(x_33, 1);
 lean::cnstr_release(x_33, 2);
 x_35 = x_33;
} else {
 lean::dec_ref(x_33);
 x_35 = lean::box(0);
}
x_36 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_35)) {
 x_37 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_37 = x_35;
}
lean::cnstr_set(x_37, 0, x_34);
lean::cnstr_set(x_37, 1, x_4);
lean::cnstr_set(x_37, 2, x_36);
lean::cnstr_set(x_7, 0, x_37);
return x_7;
}
else
{
uint8 x_38; obj* x_39; obj* x_40; obj* x_41; 
lean::dec(x_33);
x_38 = 1;
x_39 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_40 = lean::box(x_38);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_4);
lean::cnstr_set(x_41, 2, x_39);
lean::cnstr_set(x_7, 0, x_41);
return x_7;
}
}
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; uint8 x_46; obj* x_47; obj* x_48; obj* x_49; 
x_42 = lean::cnstr_get(x_7, 1);
lean::inc(x_42);
lean::dec(x_7);
x_43 = lean::cnstr_get(x_8, 1);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_8, 2);
lean::inc(x_44);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 x_45 = x_8;
} else {
 lean::dec_ref(x_8);
 x_45 = lean::box(0);
}
x_46 = 0;
x_47 = lean::box(x_46);
if (lean::is_scalar(x_45)) {
 x_48 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_48 = x_45;
}
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_43);
lean::cnstr_set(x_48, 2, x_3);
x_49 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_44, x_48);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 lean::cnstr_release(x_49, 2);
 x_51 = x_49;
} else {
 lean::dec_ref(x_49);
 x_51 = lean::box(0);
}
x_52 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_51)) {
 x_53 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_53 = x_51;
}
lean::cnstr_set(x_53, 0, x_50);
lean::cnstr_set(x_53, 1, x_4);
lean::cnstr_set(x_53, 2, x_52);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_42);
return x_54;
}
else
{
uint8 x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_49);
x_55 = 1;
x_56 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_57 = lean::box(x_55);
x_58 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_4);
lean::cnstr_set(x_58, 2, x_56);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_42);
return x_59;
}
}
}
else
{
uint8 x_60; 
lean::dec(x_8);
lean::dec(x_3);
x_60 = !lean::is_exclusive(x_7);
if (x_60 == 0)
{
obj* x_61; uint8 x_62; obj* x_63; obj* x_64; obj* x_65; 
x_61 = lean::cnstr_get(x_7, 0);
lean::dec(x_61);
x_62 = 1;
x_63 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_64 = lean::box(x_62);
x_65 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_4);
lean::cnstr_set(x_65, 2, x_63);
lean::cnstr_set(x_7, 0, x_65);
return x_7;
}
else
{
obj* x_66; uint8 x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_66 = lean::cnstr_get(x_7, 1);
lean::inc(x_66);
lean::dec(x_7);
x_67 = 1;
x_68 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_69 = lean::box(x_67);
x_70 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_4);
lean::cnstr_set(x_70, 2, x_68);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_66);
return x_71;
}
}
}
}
obj* l___private_init_lean_parser_parsec_7__takeWhileAux_x27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__6(obj* x_1, uint8 x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_1);
x_8 = l_String_OldIterator_hasNext___main(x_3);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_7);
x_9 = l___private_init_lean_parser_parsec_6__mkConsumedResult___rarg(x_2, x_3);
return x_9;
}
else
{
uint32 x_10; uint32 x_11; uint8 x_12; 
x_10 = l_String_OldIterator_curr___main(x_3);
x_11 = 10;
x_12 = x_10 == x_11;
if (x_12 == 0)
{
obj* x_13; uint8 x_14; obj* x_15; 
x_13 = l_String_OldIterator_next___main(x_3);
x_14 = 1;
x_1 = x_7;
x_2 = x_14;
x_3 = x_13;
goto _start;
}
else
{
obj* x_16; 
lean::dec(x_7);
x_16 = l___private_init_lean_parser_parsec_6__mkConsumedResult___rarg(x_2, x_3);
return x_16;
}
}
}
else
{
obj* x_17; 
lean::dec(x_1);
x_17 = l___private_init_lean_parser_parsec_6__mkConsumedResult___rarg(x_2, x_3);
return x_17;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile_x27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__5___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; uint8 x_4; obj* x_5; obj* x_6; 
x_3 = l_String_OldIterator_remaining___main(x_1);
x_4 = 0;
x_5 = l___private_init_lean_parser_parsec_7__takeWhileAux_x27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__6(x_3, x_4, x_1);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile_x27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__5(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile_x27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__5___rarg), 2, 0);
return x_2;
}
}
obj* _init_l___private_init_lean_parser_token_2__whitespaceAux___main___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_string("-");
x_2 = l_String_quote(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
return x_3;
}
}
obj* _init_l___private_init_lean_parser_token_2__whitespaceAux___main___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("input");
return x_1;
}
}
obj* _init_l___private_init_lean_parser_token_2__whitespaceAux___main___closed__3() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("--");
return x_1;
}
}
obj* _init_l___private_init_lean_parser_token_2__whitespaceAux___main___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_string("--");
x_2 = l_String_quote(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
return x_3;
}
}
obj* l___private_init_lean_parser_token_2__whitespaceAux___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_1, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_1, x_7);
x_9 = l_Lean_Parser_MonadParsec_whitespace___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__1(x_2, x_3, x_4);
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_303; obj* x_304; obj* x_305; obj* x_306; 
x_11 = lean::cnstr_get(x_9, 1);
lean::inc(x_11);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 x_12 = x_9;
} else {
 lean::dec_ref(x_9);
 x_12 = lean::box(0);
}
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
x_14 = lean::cnstr_get(x_10, 2);
lean::inc(x_14);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 lean::cnstr_release(x_10, 1);
 lean::cnstr_release(x_10, 2);
 x_15 = x_10;
} else {
 lean::dec_ref(x_10);
 x_15 = lean::box(0);
}
x_303 = l___private_init_lean_parser_token_2__whitespaceAux___main___closed__3;
x_304 = l___private_init_lean_parser_token_2__whitespaceAux___main___closed__4;
lean::inc(x_13);
x_305 = l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3(x_303, x_304, x_2, x_13, x_11);
x_306 = lean::cnstr_get(x_305, 0);
lean::inc(x_306);
if (lean::obj_tag(x_306) == 0)
{
obj* x_307; obj* x_308; obj* x_309; obj* x_310; obj* x_311; 
x_307 = lean::cnstr_get(x_305, 1);
lean::inc(x_307);
lean::dec(x_305);
x_308 = lean::cnstr_get(x_306, 1);
lean::inc(x_308);
x_309 = lean::cnstr_get(x_306, 2);
lean::inc(x_309);
lean::dec(x_306);
x_310 = l_Lean_Parser_MonadParsec_takeWhile_x27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__5___rarg(x_308, x_307);
x_311 = lean::cnstr_get(x_310, 0);
lean::inc(x_311);
if (lean::obj_tag(x_311) == 0)
{
obj* x_312; obj* x_313; obj* x_314; obj* x_315; obj* x_316; obj* x_317; obj* x_318; obj* x_319; 
x_312 = lean::cnstr_get(x_310, 1);
lean::inc(x_312);
lean::dec(x_310);
x_313 = lean::cnstr_get(x_311, 1);
lean::inc(x_313);
x_314 = lean::cnstr_get(x_311, 2);
lean::inc(x_314);
lean::dec(x_311);
x_315 = l___private_init_lean_parser_token_2__whitespaceAux___main(x_8, x_2, x_313, x_312);
x_316 = lean::cnstr_get(x_315, 0);
lean::inc(x_316);
x_317 = lean::cnstr_get(x_315, 1);
lean::inc(x_317);
lean::dec(x_315);
x_318 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_314, x_316);
x_319 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_309, x_318);
x_16 = x_319;
x_17 = x_317;
goto block_302;
}
else
{
obj* x_320; uint8 x_321; 
x_320 = lean::cnstr_get(x_310, 1);
lean::inc(x_320);
lean::dec(x_310);
x_321 = !lean::is_exclusive(x_311);
if (x_321 == 0)
{
obj* x_322; 
x_322 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_309, x_311);
x_16 = x_322;
x_17 = x_320;
goto block_302;
}
else
{
obj* x_323; uint8 x_324; obj* x_325; obj* x_326; 
x_323 = lean::cnstr_get(x_311, 0);
x_324 = lean::cnstr_get_scalar<uint8>(x_311, sizeof(void*)*1);
lean::inc(x_323);
lean::dec(x_311);
x_325 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_325, 0, x_323);
lean::cnstr_set_scalar(x_325, sizeof(void*)*1, x_324);
x_326 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_309, x_325);
x_16 = x_326;
x_17 = x_320;
goto block_302;
}
}
}
else
{
obj* x_327; uint8 x_328; 
x_327 = lean::cnstr_get(x_305, 1);
lean::inc(x_327);
lean::dec(x_305);
x_328 = !lean::is_exclusive(x_306);
if (x_328 == 0)
{
x_16 = x_306;
x_17 = x_327;
goto block_302;
}
else
{
obj* x_329; uint8 x_330; obj* x_331; 
x_329 = lean::cnstr_get(x_306, 0);
x_330 = lean::cnstr_get_scalar<uint8>(x_306, sizeof(void*)*1);
lean::inc(x_329);
lean::dec(x_306);
x_331 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_331, 0, x_329);
lean::cnstr_set_scalar(x_331, sizeof(void*)*1, x_330);
x_16 = x_331;
x_17 = x_327;
goto block_302;
}
}
block_302:
{
if (lean::obj_tag(x_16) == 0)
{
obj* x_18; obj* x_19; 
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_8);
x_18 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_16);
if (lean::is_scalar(x_12)) {
 x_19 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_19 = x_12;
}
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_17);
return x_19;
}
else
{
obj* x_20; uint8 x_21; obj* x_22; obj* x_23; 
x_20 = lean::cnstr_get(x_16, 0);
lean::inc(x_20);
x_21 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
if (x_21 == 0)
{
obj* x_239; obj* x_240; obj* x_241; obj* x_242; 
lean::dec(x_16);
x_239 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__3;
x_240 = l___private_init_lean_parser_token_1__finishCommentBlockAux___main___closed__4;
lean::inc(x_13);
x_241 = l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3(x_239, x_240, x_2, x_13, x_17);
x_242 = lean::cnstr_get(x_241, 0);
lean::inc(x_242);
if (lean::obj_tag(x_242) == 0)
{
obj* x_243; obj* x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; 
x_243 = lean::cnstr_get(x_241, 1);
lean::inc(x_243);
lean::dec(x_241);
x_244 = lean::cnstr_get(x_242, 1);
lean::inc(x_244);
x_245 = lean::cnstr_get(x_242, 2);
lean::inc(x_245);
lean::dec(x_242);
x_246 = l___private_init_lean_parser_token_2__whitespaceAux___main___closed__1;
x_247 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::inc(x_244);
x_248 = l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__4(x_2, x_246, x_247, x_244, x_243);
x_249 = lean::cnstr_get(x_248, 0);
lean::inc(x_249);
if (lean::obj_tag(x_249) == 0)
{
obj* x_250; uint8 x_251; 
x_250 = lean::cnstr_get(x_249, 0);
lean::inc(x_250);
x_251 = lean::unbox(x_250);
lean::dec(x_250);
if (x_251 == 0)
{
obj* x_252; obj* x_253; obj* x_254; obj* x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; obj* x_260; obj* x_261; obj* x_262; obj* x_263; obj* x_264; obj* x_265; 
x_252 = lean::cnstr_get(x_248, 1);
lean::inc(x_252);
lean::dec(x_248);
x_253 = lean::cnstr_get(x_249, 1);
lean::inc(x_253);
x_254 = lean::cnstr_get(x_249, 2);
lean::inc(x_254);
lean::dec(x_249);
x_255 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_255, 0, x_244);
x_256 = lean::box(0);
x_257 = l___private_init_lean_parser_token_2__whitespaceAux___main___closed__2;
x_258 = l_mjoin___rarg___closed__1;
x_259 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_257, x_258, x_255, x_256, x_2, x_253, x_252);
lean::dec(x_255);
x_260 = lean::cnstr_get(x_259, 0);
lean::inc(x_260);
x_261 = lean::cnstr_get(x_259, 1);
lean::inc(x_261);
lean::dec(x_259);
x_262 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_254, x_260);
x_263 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_247, x_262);
x_264 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_245, x_263);
x_265 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_264);
x_22 = x_265;
x_23 = x_261;
goto block_238;
}
else
{
obj* x_266; uint8 x_267; 
lean::dec(x_244);
x_266 = lean::cnstr_get(x_248, 1);
lean::inc(x_266);
lean::dec(x_248);
x_267 = !lean::is_exclusive(x_249);
if (x_267 == 0)
{
obj* x_268; obj* x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; 
x_268 = lean::cnstr_get(x_249, 2);
x_269 = lean::cnstr_get(x_249, 0);
lean::dec(x_269);
x_270 = lean::box(0);
lean::cnstr_set(x_249, 2, x_247);
lean::cnstr_set(x_249, 0, x_270);
x_271 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_268, x_249);
x_272 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_247, x_271);
x_273 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_245, x_272);
x_274 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_273);
x_22 = x_274;
x_23 = x_266;
goto block_238;
}
else
{
obj* x_275; obj* x_276; obj* x_277; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; 
x_275 = lean::cnstr_get(x_249, 1);
x_276 = lean::cnstr_get(x_249, 2);
lean::inc(x_276);
lean::inc(x_275);
lean::dec(x_249);
x_277 = lean::box(0);
x_278 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_278, 0, x_277);
lean::cnstr_set(x_278, 1, x_275);
lean::cnstr_set(x_278, 2, x_247);
x_279 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_276, x_278);
x_280 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_247, x_279);
x_281 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_245, x_280);
x_282 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_281);
x_22 = x_282;
x_23 = x_266;
goto block_238;
}
}
}
else
{
obj* x_283; uint8 x_284; 
lean::dec(x_244);
x_283 = lean::cnstr_get(x_248, 1);
lean::inc(x_283);
lean::dec(x_248);
x_284 = !lean::is_exclusive(x_249);
if (x_284 == 0)
{
obj* x_285; obj* x_286; obj* x_287; 
x_285 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_247, x_249);
x_286 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_245, x_285);
x_287 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_286);
x_22 = x_287;
x_23 = x_283;
goto block_238;
}
else
{
obj* x_288; uint8 x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; 
x_288 = lean::cnstr_get(x_249, 0);
x_289 = lean::cnstr_get_scalar<uint8>(x_249, sizeof(void*)*1);
lean::inc(x_288);
lean::dec(x_249);
x_290 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_290, 0, x_288);
lean::cnstr_set_scalar(x_290, sizeof(void*)*1, x_289);
x_291 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_247, x_290);
x_292 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_245, x_291);
x_293 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_292);
x_22 = x_293;
x_23 = x_283;
goto block_238;
}
}
}
else
{
obj* x_294; uint8 x_295; 
x_294 = lean::cnstr_get(x_241, 1);
lean::inc(x_294);
lean::dec(x_241);
x_295 = !lean::is_exclusive(x_242);
if (x_295 == 0)
{
uint8 x_296; 
x_296 = 0;
lean::cnstr_set_scalar(x_242, sizeof(void*)*1, x_296);
x_22 = x_242;
x_23 = x_294;
goto block_238;
}
else
{
obj* x_297; uint8 x_298; obj* x_299; 
x_297 = lean::cnstr_get(x_242, 0);
lean::inc(x_297);
lean::dec(x_242);
x_298 = 0;
x_299 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_299, 0, x_297);
lean::cnstr_set_scalar(x_299, sizeof(void*)*1, x_298);
x_22 = x_299;
x_23 = x_294;
goto block_238;
}
}
}
else
{
obj* x_300; obj* x_301; 
lean::dec(x_20);
lean::dec(x_15);
lean::dec(x_13);
lean::dec(x_12);
lean::dec(x_8);
x_300 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_16);
x_301 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_301, 0, x_300);
lean::cnstr_set(x_301, 1, x_17);
return x_301;
}
block_238:
{
if (lean::obj_tag(x_22) == 0)
{
uint8 x_24; 
lean::dec(x_15);
lean::dec(x_12);
x_24 = !lean::is_exclusive(x_22);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_25 = lean::cnstr_get(x_22, 1);
x_26 = lean::cnstr_get(x_22, 2);
x_27 = lean::cnstr_get(x_22, 0);
lean::dec(x_27);
x_28 = l_Lean_Parser_finishCommentBlock(x_7, x_2, x_25, x_23);
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; uint8 x_31; 
lean::free_heap_obj(x_22);
x_30 = lean::cnstr_get(x_28, 1);
lean::inc(x_30);
lean::dec(x_28);
x_31 = !lean::is_exclusive(x_29);
if (x_31 == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; uint8 x_36; 
x_32 = lean::cnstr_get(x_29, 1);
x_33 = lean::cnstr_get(x_29, 2);
x_34 = lean::cnstr_get(x_29, 0);
lean::dec(x_34);
x_35 = l___private_init_lean_parser_token_2__whitespaceAux___main(x_8, x_2, x_32, x_30);
lean::dec(x_8);
x_36 = !lean::is_exclusive(x_35);
if (x_36 == 0)
{
obj* x_37; obj* x_38; obj* x_39; 
x_37 = lean::cnstr_get(x_35, 0);
x_38 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_33, x_37);
x_39 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_26, x_38);
if (lean::obj_tag(x_39) == 0)
{
obj* x_40; obj* x_41; 
lean::free_heap_obj(x_29);
lean::dec(x_13);
x_40 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_20, x_39);
x_41 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_40);
lean::cnstr_set(x_35, 0, x_41);
return x_35;
}
else
{
uint8 x_42; 
x_42 = lean::cnstr_get_scalar<uint8>(x_39, sizeof(void*)*1);
if (x_42 == 0)
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_43 = lean::cnstr_get(x_39, 0);
lean::inc(x_43);
lean::dec(x_39);
x_44 = lean::cnstr_get(x_43, 2);
lean::inc(x_44);
lean::dec(x_43);
x_45 = l_mjoin___rarg___closed__1;
x_46 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_46, 0, x_44);
lean::closure_set(x_46, 1, x_45);
x_47 = lean::cnstr_get(x_20, 2);
lean::inc(x_47);
lean::dec(x_20);
x_48 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_48, 0, x_47);
lean::closure_set(x_48, 1, x_46);
x_49 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_49, 0, x_48);
x_50 = lean::box(0);
lean::cnstr_set(x_29, 2, x_49);
lean::cnstr_set(x_29, 1, x_13);
lean::cnstr_set(x_29, 0, x_50);
x_51 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_29);
lean::cnstr_set(x_35, 0, x_51);
return x_35;
}
else
{
obj* x_52; obj* x_53; 
lean::free_heap_obj(x_29);
lean::dec(x_13);
x_52 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_20, x_39);
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_52);
lean::cnstr_set(x_35, 0, x_53);
return x_35;
}
}
}
else
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_54 = lean::cnstr_get(x_35, 0);
x_55 = lean::cnstr_get(x_35, 1);
lean::inc(x_55);
lean::inc(x_54);
lean::dec(x_35);
x_56 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_33, x_54);
x_57 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_26, x_56);
if (lean::obj_tag(x_57) == 0)
{
obj* x_58; obj* x_59; obj* x_60; 
lean::free_heap_obj(x_29);
lean::dec(x_13);
x_58 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_20, x_57);
x_59 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_58);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_59);
lean::cnstr_set(x_60, 1, x_55);
return x_60;
}
else
{
uint8 x_61; 
x_61 = lean::cnstr_get_scalar<uint8>(x_57, sizeof(void*)*1);
if (x_61 == 0)
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_62 = lean::cnstr_get(x_57, 0);
lean::inc(x_62);
lean::dec(x_57);
x_63 = lean::cnstr_get(x_62, 2);
lean::inc(x_63);
lean::dec(x_62);
x_64 = l_mjoin___rarg___closed__1;
x_65 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_65, 0, x_63);
lean::closure_set(x_65, 1, x_64);
x_66 = lean::cnstr_get(x_20, 2);
lean::inc(x_66);
lean::dec(x_20);
x_67 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_67, 0, x_66);
lean::closure_set(x_67, 1, x_65);
x_68 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_68, 0, x_67);
x_69 = lean::box(0);
lean::cnstr_set(x_29, 2, x_68);
lean::cnstr_set(x_29, 1, x_13);
lean::cnstr_set(x_29, 0, x_69);
x_70 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_29);
x_71 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_71, 0, x_70);
lean::cnstr_set(x_71, 1, x_55);
return x_71;
}
else
{
obj* x_72; obj* x_73; obj* x_74; 
lean::free_heap_obj(x_29);
lean::dec(x_13);
x_72 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_20, x_57);
x_73 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_72);
x_74 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_55);
return x_74;
}
}
}
}
else
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_75 = lean::cnstr_get(x_29, 1);
x_76 = lean::cnstr_get(x_29, 2);
lean::inc(x_76);
lean::inc(x_75);
lean::dec(x_29);
x_77 = l___private_init_lean_parser_token_2__whitespaceAux___main(x_8, x_2, x_75, x_30);
lean::dec(x_8);
x_78 = lean::cnstr_get(x_77, 0);
lean::inc(x_78);
x_79 = lean::cnstr_get(x_77, 1);
lean::inc(x_79);
if (lean::is_exclusive(x_77)) {
 lean::cnstr_release(x_77, 0);
 lean::cnstr_release(x_77, 1);
 x_80 = x_77;
} else {
 lean::dec_ref(x_77);
 x_80 = lean::box(0);
}
x_81 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_76, x_78);
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_26, x_81);
if (lean::obj_tag(x_82) == 0)
{
obj* x_83; obj* x_84; obj* x_85; 
lean::dec(x_13);
x_83 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_20, x_82);
x_84 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_83);
if (lean::is_scalar(x_80)) {
 x_85 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_85 = x_80;
}
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_79);
return x_85;
}
else
{
uint8 x_86; 
x_86 = lean::cnstr_get_scalar<uint8>(x_82, sizeof(void*)*1);
if (x_86 == 0)
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_87 = lean::cnstr_get(x_82, 0);
lean::inc(x_87);
lean::dec(x_82);
x_88 = lean::cnstr_get(x_87, 2);
lean::inc(x_88);
lean::dec(x_87);
x_89 = l_mjoin___rarg___closed__1;
x_90 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_90, 0, x_88);
lean::closure_set(x_90, 1, x_89);
x_91 = lean::cnstr_get(x_20, 2);
lean::inc(x_91);
lean::dec(x_20);
x_92 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_92, 0, x_91);
lean::closure_set(x_92, 1, x_90);
x_93 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_93, 0, x_92);
x_94 = lean::box(0);
x_95 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_13);
lean::cnstr_set(x_95, 2, x_93);
x_96 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_95);
if (lean::is_scalar(x_80)) {
 x_97 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_97 = x_80;
}
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_79);
return x_97;
}
else
{
obj* x_98; obj* x_99; obj* x_100; 
lean::dec(x_13);
x_98 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_20, x_82);
x_99 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_98);
if (lean::is_scalar(x_80)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_80;
}
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_79);
return x_100;
}
}
}
}
else
{
uint8 x_101; 
lean::dec(x_8);
x_101 = !lean::is_exclusive(x_28);
if (x_101 == 0)
{
obj* x_102; uint8 x_103; 
x_102 = lean::cnstr_get(x_28, 0);
lean::dec(x_102);
x_103 = !lean::is_exclusive(x_29);
if (x_103 == 0)
{
obj* x_104; 
x_104 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_26, x_29);
if (lean::obj_tag(x_104) == 0)
{
obj* x_105; obj* x_106; 
lean::free_heap_obj(x_22);
lean::dec(x_13);
x_105 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_20, x_104);
x_106 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_105);
lean::cnstr_set(x_28, 0, x_106);
return x_28;
}
else
{
uint8 x_107; 
x_107 = lean::cnstr_get_scalar<uint8>(x_104, sizeof(void*)*1);
if (x_107 == 0)
{
obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; 
x_108 = lean::cnstr_get(x_104, 0);
lean::inc(x_108);
lean::dec(x_104);
x_109 = lean::cnstr_get(x_108, 2);
lean::inc(x_109);
lean::dec(x_108);
x_110 = l_mjoin___rarg___closed__1;
x_111 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_111, 0, x_109);
lean::closure_set(x_111, 1, x_110);
x_112 = lean::cnstr_get(x_20, 2);
lean::inc(x_112);
lean::dec(x_20);
x_113 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_113, 0, x_112);
lean::closure_set(x_113, 1, x_111);
x_114 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_114, 0, x_113);
x_115 = lean::box(0);
lean::cnstr_set(x_22, 2, x_114);
lean::cnstr_set(x_22, 1, x_13);
lean::cnstr_set(x_22, 0, x_115);
x_116 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_22);
lean::cnstr_set(x_28, 0, x_116);
return x_28;
}
else
{
obj* x_117; obj* x_118; 
lean::free_heap_obj(x_22);
lean::dec(x_13);
x_117 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_20, x_104);
x_118 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_117);
lean::cnstr_set(x_28, 0, x_118);
return x_28;
}
}
}
else
{
obj* x_119; uint8 x_120; obj* x_121; obj* x_122; 
x_119 = lean::cnstr_get(x_29, 0);
x_120 = lean::cnstr_get_scalar<uint8>(x_29, sizeof(void*)*1);
lean::inc(x_119);
lean::dec(x_29);
x_121 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_121, 0, x_119);
lean::cnstr_set_scalar(x_121, sizeof(void*)*1, x_120);
x_122 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_26, x_121);
if (lean::obj_tag(x_122) == 0)
{
obj* x_123; obj* x_124; 
lean::free_heap_obj(x_22);
lean::dec(x_13);
x_123 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_20, x_122);
x_124 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_123);
lean::cnstr_set(x_28, 0, x_124);
return x_28;
}
else
{
uint8 x_125; 
x_125 = lean::cnstr_get_scalar<uint8>(x_122, sizeof(void*)*1);
if (x_125 == 0)
{
obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
x_126 = lean::cnstr_get(x_122, 0);
lean::inc(x_126);
lean::dec(x_122);
x_127 = lean::cnstr_get(x_126, 2);
lean::inc(x_127);
lean::dec(x_126);
x_128 = l_mjoin___rarg___closed__1;
x_129 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_129, 0, x_127);
lean::closure_set(x_129, 1, x_128);
x_130 = lean::cnstr_get(x_20, 2);
lean::inc(x_130);
lean::dec(x_20);
x_131 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_131, 0, x_130);
lean::closure_set(x_131, 1, x_129);
x_132 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_132, 0, x_131);
x_133 = lean::box(0);
lean::cnstr_set(x_22, 2, x_132);
lean::cnstr_set(x_22, 1, x_13);
lean::cnstr_set(x_22, 0, x_133);
x_134 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_22);
lean::cnstr_set(x_28, 0, x_134);
return x_28;
}
else
{
obj* x_135; obj* x_136; 
lean::free_heap_obj(x_22);
lean::dec(x_13);
x_135 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_20, x_122);
x_136 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_135);
lean::cnstr_set(x_28, 0, x_136);
return x_28;
}
}
}
}
else
{
obj* x_137; obj* x_138; uint8 x_139; obj* x_140; obj* x_141; obj* x_142; 
x_137 = lean::cnstr_get(x_28, 1);
lean::inc(x_137);
lean::dec(x_28);
x_138 = lean::cnstr_get(x_29, 0);
lean::inc(x_138);
x_139 = lean::cnstr_get_scalar<uint8>(x_29, sizeof(void*)*1);
if (lean::is_exclusive(x_29)) {
 lean::cnstr_release(x_29, 0);
 x_140 = x_29;
} else {
 lean::dec_ref(x_29);
 x_140 = lean::box(0);
}
if (lean::is_scalar(x_140)) {
 x_141 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_141 = x_140;
}
lean::cnstr_set(x_141, 0, x_138);
lean::cnstr_set_scalar(x_141, sizeof(void*)*1, x_139);
x_142 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_26, x_141);
if (lean::obj_tag(x_142) == 0)
{
obj* x_143; obj* x_144; obj* x_145; 
lean::free_heap_obj(x_22);
lean::dec(x_13);
x_143 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_20, x_142);
x_144 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_143);
x_145 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_145, 0, x_144);
lean::cnstr_set(x_145, 1, x_137);
return x_145;
}
else
{
uint8 x_146; 
x_146 = lean::cnstr_get_scalar<uint8>(x_142, sizeof(void*)*1);
if (x_146 == 0)
{
obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; 
x_147 = lean::cnstr_get(x_142, 0);
lean::inc(x_147);
lean::dec(x_142);
x_148 = lean::cnstr_get(x_147, 2);
lean::inc(x_148);
lean::dec(x_147);
x_149 = l_mjoin___rarg___closed__1;
x_150 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_150, 0, x_148);
lean::closure_set(x_150, 1, x_149);
x_151 = lean::cnstr_get(x_20, 2);
lean::inc(x_151);
lean::dec(x_20);
x_152 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_152, 0, x_151);
lean::closure_set(x_152, 1, x_150);
x_153 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_153, 0, x_152);
x_154 = lean::box(0);
lean::cnstr_set(x_22, 2, x_153);
lean::cnstr_set(x_22, 1, x_13);
lean::cnstr_set(x_22, 0, x_154);
x_155 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_22);
x_156 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_156, 0, x_155);
lean::cnstr_set(x_156, 1, x_137);
return x_156;
}
else
{
obj* x_157; obj* x_158; obj* x_159; 
lean::free_heap_obj(x_22);
lean::dec(x_13);
x_157 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_20, x_142);
x_158 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_157);
x_159 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_159, 0, x_158);
lean::cnstr_set(x_159, 1, x_137);
return x_159;
}
}
}
}
}
else
{
obj* x_160; obj* x_161; obj* x_162; obj* x_163; 
x_160 = lean::cnstr_get(x_22, 1);
x_161 = lean::cnstr_get(x_22, 2);
lean::inc(x_161);
lean::inc(x_160);
lean::dec(x_22);
x_162 = l_Lean_Parser_finishCommentBlock(x_7, x_2, x_160, x_23);
x_163 = lean::cnstr_get(x_162, 0);
lean::inc(x_163);
if (lean::obj_tag(x_163) == 0)
{
obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; 
x_164 = lean::cnstr_get(x_162, 1);
lean::inc(x_164);
lean::dec(x_162);
x_165 = lean::cnstr_get(x_163, 1);
lean::inc(x_165);
x_166 = lean::cnstr_get(x_163, 2);
lean::inc(x_166);
if (lean::is_exclusive(x_163)) {
 lean::cnstr_release(x_163, 0);
 lean::cnstr_release(x_163, 1);
 lean::cnstr_release(x_163, 2);
 x_167 = x_163;
} else {
 lean::dec_ref(x_163);
 x_167 = lean::box(0);
}
x_168 = l___private_init_lean_parser_token_2__whitespaceAux___main(x_8, x_2, x_165, x_164);
lean::dec(x_8);
x_169 = lean::cnstr_get(x_168, 0);
lean::inc(x_169);
x_170 = lean::cnstr_get(x_168, 1);
lean::inc(x_170);
if (lean::is_exclusive(x_168)) {
 lean::cnstr_release(x_168, 0);
 lean::cnstr_release(x_168, 1);
 x_171 = x_168;
} else {
 lean::dec_ref(x_168);
 x_171 = lean::box(0);
}
x_172 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_166, x_169);
x_173 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_161, x_172);
if (lean::obj_tag(x_173) == 0)
{
obj* x_174; obj* x_175; obj* x_176; 
lean::dec(x_167);
lean::dec(x_13);
x_174 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_20, x_173);
x_175 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_174);
if (lean::is_scalar(x_171)) {
 x_176 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_176 = x_171;
}
lean::cnstr_set(x_176, 0, x_175);
lean::cnstr_set(x_176, 1, x_170);
return x_176;
}
else
{
uint8 x_177; 
x_177 = lean::cnstr_get_scalar<uint8>(x_173, sizeof(void*)*1);
if (x_177 == 0)
{
obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; 
x_178 = lean::cnstr_get(x_173, 0);
lean::inc(x_178);
lean::dec(x_173);
x_179 = lean::cnstr_get(x_178, 2);
lean::inc(x_179);
lean::dec(x_178);
x_180 = l_mjoin___rarg___closed__1;
x_181 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_181, 0, x_179);
lean::closure_set(x_181, 1, x_180);
x_182 = lean::cnstr_get(x_20, 2);
lean::inc(x_182);
lean::dec(x_20);
x_183 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_183, 0, x_182);
lean::closure_set(x_183, 1, x_181);
x_184 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_184, 0, x_183);
x_185 = lean::box(0);
if (lean::is_scalar(x_167)) {
 x_186 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_186 = x_167;
}
lean::cnstr_set(x_186, 0, x_185);
lean::cnstr_set(x_186, 1, x_13);
lean::cnstr_set(x_186, 2, x_184);
x_187 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_186);
if (lean::is_scalar(x_171)) {
 x_188 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_188 = x_171;
}
lean::cnstr_set(x_188, 0, x_187);
lean::cnstr_set(x_188, 1, x_170);
return x_188;
}
else
{
obj* x_189; obj* x_190; obj* x_191; 
lean::dec(x_167);
lean::dec(x_13);
x_189 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_20, x_173);
x_190 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_189);
if (lean::is_scalar(x_171)) {
 x_191 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_191 = x_171;
}
lean::cnstr_set(x_191, 0, x_190);
lean::cnstr_set(x_191, 1, x_170);
return x_191;
}
}
}
else
{
obj* x_192; obj* x_193; obj* x_194; uint8 x_195; obj* x_196; obj* x_197; obj* x_198; 
lean::dec(x_8);
x_192 = lean::cnstr_get(x_162, 1);
lean::inc(x_192);
if (lean::is_exclusive(x_162)) {
 lean::cnstr_release(x_162, 0);
 lean::cnstr_release(x_162, 1);
 x_193 = x_162;
} else {
 lean::dec_ref(x_162);
 x_193 = lean::box(0);
}
x_194 = lean::cnstr_get(x_163, 0);
lean::inc(x_194);
x_195 = lean::cnstr_get_scalar<uint8>(x_163, sizeof(void*)*1);
if (lean::is_exclusive(x_163)) {
 lean::cnstr_release(x_163, 0);
 x_196 = x_163;
} else {
 lean::dec_ref(x_163);
 x_196 = lean::box(0);
}
if (lean::is_scalar(x_196)) {
 x_197 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_197 = x_196;
}
lean::cnstr_set(x_197, 0, x_194);
lean::cnstr_set_scalar(x_197, sizeof(void*)*1, x_195);
x_198 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_161, x_197);
if (lean::obj_tag(x_198) == 0)
{
obj* x_199; obj* x_200; obj* x_201; 
lean::dec(x_13);
x_199 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_20, x_198);
x_200 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_199);
if (lean::is_scalar(x_193)) {
 x_201 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_201 = x_193;
}
lean::cnstr_set(x_201, 0, x_200);
lean::cnstr_set(x_201, 1, x_192);
return x_201;
}
else
{
uint8 x_202; 
x_202 = lean::cnstr_get_scalar<uint8>(x_198, sizeof(void*)*1);
if (x_202 == 0)
{
obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; obj* x_212; obj* x_213; 
x_203 = lean::cnstr_get(x_198, 0);
lean::inc(x_203);
lean::dec(x_198);
x_204 = lean::cnstr_get(x_203, 2);
lean::inc(x_204);
lean::dec(x_203);
x_205 = l_mjoin___rarg___closed__1;
x_206 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_206, 0, x_204);
lean::closure_set(x_206, 1, x_205);
x_207 = lean::cnstr_get(x_20, 2);
lean::inc(x_207);
lean::dec(x_20);
x_208 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_208, 0, x_207);
lean::closure_set(x_208, 1, x_206);
x_209 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_209, 0, x_208);
x_210 = lean::box(0);
x_211 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_211, 0, x_210);
lean::cnstr_set(x_211, 1, x_13);
lean::cnstr_set(x_211, 2, x_209);
x_212 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_211);
if (lean::is_scalar(x_193)) {
 x_213 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_213 = x_193;
}
lean::cnstr_set(x_213, 0, x_212);
lean::cnstr_set(x_213, 1, x_192);
return x_213;
}
else
{
obj* x_214; obj* x_215; obj* x_216; 
lean::dec(x_13);
x_214 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_20, x_198);
x_215 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_214);
if (lean::is_scalar(x_193)) {
 x_216 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_216 = x_193;
}
lean::cnstr_set(x_216, 0, x_215);
lean::cnstr_set(x_216, 1, x_192);
return x_216;
}
}
}
}
}
else
{
uint8 x_217; 
lean::dec(x_8);
x_217 = lean::cnstr_get_scalar<uint8>(x_22, sizeof(void*)*1);
if (x_217 == 0)
{
obj* x_218; obj* x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; 
x_218 = lean::cnstr_get(x_22, 0);
lean::inc(x_218);
lean::dec(x_22);
x_219 = lean::cnstr_get(x_218, 2);
lean::inc(x_219);
lean::dec(x_218);
x_220 = l_mjoin___rarg___closed__1;
x_221 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_221, 0, x_219);
lean::closure_set(x_221, 1, x_220);
x_222 = lean::cnstr_get(x_20, 2);
lean::inc(x_222);
lean::dec(x_20);
x_223 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_223, 0, x_222);
lean::closure_set(x_223, 1, x_221);
x_224 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_224, 0, x_223);
x_225 = lean::box(0);
if (lean::is_scalar(x_15)) {
 x_226 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_226 = x_15;
}
lean::cnstr_set(x_226, 0, x_225);
lean::cnstr_set(x_226, 1, x_13);
lean::cnstr_set(x_226, 2, x_224);
x_227 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_226);
if (lean::is_scalar(x_12)) {
 x_228 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_228 = x_12;
}
lean::cnstr_set(x_228, 0, x_227);
lean::cnstr_set(x_228, 1, x_23);
return x_228;
}
else
{
uint8 x_229; 
lean::dec(x_15);
lean::dec(x_13);
x_229 = !lean::is_exclusive(x_22);
if (x_229 == 0)
{
obj* x_230; obj* x_231; obj* x_232; 
x_230 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_20, x_22);
x_231 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_230);
if (lean::is_scalar(x_12)) {
 x_232 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_232 = x_12;
}
lean::cnstr_set(x_232, 0, x_231);
lean::cnstr_set(x_232, 1, x_23);
return x_232;
}
else
{
obj* x_233; obj* x_234; obj* x_235; obj* x_236; obj* x_237; 
x_233 = lean::cnstr_get(x_22, 0);
lean::inc(x_233);
lean::dec(x_22);
x_234 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_234, 0, x_233);
lean::cnstr_set_scalar(x_234, sizeof(void*)*1, x_217);
x_235 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_20, x_234);
x_236 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_235);
if (lean::is_scalar(x_12)) {
 x_237 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_237 = x_12;
}
lean::cnstr_set(x_237, 0, x_236);
lean::cnstr_set(x_237, 1, x_23);
return x_237;
}
}
}
}
}
}
}
else
{
uint8 x_332; 
lean::dec(x_8);
x_332 = !lean::is_exclusive(x_9);
if (x_332 == 0)
{
obj* x_333; uint8 x_334; 
x_333 = lean::cnstr_get(x_9, 0);
lean::dec(x_333);
x_334 = !lean::is_exclusive(x_10);
if (x_334 == 0)
{
return x_9;
}
else
{
obj* x_335; uint8 x_336; obj* x_337; 
x_335 = lean::cnstr_get(x_10, 0);
x_336 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
lean::inc(x_335);
lean::dec(x_10);
x_337 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_337, 0, x_335);
lean::cnstr_set_scalar(x_337, sizeof(void*)*1, x_336);
lean::cnstr_set(x_9, 0, x_337);
return x_9;
}
}
else
{
obj* x_338; obj* x_339; uint8 x_340; obj* x_341; obj* x_342; obj* x_343; 
x_338 = lean::cnstr_get(x_9, 1);
lean::inc(x_338);
lean::dec(x_9);
x_339 = lean::cnstr_get(x_10, 0);
lean::inc(x_339);
x_340 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
if (lean::is_exclusive(x_10)) {
 lean::cnstr_release(x_10, 0);
 x_341 = x_10;
} else {
 lean::dec_ref(x_10);
 x_341 = lean::box(0);
}
if (lean::is_scalar(x_341)) {
 x_342 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_342 = x_341;
}
lean::cnstr_set(x_342, 0, x_339);
lean::cnstr_set_scalar(x_342, sizeof(void*)*1, x_340);
x_343 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_343, 0, x_342);
lean::cnstr_set(x_343, 1, x_338);
return x_343;
}
}
}
else
{
obj* x_344; obj* x_345; obj* x_346; obj* x_347; 
x_344 = lean::box(0);
x_345 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
x_346 = l_mjoin___rarg___closed__1;
x_347 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_345, x_346, x_344, x_344, x_2, x_3, x_4);
return x_347;
}
}
}
obj* l___private_init_lean_parser_parsec_7__takeWhileAux_x27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
lean::dec(x_2);
x_5 = l___private_init_lean_parser_parsec_7__takeWhileAux_x27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__3(x_1, x_4, x_3);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile_x27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__2___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_takeWhile_x27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__2(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_whitespace___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_whitespace___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__4___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__4(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_1);
return x_6;
}
}
obj* l___private_init_lean_parser_parsec_7__takeWhileAux_x27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__6___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; obj* x_5; 
x_4 = lean::unbox(x_2);
lean::dec(x_2);
x_5 = l___private_init_lean_parser_parsec_7__takeWhileAux_x27___main___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__6(x_1, x_4, x_3);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile_x27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__5___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_takeWhile_x27___at___private_init_lean_parser_token_2__whitespaceAux___main___spec__5(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_token_2__whitespaceAux___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_token_2__whitespaceAux___main(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l___private_init_lean_parser_token_2__whitespaceAux(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_token_2__whitespaceAux___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l___private_init_lean_parser_token_2__whitespaceAux___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_token_2__whitespaceAux(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_whitespace(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = l_String_OldIterator_remaining___main(x_2);
x_5 = lean::mk_nat_obj(1u);
x_6 = lean::nat_add(x_4, x_5);
lean::dec(x_4);
x_7 = l___private_init_lean_parser_token_2__whitespaceAux___main(x_6, x_1, x_2, x_3);
lean::dec(x_6);
x_8 = !lean::is_exclusive(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_7, 0);
x_10 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_11 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_10, x_9);
x_12 = l_mjoin___rarg___closed__1;
x_13 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_11, x_12);
lean::cnstr_set(x_7, 0, x_13);
return x_7;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_14 = lean::cnstr_get(x_7, 0);
x_15 = lean::cnstr_get(x_7, 1);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_7);
x_16 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_17 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_14);
x_18 = l_mjoin___rarg___closed__1;
x_19 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_17, x_18);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_15);
return x_20;
}
}
}
obj* l_Lean_Parser_whitespace___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_whitespace(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_asSubstring___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_3);
x_7 = lean::apply_2(x_5, lean::box(0), x_6);
return x_7;
}
}
obj* l_Lean_Parser_asSubstring___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_asSubstring___rarg___lambda__1), 3, 2);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_2);
x_7 = lean::apply_4(x_3, lean::box(0), lean::box(0), x_4, x_6);
return x_7;
}
}
obj* l_Lean_Parser_asSubstring___rarg___lambda__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_asSubstring___rarg___lambda__2___boxed), 5, 4);
lean::closure_set(x_6, 0, x_1);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_2);
lean::closure_set(x_6, 3, x_3);
x_7 = lean::apply_4(x_2, lean::box(0), lean::box(0), x_4, x_6);
return x_7;
}
}
obj* l_Lean_Parser_asSubstring___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_2, 0);
lean::inc(x_6);
lean::dec(x_2);
x_7 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_8 = lean::apply_2(x_6, lean::box(0), x_7);
lean::inc(x_8);
lean::inc(x_5);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_asSubstring___rarg___lambda__3), 5, 4);
lean::closure_set(x_9, 0, x_1);
lean::closure_set(x_9, 1, x_5);
lean::closure_set(x_9, 2, x_8);
lean::closure_set(x_9, 3, x_4);
x_10 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_8, x_9);
return x_10;
}
}
obj* l_Lean_Parser_asSubstring(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_asSubstring___rarg), 4, 0);
return x_2;
}
}
obj* l_Lean_Parser_asSubstring___rarg___lambda__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_asSubstring___rarg___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_5);
return x_6;
}
}
obj* l_Lean_Parser_asSubstring___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_asSubstring(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_updateLast___main(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_3; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::dec(x_6);
x_7 = lean::apply_1(x_1, x_5);
lean::cnstr_set(x_2, 0, x_7);
return x_2;
}
else
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
lean::dec(x_2);
x_9 = lean::apply_1(x_1, x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
else
{
obj* x_11; obj* x_12; uint8 x_13; 
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
lean::dec(x_2);
lean::inc(x_3);
x_12 = l_Lean_Parser_updateLast___main(x_1, x_3);
x_13 = !lean::is_exclusive(x_3);
if (x_13 == 0)
{
obj* x_14; obj* x_15; 
x_14 = lean::cnstr_get(x_3, 1);
lean::dec(x_14);
x_15 = lean::cnstr_get(x_3, 0);
lean::dec(x_15);
lean::cnstr_set(x_3, 1, x_12);
lean::cnstr_set(x_3, 0, x_11);
return x_3;
}
else
{
obj* x_16; 
lean::dec(x_3);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_11);
lean::cnstr_set(x_16, 1, x_12);
return x_16;
}
}
}
}
}
obj* l_Lean_Parser_updateLast(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_updateLast___main(x_1, x_3);
return x_4;
}
}
obj* l_Lean_Parser_updateLast___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_updateLast(x_1, x_2, x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_updateLast___main___at___private_init_lean_parser_token_3__updateTrailing___main___spec__1(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
lean::dec(x_1);
return x_2;
}
else
{
obj* x_3; 
x_3 = lean::cnstr_get(x_2, 1);
lean::inc(x_3);
if (lean::obj_tag(x_3) == 0)
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_2, 1);
lean::dec(x_6);
x_7 = l___private_init_lean_parser_token_3__updateTrailing___main(x_1, x_5);
lean::cnstr_set(x_2, 0, x_7);
return x_2;
}
else
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
lean::dec(x_2);
x_9 = l___private_init_lean_parser_token_3__updateTrailing___main(x_1, x_8);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_3);
return x_10;
}
}
else
{
obj* x_11; obj* x_12; uint8 x_13; 
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
lean::dec(x_2);
lean::inc(x_3);
x_12 = l_Lean_Parser_updateLast___main___at___private_init_lean_parser_token_3__updateTrailing___main___spec__1(x_1, x_3);
x_13 = !lean::is_exclusive(x_3);
if (x_13 == 0)
{
obj* x_14; obj* x_15; 
x_14 = lean::cnstr_get(x_3, 1);
lean::dec(x_14);
x_15 = lean::cnstr_get(x_3, 0);
lean::dec(x_15);
lean::cnstr_set(x_3, 1, x_12);
lean::cnstr_set(x_3, 0, x_11);
return x_3;
}
else
{
obj* x_16; 
lean::dec(x_3);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_11);
lean::cnstr_set(x_16, 1, x_12);
return x_16;
}
}
}
}
}
obj* l___private_init_lean_parser_token_3__updateTrailing___main(obj* x_1, obj* x_2) {
_start:
{
switch (lean::obj_tag(x_2)) {
case 0:
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_2, 0);
lean::inc(x_3);
x_4 = lean::cnstr_get(x_3, 0);
lean::inc(x_4);
if (lean::obj_tag(x_4) == 0)
{
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
return x_2;
}
else
{
uint8 x_5; 
x_5 = !lean::is_exclusive(x_2);
if (x_5 == 0)
{
obj* x_6; uint8 x_7; 
x_6 = lean::cnstr_get(x_2, 0);
lean::dec(x_6);
x_7 = !lean::is_exclusive(x_4);
if (x_7 == 0)
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_3);
if (x_8 == 0)
{
obj* x_9; obj* x_10; uint8 x_11; 
x_9 = lean::cnstr_get(x_4, 0);
x_10 = lean::cnstr_get(x_3, 0);
lean::dec(x_10);
x_11 = !lean::is_exclusive(x_9);
if (x_11 == 0)
{
obj* x_12; 
x_12 = lean::cnstr_get(x_9, 2);
lean::dec(x_12);
lean::cnstr_set(x_9, 2, x_1);
return x_2;
}
else
{
obj* x_13; obj* x_14; obj* x_15; 
x_13 = lean::cnstr_get(x_9, 0);
x_14 = lean::cnstr_get(x_9, 1);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_9);
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_14);
lean::cnstr_set(x_15, 2, x_1);
lean::cnstr_set(x_4, 0, x_15);
return x_2;
}
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_16 = lean::cnstr_get(x_4, 0);
x_17 = lean::cnstr_get(x_3, 1);
lean::inc(x_17);
lean::dec(x_3);
x_18 = lean::cnstr_get(x_16, 0);
lean::inc(x_18);
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_release(x_16, 1);
 lean::cnstr_release(x_16, 2);
 x_20 = x_16;
} else {
 lean::dec_ref(x_16);
 x_20 = lean::box(0);
}
if (lean::is_scalar(x_20)) {
 x_21 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_21 = x_20;
}
lean::cnstr_set(x_21, 0, x_18);
lean::cnstr_set(x_21, 1, x_19);
lean::cnstr_set(x_21, 2, x_1);
lean::cnstr_set(x_4, 0, x_21);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_4);
lean::cnstr_set(x_22, 1, x_17);
lean::cnstr_set(x_2, 0, x_22);
return x_2;
}
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_23 = lean::cnstr_get(x_4, 0);
lean::inc(x_23);
lean::dec(x_4);
x_24 = lean::cnstr_get(x_3, 1);
lean::inc(x_24);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_25 = x_3;
} else {
 lean::dec_ref(x_3);
 x_25 = lean::box(0);
}
x_26 = lean::cnstr_get(x_23, 0);
lean::inc(x_26);
x_27 = lean::cnstr_get(x_23, 1);
lean::inc(x_27);
if (lean::is_exclusive(x_23)) {
 lean::cnstr_release(x_23, 0);
 lean::cnstr_release(x_23, 1);
 lean::cnstr_release(x_23, 2);
 x_28 = x_23;
} else {
 lean::dec_ref(x_23);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_26);
lean::cnstr_set(x_29, 1, x_27);
lean::cnstr_set(x_29, 2, x_1);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
if (lean::is_scalar(x_25)) {
 x_31 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_31 = x_25;
}
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_24);
lean::cnstr_set(x_2, 0, x_31);
return x_2;
}
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_2);
x_32 = lean::cnstr_get(x_4, 0);
lean::inc(x_32);
if (lean::is_exclusive(x_4)) {
 lean::cnstr_release(x_4, 0);
 x_33 = x_4;
} else {
 lean::dec_ref(x_4);
 x_33 = lean::box(0);
}
x_34 = lean::cnstr_get(x_3, 1);
lean::inc(x_34);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_35 = x_3;
} else {
 lean::dec_ref(x_3);
 x_35 = lean::box(0);
}
x_36 = lean::cnstr_get(x_32, 0);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_32, 1);
lean::inc(x_37);
if (lean::is_exclusive(x_32)) {
 lean::cnstr_release(x_32, 0);
 lean::cnstr_release(x_32, 1);
 lean::cnstr_release(x_32, 2);
 x_38 = x_32;
} else {
 lean::dec_ref(x_32);
 x_38 = lean::box(0);
}
if (lean::is_scalar(x_38)) {
 x_39 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_39 = x_38;
}
lean::cnstr_set(x_39, 0, x_36);
lean::cnstr_set(x_39, 1, x_37);
lean::cnstr_set(x_39, 2, x_1);
if (lean::is_scalar(x_33)) {
 x_40 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_40 = x_33;
}
lean::cnstr_set(x_40, 0, x_39);
if (lean::is_scalar(x_35)) {
 x_41 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_41 = x_35;
}
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_34);
x_42 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
return x_42;
}
}
}
case 1:
{
obj* x_43; obj* x_44; 
x_43 = lean::cnstr_get(x_2, 0);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
if (lean::obj_tag(x_44) == 0)
{
lean::dec(x_44);
lean::dec(x_43);
lean::dec(x_1);
return x_2;
}
else
{
uint8 x_45; 
x_45 = !lean::is_exclusive(x_2);
if (x_45 == 0)
{
obj* x_46; uint8 x_47; 
x_46 = lean::cnstr_get(x_2, 0);
lean::dec(x_46);
x_47 = !lean::is_exclusive(x_44);
if (x_47 == 0)
{
uint8 x_48; 
x_48 = !lean::is_exclusive(x_43);
if (x_48 == 0)
{
obj* x_49; obj* x_50; uint8 x_51; 
x_49 = lean::cnstr_get(x_44, 0);
x_50 = lean::cnstr_get(x_43, 0);
lean::dec(x_50);
x_51 = !lean::is_exclusive(x_49);
if (x_51 == 0)
{
obj* x_52; 
x_52 = lean::cnstr_get(x_49, 2);
lean::dec(x_52);
lean::cnstr_set(x_49, 2, x_1);
return x_2;
}
else
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = lean::cnstr_get(x_49, 0);
x_54 = lean::cnstr_get(x_49, 1);
lean::inc(x_54);
lean::inc(x_53);
lean::dec(x_49);
x_55 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_55, 0, x_53);
lean::cnstr_set(x_55, 1, x_54);
lean::cnstr_set(x_55, 2, x_1);
lean::cnstr_set(x_44, 0, x_55);
return x_2;
}
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; 
x_56 = lean::cnstr_get(x_44, 0);
x_57 = lean::cnstr_get(x_43, 1);
x_58 = lean::cnstr_get(x_43, 2);
x_59 = lean::cnstr_get(x_43, 3);
x_60 = lean::cnstr_get(x_43, 4);
lean::inc(x_60);
lean::inc(x_59);
lean::inc(x_58);
lean::inc(x_57);
lean::dec(x_43);
x_61 = lean::cnstr_get(x_56, 0);
lean::inc(x_61);
x_62 = lean::cnstr_get(x_56, 1);
lean::inc(x_62);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 lean::cnstr_release(x_56, 1);
 lean::cnstr_release(x_56, 2);
 x_63 = x_56;
} else {
 lean::dec_ref(x_56);
 x_63 = lean::box(0);
}
if (lean::is_scalar(x_63)) {
 x_64 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_64 = x_63;
}
lean::cnstr_set(x_64, 0, x_61);
lean::cnstr_set(x_64, 1, x_62);
lean::cnstr_set(x_64, 2, x_1);
lean::cnstr_set(x_44, 0, x_64);
x_65 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_65, 0, x_44);
lean::cnstr_set(x_65, 1, x_57);
lean::cnstr_set(x_65, 2, x_58);
lean::cnstr_set(x_65, 3, x_59);
lean::cnstr_set(x_65, 4, x_60);
lean::cnstr_set(x_2, 0, x_65);
return x_2;
}
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_66 = lean::cnstr_get(x_44, 0);
lean::inc(x_66);
lean::dec(x_44);
x_67 = lean::cnstr_get(x_43, 1);
lean::inc(x_67);
x_68 = lean::cnstr_get(x_43, 2);
lean::inc(x_68);
x_69 = lean::cnstr_get(x_43, 3);
lean::inc(x_69);
x_70 = lean::cnstr_get(x_43, 4);
lean::inc(x_70);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 lean::cnstr_release(x_43, 1);
 lean::cnstr_release(x_43, 2);
 lean::cnstr_release(x_43, 3);
 lean::cnstr_release(x_43, 4);
 x_71 = x_43;
} else {
 lean::dec_ref(x_43);
 x_71 = lean::box(0);
}
x_72 = lean::cnstr_get(x_66, 0);
lean::inc(x_72);
x_73 = lean::cnstr_get(x_66, 1);
lean::inc(x_73);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 lean::cnstr_release(x_66, 1);
 lean::cnstr_release(x_66, 2);
 x_74 = x_66;
} else {
 lean::dec_ref(x_66);
 x_74 = lean::box(0);
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_72);
lean::cnstr_set(x_75, 1, x_73);
lean::cnstr_set(x_75, 2, x_1);
x_76 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_76, 0, x_75);
if (lean::is_scalar(x_71)) {
 x_77 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_77 = x_71;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_67);
lean::cnstr_set(x_77, 2, x_68);
lean::cnstr_set(x_77, 3, x_69);
lean::cnstr_set(x_77, 4, x_70);
lean::cnstr_set(x_2, 0, x_77);
return x_2;
}
}
else
{
obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
lean::dec(x_2);
x_78 = lean::cnstr_get(x_44, 0);
lean::inc(x_78);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 x_79 = x_44;
} else {
 lean::dec_ref(x_44);
 x_79 = lean::box(0);
}
x_80 = lean::cnstr_get(x_43, 1);
lean::inc(x_80);
x_81 = lean::cnstr_get(x_43, 2);
lean::inc(x_81);
x_82 = lean::cnstr_get(x_43, 3);
lean::inc(x_82);
x_83 = lean::cnstr_get(x_43, 4);
lean::inc(x_83);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 lean::cnstr_release(x_43, 1);
 lean::cnstr_release(x_43, 2);
 lean::cnstr_release(x_43, 3);
 lean::cnstr_release(x_43, 4);
 x_84 = x_43;
} else {
 lean::dec_ref(x_43);
 x_84 = lean::box(0);
}
x_85 = lean::cnstr_get(x_78, 0);
lean::inc(x_85);
x_86 = lean::cnstr_get(x_78, 1);
lean::inc(x_86);
if (lean::is_exclusive(x_78)) {
 lean::cnstr_release(x_78, 0);
 lean::cnstr_release(x_78, 1);
 lean::cnstr_release(x_78, 2);
 x_87 = x_78;
} else {
 lean::dec_ref(x_78);
 x_87 = lean::box(0);
}
if (lean::is_scalar(x_87)) {
 x_88 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_88 = x_87;
}
lean::cnstr_set(x_88, 0, x_85);
lean::cnstr_set(x_88, 1, x_86);
lean::cnstr_set(x_88, 2, x_1);
if (lean::is_scalar(x_79)) {
 x_89 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_89 = x_79;
}
lean::cnstr_set(x_89, 0, x_88);
if (lean::is_scalar(x_84)) {
 x_90 = lean::alloc_cnstr(0, 5, 0);
} else {
 x_90 = x_84;
}
lean::cnstr_set(x_90, 0, x_89);
lean::cnstr_set(x_90, 1, x_80);
lean::cnstr_set(x_90, 2, x_81);
lean::cnstr_set(x_90, 3, x_82);
lean::cnstr_set(x_90, 4, x_83);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
return x_91;
}
}
}
case 2:
{
uint8 x_92; 
x_92 = !lean::is_exclusive(x_2);
if (x_92 == 0)
{
obj* x_93; uint8 x_94; 
x_93 = lean::cnstr_get(x_2, 0);
x_94 = !lean::is_exclusive(x_93);
if (x_94 == 0)
{
obj* x_95; obj* x_96; 
x_95 = lean::cnstr_get(x_93, 1);
x_96 = l_Lean_Parser_updateLast___main___at___private_init_lean_parser_token_3__updateTrailing___main___spec__1(x_1, x_95);
lean::cnstr_set(x_93, 1, x_96);
return x_2;
}
else
{
obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_97 = lean::cnstr_get(x_93, 0);
x_98 = lean::cnstr_get(x_93, 1);
x_99 = lean::cnstr_get(x_93, 2);
lean::inc(x_99);
lean::inc(x_98);
lean::inc(x_97);
lean::dec(x_93);
x_100 = l_Lean_Parser_updateLast___main___at___private_init_lean_parser_token_3__updateTrailing___main___spec__1(x_1, x_98);
x_101 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_101, 0, x_97);
lean::cnstr_set(x_101, 1, x_100);
lean::cnstr_set(x_101, 2, x_99);
lean::cnstr_set(x_2, 0, x_101);
return x_2;
}
}
else
{
obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
x_102 = lean::cnstr_get(x_2, 0);
lean::inc(x_102);
lean::dec(x_2);
x_103 = lean::cnstr_get(x_102, 0);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_102, 1);
lean::inc(x_104);
x_105 = lean::cnstr_get(x_102, 2);
lean::inc(x_105);
if (lean::is_exclusive(x_102)) {
 lean::cnstr_release(x_102, 0);
 lean::cnstr_release(x_102, 1);
 lean::cnstr_release(x_102, 2);
 x_106 = x_102;
} else {
 lean::dec_ref(x_102);
 x_106 = lean::box(0);
}
x_107 = l_Lean_Parser_updateLast___main___at___private_init_lean_parser_token_3__updateTrailing___main___spec__1(x_1, x_104);
if (lean::is_scalar(x_106)) {
 x_108 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_108 = x_106;
}
lean::cnstr_set(x_108, 0, x_103);
lean::cnstr_set(x_108, 1, x_107);
lean::cnstr_set(x_108, 2, x_105);
x_109 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_109, 0, x_108);
return x_109;
}
}
default: 
{
lean::dec(x_1);
return x_2;
}
}
}
}
obj* l___private_init_lean_parser_token_3__updateTrailing(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_parser_token_3__updateTrailing___main(x_1, x_2);
return x_3;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::apply_2(x_1, x_3, x_4);
return x_5;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_3);
x_6 = lean::apply_3(x_1, x_3, x_4, x_5);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
lean::dec(x_6);
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_7, 1);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_7, 2);
lean::inc(x_11);
lean::dec(x_7);
x_12 = lean::apply_4(x_2, x_9, x_3, x_10, x_8);
x_13 = !lean::is_exclusive(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; 
x_14 = lean::cnstr_get(x_12, 0);
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_14);
lean::cnstr_set(x_12, 0, x_15);
return x_12;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_16 = lean::cnstr_get(x_12, 0);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_12);
x_18 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_16);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8 x_20; 
lean::dec(x_3);
lean::dec(x_2);
x_20 = !lean::is_exclusive(x_6);
if (x_20 == 0)
{
obj* x_21; uint8 x_22; 
x_21 = lean::cnstr_get(x_6, 0);
lean::dec(x_21);
x_22 = !lean::is_exclusive(x_7);
if (x_22 == 0)
{
return x_6;
}
else
{
obj* x_23; uint8 x_24; obj* x_25; 
x_23 = lean::cnstr_get(x_7, 0);
x_24 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
lean::inc(x_23);
lean::dec(x_7);
x_25 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set_scalar(x_25, sizeof(void*)*1, x_24);
lean::cnstr_set(x_6, 0, x_25);
return x_6;
}
}
else
{
obj* x_26; obj* x_27; uint8 x_28; obj* x_29; obj* x_30; obj* x_31; 
x_26 = lean::cnstr_get(x_6, 1);
lean::inc(x_26);
lean::dec(x_6);
x_27 = lean::cnstr_get(x_7, 0);
lean::inc(x_27);
x_28 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_29 = x_7;
} else {
 lean::dec_ref(x_7);
 x_29 = lean::box(0);
}
if (lean::is_scalar(x_29)) {
 x_30 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_30 = x_29;
}
lean::cnstr_set(x_30, 0, x_27);
lean::cnstr_set_scalar(x_30, sizeof(void*)*1, x_28);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_26);
return x_31;
}
}
}
}
obj* l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 0);
return x_3;
}
}
obj* l_Lean_Parser_withTrailing___rarg___lambda__1(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; 
x_3 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::inc(x_1);
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_1);
lean::cnstr_set(x_4, 2, x_3);
x_5 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_5, 0, x_4);
lean::cnstr_set(x_5, 1, x_2);
return x_5;
}
}
obj* l_Lean_Parser_withTrailing___rarg___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_Parser_whitespace(x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_5);
if (x_7 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::cnstr_get(x_5, 0);
lean::dec(x_8);
x_9 = !lean::is_exclusive(x_6);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_6, 1);
x_11 = lean::cnstr_get(x_6, 2);
x_12 = lean::cnstr_get(x_6, 0);
lean::dec(x_12);
lean::inc(x_10);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_1);
lean::cnstr_set(x_13, 1, x_10);
x_14 = l_Lean_Parser_finishCommentBlock___closed__2;
lean::cnstr_set(x_6, 2, x_14);
lean::cnstr_set(x_6, 0, x_13);
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_6);
lean::cnstr_set(x_5, 0, x_15);
return x_5;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_16 = lean::cnstr_get(x_6, 1);
x_17 = lean::cnstr_get(x_6, 2);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_6);
lean::inc(x_16);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_1);
lean::cnstr_set(x_18, 1, x_16);
x_19 = l_Lean_Parser_finishCommentBlock___closed__2;
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_16);
lean::cnstr_set(x_20, 2, x_19);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_20);
lean::cnstr_set(x_5, 0, x_21);
return x_5;
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_5, 1);
lean::inc(x_22);
lean::dec(x_5);
x_23 = lean::cnstr_get(x_6, 1);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_6, 2);
lean::inc(x_24);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_25 = x_6;
} else {
 lean::dec_ref(x_6);
 x_25 = lean::box(0);
}
lean::inc(x_23);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_1);
lean::cnstr_set(x_26, 1, x_23);
x_27 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_25)) {
 x_28 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_28 = x_25;
}
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_23);
lean::cnstr_set(x_28, 2, x_27);
x_29 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_22);
return x_30;
}
}
else
{
uint8 x_31; 
lean::dec(x_1);
x_31 = !lean::is_exclusive(x_5);
if (x_31 == 0)
{
obj* x_32; uint8 x_33; 
x_32 = lean::cnstr_get(x_5, 0);
lean::dec(x_32);
x_33 = !lean::is_exclusive(x_6);
if (x_33 == 0)
{
return x_5;
}
else
{
obj* x_34; uint8 x_35; obj* x_36; 
x_34 = lean::cnstr_get(x_6, 0);
x_35 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
lean::inc(x_34);
lean::dec(x_6);
x_36 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_35);
lean::cnstr_set(x_5, 0, x_36);
return x_5;
}
}
else
{
obj* x_37; obj* x_38; uint8 x_39; obj* x_40; obj* x_41; obj* x_42; 
x_37 = lean::cnstr_get(x_5, 1);
lean::inc(x_37);
lean::dec(x_5);
x_38 = lean::cnstr_get(x_6, 0);
lean::inc(x_38);
x_39 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_40 = x_6;
} else {
 lean::dec_ref(x_6);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_38);
lean::cnstr_set_scalar(x_41, sizeof(void*)*1, x_39);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_37);
return x_42;
}
}
}
}
obj* l_Lean_Parser_withTrailing___rarg___lambda__3(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
lean::inc(x_4);
lean::dec(x_1);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = l___private_init_lean_parser_token_3__updateTrailing___main(x_3, x_2);
x_7 = lean::apply_2(x_5, lean::box(0), x_6);
return x_7;
}
}
obj* _init_l_Lean_Parser_withTrailing___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__2___boxed), 4, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_Lean_Parser_withTrailing___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
x_6 = l_Lean_Parser_withTrailing___rarg___closed__1;
x_7 = lean::apply_2(x_3, lean::box(0), x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__3), 3, 2);
lean::closure_set(x_8, 0, x_1);
lean::closure_set(x_8, 1, x_4);
x_9 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_8);
return x_9;
}
}
obj* l_Lean_Parser_withTrailing(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_withTrailing___rarg___lambda__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_withTrailing___rarg___lambda__2(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_withTrailing___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_withTrailing___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_withTrailing___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_withTrailing(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_mkRawRes(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
lean::inc(x_2);
lean::inc(x_1);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
lean::inc(x_1, 2);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_1);
x_5 = lean::cnstr_get(x_1, 1);
lean::inc(x_5);
lean::dec(x_1);
lean::inc(x_2);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_2);
lean::cnstr_set(x_6, 1, x_2);
x_7 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_5);
lean::cnstr_set(x_7, 2, x_6);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = l_Lean_Parser_Substring_toString(x_3);
lean::dec(x_3);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_8);
lean::cnstr_set(x_10, 1, x_9);
x_11 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
return x_11;
}
}
obj* l_Lean_Parser_raw___rarg___lambda__1(obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_mkRawRes(x_1, x_6);
if (x_2 == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_5);
x_8 = lean::cnstr_get(x_3, 0);
lean::inc(x_8);
lean::dec(x_3);
x_9 = lean::cnstr_get(x_8, 1);
lean::inc(x_9);
lean::dec(x_8);
x_10 = lean::apply_2(x_9, lean::box(0), x_7);
return x_10;
}
else
{
obj* x_11; 
x_11 = l_Lean_Parser_withTrailing___rarg(x_3, x_4, x_5, x_7);
return x_11;
}
}
}
obj* l_Lean_Parser_raw___rarg___lambda__2(obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::box(x_2);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_raw___rarg___lambda__1___boxed), 6, 5);
lean::closure_set(x_10, 0, x_1);
lean::closure_set(x_10, 1, x_9);
lean::closure_set(x_10, 2, x_3);
lean::closure_set(x_10, 3, x_4);
lean::closure_set(x_10, 4, x_5);
x_11 = lean::apply_4(x_6, lean::box(0), lean::box(0), x_7, x_10);
return x_11;
}
}
obj* l_Lean_Parser_raw___rarg___lambda__3(uint8 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::box(x_1);
lean::inc(x_5);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_raw___rarg___lambda__2___boxed), 8, 7);
lean::closure_set(x_10, 0, x_8);
lean::closure_set(x_10, 1, x_9);
lean::closure_set(x_10, 2, x_2);
lean::closure_set(x_10, 3, x_3);
lean::closure_set(x_10, 4, x_4);
lean::closure_set(x_10, 5, x_5);
lean::closure_set(x_10, 6, x_6);
x_11 = lean::apply_4(x_5, lean::box(0), lean::box(0), x_7, x_10);
return x_11;
}
}
obj* l_Lean_Parser_raw___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, uint8 x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_7 = lean::cnstr_get(x_1, 1);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_2, 0);
lean::inc(x_8);
x_9 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_10 = lean::apply_2(x_8, lean::box(0), x_9);
x_11 = lean::box(x_6);
lean::inc(x_10);
lean::inc(x_7);
x_12 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_raw___rarg___lambda__3___boxed), 8, 7);
lean::closure_set(x_12, 0, x_11);
lean::closure_set(x_12, 1, x_1);
lean::closure_set(x_12, 2, x_2);
lean::closure_set(x_12, 3, x_3);
lean::closure_set(x_12, 4, x_7);
lean::closure_set(x_12, 5, x_10);
lean::closure_set(x_12, 6, x_5);
x_13 = lean::apply_4(x_7, lean::box(0), lean::box(0), x_10, x_12);
return x_13;
}
}
obj* l_Lean_Parser_raw(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_raw___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Lean_Parser_raw___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = l_Lean_Parser_raw___rarg___lambda__1(x_1, x_7, x_3, x_4, x_5, x_6);
lean::dec(x_4);
return x_8;
}
}
obj* l_Lean_Parser_raw___rarg___lambda__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
uint8 x_9; obj* x_10; 
x_9 = lean::unbox(x_2);
lean::dec(x_2);
x_10 = l_Lean_Parser_raw___rarg___lambda__2(x_1, x_9, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_8);
return x_10;
}
}
obj* l_Lean_Parser_raw___rarg___lambda__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
uint8 x_9; obj* x_10; 
x_9 = lean::unbox(x_1);
lean::dec(x_1);
x_10 = l_Lean_Parser_raw___rarg___lambda__3(x_9, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
obj* l_Lean_Parser_raw___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_raw___rarg(x_1, x_2, x_3, x_4, x_5, x_7);
return x_8;
}
}
obj* l_Lean_Parser_raw___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_raw(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_raw_tokens(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, uint8 x_7) {
_start:
{
obj* x_8; 
x_8 = lean::box(0);
return x_8;
}
}
obj* l_Lean_Parser_raw_tokens___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
uint8 x_8; obj* x_9; 
x_8 = lean::unbox(x_7);
lean::dec(x_7);
x_9 = l_Lean_Parser_raw_tokens(x_1, x_2, x_3, x_4, x_5, x_6, x_8);
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_9;
}
}
obj* l_Lean_Parser_raw_view___rarg___lambda__1(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; obj* x_3; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_3, 0, x_2);
return x_3;
}
else
{
obj* x_4; 
x_4 = lean::box(0);
return x_4;
}
}
}
obj* l_Lean_Parser_raw_view___rarg___lambda__2(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = lean::box(3);
return x_2;
}
else
{
obj* x_3; obj* x_4; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
x_4 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_4, 0, x_3);
return x_4;
}
}
}
obj* _init_l_Lean_Parser_raw_view___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_raw_view___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_raw_view___rarg___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_raw_view___rarg___lambda__2___boxed), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_raw_view___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, uint8 x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = l_Lean_Parser_raw_view___rarg___closed__1;
x_8 = l_Lean_Parser_raw_view___rarg___closed__2;
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_Lean_Parser_raw_view(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_raw_view___rarg___boxed), 6, 0);
return x_2;
}
}
obj* l_Lean_Parser_raw_view___rarg___lambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_raw_view___rarg___lambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_raw_view___rarg___lambda__2___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_raw_view___rarg___lambda__2(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_raw_view___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_raw_view___rarg(x_1, x_2, x_3, x_4, x_5, x_7);
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_8;
}
}
obj* l_Lean_Parser_raw_view___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_raw_view(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_rawStr_Lean_Parser_HasTokens(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, uint8 x_6) {
_start:
{
obj* x_7; 
x_7 = lean::box(0);
return x_7;
}
}
obj* l_Lean_Parser_rawStr_Lean_Parser_HasTokens___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_rawStr_Lean_Parser_HasTokens(x_1, x_2, x_3, x_4, x_5, x_7);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_8;
}
}
obj* l_Lean_Parser_rawStr_Lean_Parser_HasView___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint8 x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_4);
x_6 = l_String_quote(x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
lean::inc(x_2);
lean::inc(x_1);
x_8 = l_Lean_Parser_MonadParsec_strCore___rarg(x_1, x_2, x_4, x_7);
x_9 = l_Lean_Parser_raw_view___rarg(x_1, x_2, x_3, lean::box(0), x_8, x_5);
lean::dec(x_8);
lean::dec(x_2);
lean::dec(x_1);
return x_9;
}
}
obj* l_Lean_Parser_rawStr_Lean_Parser_HasView(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_rawStr_Lean_Parser_HasView___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_rawStr_Lean_Parser_HasView___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_5);
lean::dec(x_5);
x_7 = l_Lean_Parser_rawStr_Lean_Parser_HasView___rarg(x_1, x_2, x_3, x_4, x_6);
lean::dec(x_3);
return x_7;
}
}
obj* l_Lean_Parser_rawStr_Lean_Parser_HasView___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_rawStr_Lean_Parser_HasView(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_rawStr___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint8 x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
lean::inc(x_4);
x_6 = l_String_quote(x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_7, 0, x_6);
lean::inc(x_2);
lean::inc(x_1);
x_8 = l_Lean_Parser_MonadParsec_strCore___rarg(x_1, x_2, x_4, x_7);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
x_11 = l_Lean_Parser_MonadParsec_leftOver___rarg___closed__1;
x_12 = lean::apply_2(x_10, lean::box(0), x_11);
x_13 = lean::box(x_5);
lean::inc(x_12);
lean::inc(x_9);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_raw___rarg___lambda__3___boxed), 8, 7);
lean::closure_set(x_14, 0, x_13);
lean::closure_set(x_14, 1, x_1);
lean::closure_set(x_14, 2, x_2);
lean::closure_set(x_14, 3, x_3);
lean::closure_set(x_14, 4, x_9);
lean::closure_set(x_14, 5, x_12);
lean::closure_set(x_14, 6, x_8);
x_15 = lean::apply_4(x_9, lean::box(0), lean::box(0), x_12, x_14);
return x_15;
}
}
obj* l_Lean_Parser_rawStr(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_rawStr___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_rawStr___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_5);
lean::dec(x_5);
x_7 = l_Lean_Parser_rawStr___rarg(x_1, x_2, x_3, x_4, x_6);
return x_7;
}
}
obj* l_Lean_Parser_rawStr___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_rawStr(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_rawStr_viewDefault___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, uint8 x_5) {
_start:
{
obj* x_6; 
x_6 = lean::box(0);
return x_6;
}
}
obj* l_Lean_Parser_rawStr_viewDefault(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_rawStr_viewDefault___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_rawStr_viewDefault___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; obj* x_7; 
x_6 = lean::unbox(x_5);
lean::dec(x_5);
x_7 = l_Lean_Parser_rawStr_viewDefault___rarg(x_1, x_2, x_3, x_4, x_6);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* l_Lean_Parser_rawStr_viewDefault___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_rawStr_viewDefault(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_detailIdentPartEscaped() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("detailIdentPartEscaped");
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
obj* _init_l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_2);
lean::cnstr_set(x_5, 1, x_4);
x_6 = l_Lean_Parser_detailIdentPartEscaped;
x_7 = l_Lean_Parser_Syntax_mkNode(x_6, x_5);
return x_7;
}
}
obj* _init_l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::cnstr_get(x_1, 2);
x_5 = lean::box(0);
if (lean::obj_tag(x_2) == 0)
{
if (lean::obj_tag(x_3) == 0)
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; 
x_6 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__1;
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_7 = lean::cnstr_get(x_4, 0);
lean::inc(x_7);
x_8 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_5);
x_10 = lean::box(3);
x_11 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = l_Lean_Parser_detailIdentPartEscaped;
x_14 = l_Lean_Parser_Syntax_mkNode(x_13, x_12);
return x_14;
}
}
else
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_3, 0);
lean::inc(x_15);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
if (lean::obj_tag(x_4) == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_17 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_18 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_17);
x_19 = lean::box(3);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
x_21 = l_Lean_Parser_detailIdentPartEscaped;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_23 = lean::cnstr_get(x_4, 0);
lean::inc(x_23);
x_24 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_24, 0, x_23);
x_25 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_5);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_16);
lean::cnstr_set(x_26, 1, x_25);
x_27 = lean::box(3);
x_28 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_26);
x_29 = l_Lean_Parser_detailIdentPartEscaped;
x_30 = l_Lean_Parser_Syntax_mkNode(x_29, x_28);
return x_30;
}
}
}
else
{
obj* x_31; obj* x_32; 
x_31 = lean::cnstr_get(x_2, 0);
lean::inc(x_31);
x_32 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
if (lean::obj_tag(x_3) == 0)
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_33 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__3;
x_34 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_33);
x_35 = l_Lean_Parser_detailIdentPartEscaped;
x_36 = l_Lean_Parser_Syntax_mkNode(x_35, x_34);
return x_36;
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_37 = lean::cnstr_get(x_4, 0);
lean::inc(x_37);
x_38 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_5);
x_40 = lean::box(3);
x_41 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_39);
x_42 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_42, 0, x_32);
lean::cnstr_set(x_42, 1, x_41);
x_43 = l_Lean_Parser_detailIdentPartEscaped;
x_44 = l_Lean_Parser_Syntax_mkNode(x_43, x_42);
return x_44;
}
}
else
{
obj* x_45; obj* x_46; 
x_45 = lean::cnstr_get(x_3, 0);
lean::inc(x_45);
x_46 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_46, 0, x_45);
if (lean::obj_tag(x_4) == 0)
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_47 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2;
x_48 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_47);
x_49 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_49, 0, x_32);
lean::cnstr_set(x_49, 1, x_48);
x_50 = l_Lean_Parser_detailIdentPartEscaped;
x_51 = l_Lean_Parser_Syntax_mkNode(x_50, x_49);
return x_51;
}
else
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_52 = lean::cnstr_get(x_4, 0);
lean::inc(x_52);
x_53 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_53, 0, x_52);
x_54 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_5);
x_55 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_55, 0, x_46);
lean::cnstr_set(x_55, 1, x_54);
x_56 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_56, 0, x_32);
lean::cnstr_set(x_56, 1, x_55);
x_57 = l_Lean_Parser_detailIdentPartEscaped;
x_58 = l_Lean_Parser_Syntax_mkNode(x_57, x_56);
return x_58;
}
}
}
}
}
obj* _init_l_Lean_Parser_detailIdentPartEscaped_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_2, 0, x_1);
lean::cnstr_set(x_2, 1, x_1);
lean::cnstr_set(x_2, 2, x_1);
return x_2;
}
}
obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_32; 
x_32 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_32) == 0)
{
obj* x_33; 
lean::dec(x_32);
x_33 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___lambda__1___closed__1;
return x_33;
}
else
{
obj* x_34; obj* x_35; 
x_34 = lean::cnstr_get(x_32, 0);
lean::inc(x_34);
lean::dec(x_32);
x_35 = lean::cnstr_get(x_34, 1);
lean::inc(x_35);
lean::dec(x_34);
if (lean::obj_tag(x_35) == 0)
{
obj* x_36; 
x_36 = lean::box(3);
x_2 = x_35;
x_3 = x_36;
goto block_31;
}
else
{
obj* x_37; obj* x_38; 
x_37 = lean::cnstr_get(x_35, 0);
lean::inc(x_37);
x_38 = lean::cnstr_get(x_35, 1);
lean::inc(x_38);
lean::dec(x_35);
x_2 = x_38;
x_3 = x_37;
goto block_31;
}
}
block_31:
{
obj* x_4; 
if (lean::obj_tag(x_3) == 0)
{
obj* x_28; obj* x_29; 
x_28 = lean::cnstr_get(x_3, 0);
lean::inc(x_28);
lean::dec(x_3);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
x_4 = x_29;
goto block_27;
}
else
{
obj* x_30; 
lean::dec(x_3);
x_30 = lean::box(0);
x_4 = x_30;
goto block_27;
}
block_27:
{
obj* x_5; obj* x_6; obj* x_13; obj* x_14; 
if (lean::obj_tag(x_2) == 0)
{
obj* x_24; 
x_24 = lean::box(3);
x_13 = x_2;
x_14 = x_24;
goto block_23;
}
else
{
obj* x_25; obj* x_26; 
x_25 = lean::cnstr_get(x_2, 0);
lean::inc(x_25);
x_26 = lean::cnstr_get(x_2, 1);
lean::inc(x_26);
lean::dec(x_2);
x_13 = x_26;
x_14 = x_25;
goto block_23;
}
block_12:
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_4);
lean::cnstr_set(x_9, 1, x_5);
lean::cnstr_set(x_9, 2, x_8);
return x_9;
}
else
{
obj* x_10; obj* x_11; 
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_4);
lean::cnstr_set(x_11, 1, x_5);
lean::cnstr_set(x_11, 2, x_10);
return x_11;
}
}
block_23:
{
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
lean::dec(x_14);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
if (lean::obj_tag(x_13) == 0)
{
obj* x_17; obj* x_18; 
lean::dec(x_13);
x_17 = lean::box(0);
x_18 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_18, 0, x_4);
lean::cnstr_set(x_18, 1, x_16);
lean::cnstr_set(x_18, 2, x_17);
return x_18;
}
else
{
obj* x_19; 
x_19 = lean::cnstr_get(x_13, 0);
lean::inc(x_19);
lean::dec(x_13);
x_5 = x_16;
x_6 = x_19;
goto block_12;
}
}
else
{
obj* x_20; 
lean::dec(x_14);
x_20 = lean::box(0);
if (lean::obj_tag(x_13) == 0)
{
obj* x_21; 
lean::dec(x_13);
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_4);
lean::cnstr_set(x_21, 1, x_20);
lean::cnstr_set(x_21, 2, x_20);
return x_21;
}
else
{
obj* x_22; 
x_22 = lean::cnstr_get(x_13, 0);
lean::inc(x_22);
lean::dec(x_13);
x_5 = x_20;
x_6 = x_22;
goto block_12;
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_detailIdentPartEscaped_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPartEscaped_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___boxed), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_detailIdentPartEscaped_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_detailIdentPartEscaped_HasView_x27;
return x_1;
}
}
obj* _init_l_Lean_Parser_detailIdentPart() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("detailIdentPart");
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
obj* _init_l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(0u);
x_3 = lean_name_mk_numeral(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_nat_obj(1u);
x_4 = lean_name_mk_numeral(x_2, x_3);
x_5 = lean::box(3);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
x_7 = l_Lean_Parser_Syntax_mkNode(x_4, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_detailIdentPart;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(1u);
x_3 = lean_name_mk_numeral(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_3 = lean::cnstr_get(x_1, 0);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_Parser_detailIdentPartEscaped_HasView;
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
x_6 = lean::apply_1(x_5, x_3);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
x_8 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__1;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_2);
x_11 = l_Lean_Parser_detailIdentPart;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
return x_12;
}
else
{
obj* x_13; 
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
lean::dec(x_13);
x_14 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__2;
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
lean::dec(x_13);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_2);
x_18 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__3;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_2);
x_21 = l_Lean_Parser_detailIdentPart;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
}
}
}
obj* _init_l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_detailIdentPartEscaped_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("detailIdentPart");
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
obj* l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_2);
x_3 = l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__2;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
lean::dec(x_4);
x_7 = l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__3;
x_8 = lean_name_dec_eq(x_5, x_7);
lean::dec(x_5);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_6);
x_9 = l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__2;
return x_9;
}
else
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
lean::dec(x_6);
x_10 = l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__2;
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; 
lean::dec(x_11);
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
lean::dec(x_6);
x_13 = l_Lean_Parser_Syntax_asNode___main(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
lean::dec(x_13);
x_14 = l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__2;
return x_14;
}
else
{
uint8 x_15; 
x_15 = !lean::is_exclusive(x_13);
if (x_15 == 0)
{
obj* x_16; obj* x_17; 
x_16 = lean::cnstr_get(x_13, 0);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
switch (lean::obj_tag(x_17)) {
case 0:
{
obj* x_18; 
lean::dec(x_17);
lean::free_heap_obj(x_13);
lean::dec(x_16);
x_18 = l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__2;
return x_18;
}
case 1:
{
obj* x_19; 
lean::dec(x_17);
lean::free_heap_obj(x_13);
lean::dec(x_16);
x_19 = l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__2;
return x_19;
}
default: 
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint8 x_24; 
x_20 = lean::cnstr_get(x_16, 1);
lean::inc(x_20);
lean::dec(x_16);
x_21 = lean::cnstr_get(x_17, 0);
lean::inc(x_21);
x_22 = lean::cnstr_get(x_17, 1);
lean::inc(x_22);
lean::dec(x_17);
x_23 = lean::box(0);
x_24 = lean_name_dec_eq(x_21, x_23);
lean::dec(x_21);
if (x_24 == 0)
{
obj* x_25; 
lean::dec(x_22);
lean::dec(x_20);
lean::free_heap_obj(x_13);
x_25 = l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__2;
return x_25;
}
else
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_26; 
lean::dec(x_22);
lean::dec(x_20);
lean::free_heap_obj(x_13);
x_26 = l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__2;
return x_26;
}
else
{
obj* x_27; 
x_27 = lean::cnstr_get(x_20, 1);
lean::inc(x_27);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; obj* x_29; uint8 x_30; 
lean::dec(x_27);
x_28 = lean::cnstr_get(x_20, 0);
lean::inc(x_28);
lean::dec(x_20);
x_29 = lean::mk_nat_obj(0u);
x_30 = lean::nat_dec_eq(x_22, x_29);
lean::dec(x_22);
if (x_30 == 0)
{
if (lean::obj_tag(x_28) == 0)
{
obj* x_31; obj* x_32; 
x_31 = lean::cnstr_get(x_28, 0);
lean::inc(x_31);
lean::dec(x_28);
lean::cnstr_set(x_13, 0, x_31);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_13);
return x_32;
}
else
{
obj* x_33; 
lean::dec(x_28);
lean::free_heap_obj(x_13);
x_33 = l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__1;
return x_33;
}
}
else
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
lean::free_heap_obj(x_13);
x_34 = l_Lean_Parser_detailIdentPartEscaped_HasView;
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
x_36 = lean::apply_1(x_35, x_28);
x_37 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_37, 0, x_36);
return x_37;
}
}
else
{
obj* x_38; 
lean::dec(x_27);
lean::dec(x_22);
lean::dec(x_20);
lean::free_heap_obj(x_13);
x_38 = l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__2;
return x_38;
}
}
}
}
}
}
else
{
obj* x_39; obj* x_40; 
x_39 = lean::cnstr_get(x_13, 0);
lean::inc(x_39);
lean::dec(x_13);
x_40 = lean::cnstr_get(x_39, 0);
lean::inc(x_40);
switch (lean::obj_tag(x_40)) {
case 0:
{
obj* x_41; 
lean::dec(x_40);
lean::dec(x_39);
x_41 = l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__2;
return x_41;
}
case 1:
{
obj* x_42; 
lean::dec(x_40);
lean::dec(x_39);
x_42 = l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__2;
return x_42;
}
default: 
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; uint8 x_47; 
x_43 = lean::cnstr_get(x_39, 1);
lean::inc(x_43);
lean::dec(x_39);
x_44 = lean::cnstr_get(x_40, 0);
lean::inc(x_44);
x_45 = lean::cnstr_get(x_40, 1);
lean::inc(x_45);
lean::dec(x_40);
x_46 = lean::box(0);
x_47 = lean_name_dec_eq(x_44, x_46);
lean::dec(x_44);
if (x_47 == 0)
{
obj* x_48; 
lean::dec(x_45);
lean::dec(x_43);
x_48 = l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__2;
return x_48;
}
else
{
if (lean::obj_tag(x_43) == 0)
{
obj* x_49; 
lean::dec(x_45);
lean::dec(x_43);
x_49 = l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__2;
return x_49;
}
else
{
obj* x_50; 
x_50 = lean::cnstr_get(x_43, 1);
lean::inc(x_50);
if (lean::obj_tag(x_50) == 0)
{
obj* x_51; obj* x_52; uint8 x_53; 
lean::dec(x_50);
x_51 = lean::cnstr_get(x_43, 0);
lean::inc(x_51);
lean::dec(x_43);
x_52 = lean::mk_nat_obj(0u);
x_53 = lean::nat_dec_eq(x_45, x_52);
lean::dec(x_45);
if (x_53 == 0)
{
if (lean::obj_tag(x_51) == 0)
{
obj* x_54; obj* x_55; obj* x_56; 
x_54 = lean::cnstr_get(x_51, 0);
lean::inc(x_54);
lean::dec(x_51);
x_55 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_55, 0, x_54);
x_56 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_56, 0, x_55);
return x_56;
}
else
{
obj* x_57; 
lean::dec(x_51);
x_57 = l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__1;
return x_57;
}
}
else
{
obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_58 = l_Lean_Parser_detailIdentPartEscaped_HasView;
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_60 = lean::apply_1(x_59, x_51);
x_61 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_61, 0, x_60);
return x_61;
}
}
else
{
obj* x_62; 
lean::dec(x_50);
lean::dec(x_45);
lean::dec(x_43);
x_62 = l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__2;
return x_62;
}
}
}
}
}
}
}
}
else
{
obj* x_63; 
lean::dec(x_11);
lean::dec(x_6);
x_63 = l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__2;
return x_63;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_detailIdentPart_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_detailIdentPart_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_detailIdentPart_HasView_x27;
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__3(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_1);
x_8 = l_String_OldIterator_hasNext___main(x_3);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_7);
x_9 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_9;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = l_String_OldIterator_curr___main(x_3);
x_11 = l_Lean_isIdEndEscape(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::string_push(x_2, x_10);
x_13 = l_String_OldIterator_next___main(x_3);
x_1 = x_7;
x_2 = x_12;
x_3 = x_13;
goto _start;
}
else
{
obj* x_15; 
lean::dec(x_7);
x_15 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_15;
}
}
}
else
{
obj* x_16; 
lean::dec(x_1);
x_16 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_16;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_String_OldIterator_remaining___main(x_3);
x_6 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__3(x_5, x_1, x_3);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_4);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_String_OldIterator_hasNext___main(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_5 = lean::box(0);
x_6 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_7 = l_mjoin___rarg___closed__1;
x_8 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_6, x_7, x_5, x_5, x_1, x_2, x_3);
x_9 = !lean::is_exclusive(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_8, 0);
x_11 = lean::cnstr_get(x_8, 1);
x_12 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_13 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_10);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint32 x_18; obj* x_19; obj* x_20; uint8 x_21; 
lean::free_heap_obj(x_8);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_13, 1);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_13, 2);
lean::inc(x_16);
lean::dec(x_13);
x_17 = l_String_splitAux___main___closed__1;
x_18 = lean::unbox_uint32(x_14);
lean::dec(x_14);
x_19 = lean::string_push(x_17, x_18);
x_20 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__2(x_19, x_1, x_15, x_11);
x_21 = !lean::is_exclusive(x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_23; 
x_22 = lean::cnstr_get(x_20, 0);
x_23 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_22);
lean::cnstr_set(x_20, 0, x_23);
return x_20;
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_24 = lean::cnstr_get(x_20, 0);
x_25 = lean::cnstr_get(x_20, 1);
lean::inc(x_25);
lean::inc(x_24);
lean::dec(x_20);
x_26 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_24);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8 x_28; 
x_28 = !lean::is_exclusive(x_13);
if (x_28 == 0)
{
lean::cnstr_set(x_8, 0, x_13);
return x_8;
}
else
{
obj* x_29; uint8 x_30; obj* x_31; 
x_29 = lean::cnstr_get(x_13, 0);
x_30 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
lean::inc(x_29);
lean::dec(x_13);
x_31 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set_scalar(x_31, sizeof(void*)*1, x_30);
lean::cnstr_set(x_8, 0, x_31);
return x_8;
}
}
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_32 = lean::cnstr_get(x_8, 0);
x_33 = lean::cnstr_get(x_8, 1);
lean::inc(x_33);
lean::inc(x_32);
lean::dec(x_8);
x_34 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_34, x_32);
if (lean::obj_tag(x_35) == 0)
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; uint32 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_35, 1);
lean::inc(x_37);
x_38 = lean::cnstr_get(x_35, 2);
lean::inc(x_38);
lean::dec(x_35);
x_39 = l_String_splitAux___main___closed__1;
x_40 = lean::unbox_uint32(x_36);
lean::dec(x_36);
x_41 = lean::string_push(x_39, x_40);
x_42 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__2(x_41, x_1, x_37, x_33);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_42, 1);
lean::inc(x_44);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 lean::cnstr_release(x_42, 1);
 x_45 = x_42;
} else {
 lean::dec_ref(x_42);
 x_45 = lean::box(0);
}
x_46 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_43);
if (lean::is_scalar(x_45)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_45;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_44);
return x_47;
}
else
{
obj* x_48; uint8 x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::cnstr_get(x_35, 0);
lean::inc(x_48);
x_49 = lean::cnstr_get_scalar<uint8>(x_35, sizeof(void*)*1);
if (lean::is_exclusive(x_35)) {
 lean::cnstr_release(x_35, 0);
 x_50 = x_35;
} else {
 lean::dec_ref(x_35);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_48);
lean::cnstr_set_scalar(x_51, sizeof(void*)*1, x_49);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_33);
return x_52;
}
}
}
else
{
uint32 x_53; uint8 x_54; 
x_53 = l_String_OldIterator_curr___main(x_2);
x_54 = l_Lean_isIdEndEscape(x_53);
if (x_54 == 0)
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; uint8 x_60; 
x_55 = l_String_OldIterator_next___main(x_2);
x_56 = lean::box(0);
x_57 = l_String_splitAux___main___closed__1;
x_58 = lean::string_push(x_57, x_53);
x_59 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__2(x_58, x_1, x_55, x_3);
x_60 = !lean::is_exclusive(x_59);
if (x_60 == 0)
{
obj* x_61; obj* x_62; 
x_61 = lean::cnstr_get(x_59, 0);
x_62 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_56, x_61);
lean::cnstr_set(x_59, 0, x_62);
return x_59;
}
else
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_63 = lean::cnstr_get(x_59, 0);
x_64 = lean::cnstr_get(x_59, 1);
lean::inc(x_64);
lean::inc(x_63);
lean::dec(x_59);
x_65 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_56, x_63);
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_64);
return x_66;
}
}
else
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; uint8 x_74; 
x_67 = l_Char_quoteCore(x_53);
x_68 = l_Char_HasRepr___closed__1;
x_69 = lean::string_append(x_68, x_67);
lean::dec(x_67);
x_70 = lean::string_append(x_69, x_68);
x_71 = lean::box(0);
x_72 = l_mjoin___rarg___closed__1;
x_73 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_70, x_72, x_71, x_71, x_1, x_2, x_3);
x_74 = !lean::is_exclusive(x_73);
if (x_74 == 0)
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; 
x_75 = lean::cnstr_get(x_73, 0);
x_76 = lean::cnstr_get(x_73, 1);
x_77 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_78 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_77, x_75);
if (lean::obj_tag(x_78) == 0)
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; uint32 x_83; obj* x_84; obj* x_85; uint8 x_86; 
lean::free_heap_obj(x_73);
x_79 = lean::cnstr_get(x_78, 0);
lean::inc(x_79);
x_80 = lean::cnstr_get(x_78, 1);
lean::inc(x_80);
x_81 = lean::cnstr_get(x_78, 2);
lean::inc(x_81);
lean::dec(x_78);
x_82 = l_String_splitAux___main___closed__1;
x_83 = lean::unbox_uint32(x_79);
lean::dec(x_79);
x_84 = lean::string_push(x_82, x_83);
x_85 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__2(x_84, x_1, x_80, x_76);
x_86 = !lean::is_exclusive(x_85);
if (x_86 == 0)
{
obj* x_87; obj* x_88; 
x_87 = lean::cnstr_get(x_85, 0);
x_88 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_81, x_87);
lean::cnstr_set(x_85, 0, x_88);
return x_85;
}
else
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_89 = lean::cnstr_get(x_85, 0);
x_90 = lean::cnstr_get(x_85, 1);
lean::inc(x_90);
lean::inc(x_89);
lean::dec(x_85);
x_91 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_81, x_89);
x_92 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_90);
return x_92;
}
}
else
{
uint8 x_93; 
x_93 = !lean::is_exclusive(x_78);
if (x_93 == 0)
{
lean::cnstr_set(x_73, 0, x_78);
return x_73;
}
else
{
obj* x_94; uint8 x_95; obj* x_96; 
x_94 = lean::cnstr_get(x_78, 0);
x_95 = lean::cnstr_get_scalar<uint8>(x_78, sizeof(void*)*1);
lean::inc(x_94);
lean::dec(x_78);
x_96 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_96, 0, x_94);
lean::cnstr_set_scalar(x_96, sizeof(void*)*1, x_95);
lean::cnstr_set(x_73, 0, x_96);
return x_73;
}
}
}
else
{
obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_97 = lean::cnstr_get(x_73, 0);
x_98 = lean::cnstr_get(x_73, 1);
lean::inc(x_98);
lean::inc(x_97);
lean::dec(x_73);
x_99 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_100 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_99, x_97);
if (lean::obj_tag(x_100) == 0)
{
obj* x_101; obj* x_102; obj* x_103; obj* x_104; uint32 x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_101 = lean::cnstr_get(x_100, 0);
lean::inc(x_101);
x_102 = lean::cnstr_get(x_100, 1);
lean::inc(x_102);
x_103 = lean::cnstr_get(x_100, 2);
lean::inc(x_103);
lean::dec(x_100);
x_104 = l_String_splitAux___main___closed__1;
x_105 = lean::unbox_uint32(x_101);
lean::dec(x_101);
x_106 = lean::string_push(x_104, x_105);
x_107 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__2(x_106, x_1, x_102, x_98);
x_108 = lean::cnstr_get(x_107, 0);
lean::inc(x_108);
x_109 = lean::cnstr_get(x_107, 1);
lean::inc(x_109);
if (lean::is_exclusive(x_107)) {
 lean::cnstr_release(x_107, 0);
 lean::cnstr_release(x_107, 1);
 x_110 = x_107;
} else {
 lean::dec_ref(x_107);
 x_110 = lean::box(0);
}
x_111 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_103, x_108);
if (lean::is_scalar(x_110)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_110;
}
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_109);
return x_112;
}
else
{
obj* x_113; uint8 x_114; obj* x_115; obj* x_116; obj* x_117; 
x_113 = lean::cnstr_get(x_100, 0);
lean::inc(x_113);
x_114 = lean::cnstr_get_scalar<uint8>(x_100, sizeof(void*)*1);
if (lean::is_exclusive(x_100)) {
 lean::cnstr_release(x_100, 0);
 x_115 = x_100;
} else {
 lean::dec_ref(x_100);
 x_115 = lean::box(0);
}
if (lean::is_scalar(x_115)) {
 x_116 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_116 = x_115;
}
lean::cnstr_set(x_116, 0, x_113);
lean::cnstr_set_scalar(x_116, sizeof(void*)*1, x_114);
x_117 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_117, 0, x_116);
lean::cnstr_set(x_117, 1, x_98);
return x_117;
}
}
}
}
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__5(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_7 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_8 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_8, 0, x_2);
lean::cnstr_set(x_8, 1, x_5);
lean::cnstr_set(x_8, 2, x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_6);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_66; obj* x_67; 
x_10 = lean::cnstr_get(x_3, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_3, 1);
lean::inc(x_11);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_12 = x_3;
} else {
 lean::dec_ref(x_3);
 x_12 = lean::box(0);
}
lean::inc(x_4);
x_66 = lean::apply_3(x_10, x_4, x_5, x_6);
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; 
x_68 = lean::cnstr_get(x_66, 1);
lean::inc(x_68);
lean::dec(x_66);
x_13 = x_67;
x_14 = x_68;
goto block_65;
}
else
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_69; 
x_69 = lean::cnstr_get_scalar<uint8>(x_67, sizeof(void*)*1);
if (x_69 == 0)
{
obj* x_70; uint8 x_71; 
x_70 = lean::cnstr_get(x_66, 1);
lean::inc(x_70);
lean::dec(x_66);
x_71 = !lean::is_exclusive(x_67);
if (x_71 == 0)
{
uint8 x_72; 
x_72 = 0;
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_72);
x_13 = x_67;
x_14 = x_70;
goto block_65;
}
else
{
obj* x_73; uint8 x_74; obj* x_75; 
x_73 = lean::cnstr_get(x_67, 0);
lean::inc(x_73);
lean::dec(x_67);
x_74 = 0;
x_75 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_75, 0, x_73);
lean::cnstr_set_scalar(x_75, sizeof(void*)*1, x_74);
x_13 = x_75;
x_14 = x_70;
goto block_65;
}
}
else
{
obj* x_76; uint8 x_77; 
x_76 = lean::cnstr_get(x_66, 1);
lean::inc(x_76);
lean::dec(x_66);
x_77 = !lean::is_exclusive(x_67);
if (x_77 == 0)
{
uint8 x_78; 
x_78 = 1;
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_78);
x_13 = x_67;
x_14 = x_76;
goto block_65;
}
else
{
obj* x_79; uint8 x_80; obj* x_81; 
x_79 = lean::cnstr_get(x_67, 0);
lean::inc(x_79);
lean::dec(x_67);
x_80 = 1;
x_81 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_81, 0, x_79);
lean::cnstr_set_scalar(x_81, sizeof(void*)*1, x_80);
x_13 = x_81;
x_14 = x_76;
goto block_65;
}
}
}
else
{
obj* x_82; obj* x_83; 
x_82 = lean::cnstr_get(x_67, 0);
lean::inc(x_82);
x_83 = lean::cnstr_get(x_82, 3);
lean::inc(x_83);
if (lean::obj_tag(x_83) == 0)
{
obj* x_84; uint8 x_85; 
lean::dec(x_83);
x_84 = lean::cnstr_get(x_66, 1);
lean::inc(x_84);
lean::dec(x_66);
x_85 = !lean::is_exclusive(x_67);
if (x_85 == 0)
{
uint8 x_86; obj* x_87; uint8 x_88; 
x_86 = lean::cnstr_get_scalar<uint8>(x_67, sizeof(void*)*1);
x_87 = lean::cnstr_get(x_67, 0);
lean::dec(x_87);
x_88 = !lean::is_exclusive(x_82);
if (x_88 == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_89 = lean::cnstr_get(x_82, 3);
lean::dec(x_89);
x_90 = lean::box(3);
lean::inc(x_2);
x_91 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_91, 0, x_90);
lean::cnstr_set(x_91, 1, x_2);
x_92 = l_List_reverse___rarg(x_91);
lean::inc(x_1);
x_93 = l_Lean_Parser_Syntax_mkNode(x_1, x_92);
x_94 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_82, 3, x_94);
if (x_86 == 0)
{
uint8 x_95; 
x_95 = 0;
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_95);
x_13 = x_67;
x_14 = x_84;
goto block_65;
}
else
{
uint8 x_96; 
x_96 = 1;
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_96);
x_13 = x_67;
x_14 = x_84;
goto block_65;
}
}
else
{
obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; 
x_97 = lean::cnstr_get(x_82, 0);
x_98 = lean::cnstr_get(x_82, 1);
x_99 = lean::cnstr_get(x_82, 2);
lean::inc(x_99);
lean::inc(x_98);
lean::inc(x_97);
lean::dec(x_82);
x_100 = lean::box(3);
lean::inc(x_2);
x_101 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_2);
x_102 = l_List_reverse___rarg(x_101);
lean::inc(x_1);
x_103 = l_Lean_Parser_Syntax_mkNode(x_1, x_102);
x_104 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_104, 0, x_103);
x_105 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_105, 0, x_97);
lean::cnstr_set(x_105, 1, x_98);
lean::cnstr_set(x_105, 2, x_99);
lean::cnstr_set(x_105, 3, x_104);
if (x_86 == 0)
{
uint8 x_106; 
x_106 = 0;
lean::cnstr_set(x_67, 0, x_105);
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_106);
x_13 = x_67;
x_14 = x_84;
goto block_65;
}
else
{
uint8 x_107; 
x_107 = 1;
lean::cnstr_set(x_67, 0, x_105);
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_107);
x_13 = x_67;
x_14 = x_84;
goto block_65;
}
}
}
else
{
uint8 x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; 
x_108 = lean::cnstr_get_scalar<uint8>(x_67, sizeof(void*)*1);
lean::dec(x_67);
x_109 = lean::cnstr_get(x_82, 0);
lean::inc(x_109);
x_110 = lean::cnstr_get(x_82, 1);
lean::inc(x_110);
x_111 = lean::cnstr_get(x_82, 2);
lean::inc(x_111);
if (lean::is_exclusive(x_82)) {
 lean::cnstr_release(x_82, 0);
 lean::cnstr_release(x_82, 1);
 lean::cnstr_release(x_82, 2);
 lean::cnstr_release(x_82, 3);
 x_112 = x_82;
} else {
 lean::dec_ref(x_82);
 x_112 = lean::box(0);
}
x_113 = lean::box(3);
lean::inc(x_2);
x_114 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_114, 0, x_113);
lean::cnstr_set(x_114, 1, x_2);
x_115 = l_List_reverse___rarg(x_114);
lean::inc(x_1);
x_116 = l_Lean_Parser_Syntax_mkNode(x_1, x_115);
x_117 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_117, 0, x_116);
if (lean::is_scalar(x_112)) {
 x_118 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_118 = x_112;
}
lean::cnstr_set(x_118, 0, x_109);
lean::cnstr_set(x_118, 1, x_110);
lean::cnstr_set(x_118, 2, x_111);
lean::cnstr_set(x_118, 3, x_117);
if (x_108 == 0)
{
uint8 x_119; obj* x_120; 
x_119 = 0;
x_120 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_120, 0, x_118);
lean::cnstr_set_scalar(x_120, sizeof(void*)*1, x_119);
x_13 = x_120;
x_14 = x_84;
goto block_65;
}
else
{
uint8 x_121; obj* x_122; 
x_121 = 1;
x_122 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_122, 0, x_118);
lean::cnstr_set_scalar(x_122, sizeof(void*)*1, x_121);
x_13 = x_122;
x_14 = x_84;
goto block_65;
}
}
}
else
{
obj* x_123; uint8 x_124; 
x_123 = lean::cnstr_get(x_66, 1);
lean::inc(x_123);
lean::dec(x_66);
x_124 = !lean::is_exclusive(x_67);
if (x_124 == 0)
{
uint8 x_125; obj* x_126; uint8 x_127; 
x_125 = lean::cnstr_get_scalar<uint8>(x_67, sizeof(void*)*1);
x_126 = lean::cnstr_get(x_67, 0);
lean::dec(x_126);
x_127 = !lean::is_exclusive(x_82);
if (x_127 == 0)
{
obj* x_128; uint8 x_129; 
x_128 = lean::cnstr_get(x_82, 3);
lean::dec(x_128);
x_129 = !lean::is_exclusive(x_83);
if (x_129 == 0)
{
obj* x_130; obj* x_131; obj* x_132; obj* x_133; 
x_130 = lean::cnstr_get(x_83, 0);
lean::inc(x_2);
x_131 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_131, 0, x_130);
lean::cnstr_set(x_131, 1, x_2);
x_132 = l_List_reverse___rarg(x_131);
lean::inc(x_1);
x_133 = l_Lean_Parser_Syntax_mkNode(x_1, x_132);
lean::cnstr_set(x_83, 0, x_133);
if (x_125 == 0)
{
uint8 x_134; 
x_134 = 0;
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_134);
x_13 = x_67;
x_14 = x_123;
goto block_65;
}
else
{
uint8 x_135; 
x_135 = 1;
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_135);
x_13 = x_67;
x_14 = x_123;
goto block_65;
}
}
else
{
obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
x_136 = lean::cnstr_get(x_83, 0);
lean::inc(x_136);
lean::dec(x_83);
lean::inc(x_2);
x_137 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_137, 0, x_136);
lean::cnstr_set(x_137, 1, x_2);
x_138 = l_List_reverse___rarg(x_137);
lean::inc(x_1);
x_139 = l_Lean_Parser_Syntax_mkNode(x_1, x_138);
x_140 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_140, 0, x_139);
lean::cnstr_set(x_82, 3, x_140);
if (x_125 == 0)
{
uint8 x_141; 
x_141 = 0;
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_141);
x_13 = x_67;
x_14 = x_123;
goto block_65;
}
else
{
uint8 x_142; 
x_142 = 1;
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_142);
x_13 = x_67;
x_14 = x_123;
goto block_65;
}
}
}
else
{
obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
x_143 = lean::cnstr_get(x_82, 0);
x_144 = lean::cnstr_get(x_82, 1);
x_145 = lean::cnstr_get(x_82, 2);
lean::inc(x_145);
lean::inc(x_144);
lean::inc(x_143);
lean::dec(x_82);
x_146 = lean::cnstr_get(x_83, 0);
lean::inc(x_146);
if (lean::is_exclusive(x_83)) {
 lean::cnstr_release(x_83, 0);
 x_147 = x_83;
} else {
 lean::dec_ref(x_83);
 x_147 = lean::box(0);
}
lean::inc(x_2);
x_148 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_148, 0, x_146);
lean::cnstr_set(x_148, 1, x_2);
x_149 = l_List_reverse___rarg(x_148);
lean::inc(x_1);
x_150 = l_Lean_Parser_Syntax_mkNode(x_1, x_149);
if (lean::is_scalar(x_147)) {
 x_151 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_151 = x_147;
}
lean::cnstr_set(x_151, 0, x_150);
x_152 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_152, 0, x_143);
lean::cnstr_set(x_152, 1, x_144);
lean::cnstr_set(x_152, 2, x_145);
lean::cnstr_set(x_152, 3, x_151);
if (x_125 == 0)
{
uint8 x_153; 
x_153 = 0;
lean::cnstr_set(x_67, 0, x_152);
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_153);
x_13 = x_67;
x_14 = x_123;
goto block_65;
}
else
{
uint8 x_154; 
x_154 = 1;
lean::cnstr_set(x_67, 0, x_152);
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_154);
x_13 = x_67;
x_14 = x_123;
goto block_65;
}
}
}
else
{
uint8 x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; 
x_155 = lean::cnstr_get_scalar<uint8>(x_67, sizeof(void*)*1);
lean::dec(x_67);
x_156 = lean::cnstr_get(x_82, 0);
lean::inc(x_156);
x_157 = lean::cnstr_get(x_82, 1);
lean::inc(x_157);
x_158 = lean::cnstr_get(x_82, 2);
lean::inc(x_158);
if (lean::is_exclusive(x_82)) {
 lean::cnstr_release(x_82, 0);
 lean::cnstr_release(x_82, 1);
 lean::cnstr_release(x_82, 2);
 lean::cnstr_release(x_82, 3);
 x_159 = x_82;
} else {
 lean::dec_ref(x_82);
 x_159 = lean::box(0);
}
x_160 = lean::cnstr_get(x_83, 0);
lean::inc(x_160);
if (lean::is_exclusive(x_83)) {
 lean::cnstr_release(x_83, 0);
 x_161 = x_83;
} else {
 lean::dec_ref(x_83);
 x_161 = lean::box(0);
}
lean::inc(x_2);
x_162 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_162, 0, x_160);
lean::cnstr_set(x_162, 1, x_2);
x_163 = l_List_reverse___rarg(x_162);
lean::inc(x_1);
x_164 = l_Lean_Parser_Syntax_mkNode(x_1, x_163);
if (lean::is_scalar(x_161)) {
 x_165 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_165 = x_161;
}
lean::cnstr_set(x_165, 0, x_164);
if (lean::is_scalar(x_159)) {
 x_166 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_166 = x_159;
}
lean::cnstr_set(x_166, 0, x_156);
lean::cnstr_set(x_166, 1, x_157);
lean::cnstr_set(x_166, 2, x_158);
lean::cnstr_set(x_166, 3, x_165);
if (x_155 == 0)
{
uint8 x_167; obj* x_168; 
x_167 = 0;
x_168 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_168, 0, x_166);
lean::cnstr_set_scalar(x_168, sizeof(void*)*1, x_167);
x_13 = x_168;
x_14 = x_123;
goto block_65;
}
else
{
uint8 x_169; obj* x_170; 
x_169 = 1;
x_170 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_170, 0, x_166);
lean::cnstr_set_scalar(x_170, sizeof(void*)*1, x_169);
x_13 = x_170;
x_14 = x_123;
goto block_65;
}
}
}
}
}
block_65:
{
if (lean::obj_tag(x_13) == 0)
{
uint8 x_15; 
x_15 = !lean::is_exclusive(x_13);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_16 = lean::cnstr_get(x_13, 0);
x_17 = lean::cnstr_get(x_13, 2);
if (lean::is_scalar(x_12)) {
 x_18 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_18 = x_12;
}
lean::cnstr_set(x_18, 0, x_16);
lean::cnstr_set(x_18, 1, x_2);
x_19 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_13, 2, x_19);
lean::cnstr_set(x_13, 0, x_18);
x_20 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_13);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; uint8 x_25; 
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
x_22 = lean::cnstr_get(x_20, 1);
lean::inc(x_22);
x_23 = lean::cnstr_get(x_20, 2);
lean::inc(x_23);
lean::dec(x_20);
x_24 = l_List_mfoldl___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__5(x_1, x_21, x_11, x_4, x_22, x_14);
x_25 = !lean::is_exclusive(x_24);
if (x_25 == 0)
{
obj* x_26; obj* x_27; 
x_26 = lean::cnstr_get(x_24, 0);
x_27 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_23, x_26);
lean::cnstr_set(x_24, 0, x_27);
return x_24;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_28 = lean::cnstr_get(x_24, 0);
x_29 = lean::cnstr_get(x_24, 1);
lean::inc(x_29);
lean::inc(x_28);
lean::dec(x_24);
x_30 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_23, x_28);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_30);
lean::cnstr_set(x_31, 1, x_29);
return x_31;
}
}
else
{
uint8 x_32; 
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_1);
x_32 = !lean::is_exclusive(x_20);
if (x_32 == 0)
{
obj* x_33; 
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_20);
lean::cnstr_set(x_33, 1, x_14);
return x_33;
}
else
{
obj* x_34; uint8 x_35; obj* x_36; obj* x_37; 
x_34 = lean::cnstr_get(x_20, 0);
x_35 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
lean::inc(x_34);
lean::dec(x_20);
x_36 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_35);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_14);
return x_37;
}
}
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_38 = lean::cnstr_get(x_13, 0);
x_39 = lean::cnstr_get(x_13, 1);
x_40 = lean::cnstr_get(x_13, 2);
lean::inc(x_40);
lean::inc(x_39);
lean::inc(x_38);
lean::dec(x_13);
if (lean::is_scalar(x_12)) {
 x_41 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_41 = x_12;
}
lean::cnstr_set(x_41, 0, x_38);
lean::cnstr_set(x_41, 1, x_2);
x_42 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_43 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_39);
lean::cnstr_set(x_43, 2, x_42);
x_44 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_40, x_43);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_45 = lean::cnstr_get(x_44, 0);
lean::inc(x_45);
x_46 = lean::cnstr_get(x_44, 1);
lean::inc(x_46);
x_47 = lean::cnstr_get(x_44, 2);
lean::inc(x_47);
lean::dec(x_44);
x_48 = l_List_mfoldl___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__5(x_1, x_45, x_11, x_4, x_46, x_14);
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_50 = lean::cnstr_get(x_48, 1);
lean::inc(x_50);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 lean::cnstr_release(x_48, 1);
 x_51 = x_48;
} else {
 lean::dec_ref(x_48);
 x_51 = lean::box(0);
}
x_52 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_47, x_49);
if (lean::is_scalar(x_51)) {
 x_53 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_53 = x_51;
}
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_50);
return x_53;
}
else
{
obj* x_54; uint8 x_55; obj* x_56; obj* x_57; obj* x_58; 
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_1);
x_54 = lean::cnstr_get(x_44, 0);
lean::inc(x_54);
x_55 = lean::cnstr_get_scalar<uint8>(x_44, sizeof(void*)*1);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 x_56 = x_44;
} else {
 lean::dec_ref(x_44);
 x_56 = lean::box(0);
}
if (lean::is_scalar(x_56)) {
 x_57 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_57 = x_56;
}
lean::cnstr_set(x_57, 0, x_54);
lean::cnstr_set_scalar(x_57, sizeof(void*)*1, x_55);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_14);
return x_58;
}
}
}
else
{
uint8 x_59; 
lean::dec(x_12);
lean::dec(x_11);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
x_59 = !lean::is_exclusive(x_13);
if (x_59 == 0)
{
obj* x_60; 
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_13);
lean::cnstr_set(x_60, 1, x_14);
return x_60;
}
else
{
obj* x_61; uint8 x_62; obj* x_63; obj* x_64; 
x_61 = lean::cnstr_get(x_13, 0);
x_62 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
lean::inc(x_61);
lean::dec(x_13);
x_63 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_63, 0, x_61);
lean::cnstr_set_scalar(x_63, sizeof(void*)*1, x_62);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_14);
return x_64;
}
}
}
}
}
}
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::box(0);
lean::inc(x_1);
x_7 = l_List_mfoldl___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__5(x_1, x_6, x_2, x_3, x_4, x_5);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_7);
if (x_9 == 0)
{
obj* x_10; uint8 x_11; 
x_10 = lean::cnstr_get(x_7, 0);
lean::dec(x_10);
x_11 = !lean::is_exclusive(x_8);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_12 = lean::cnstr_get(x_8, 0);
x_13 = lean::cnstr_get(x_8, 2);
x_14 = l_List_reverse___rarg(x_12);
x_15 = l_Lean_Parser_Syntax_mkNode(x_1, x_14);
x_16 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_8, 2, x_16);
lean::cnstr_set(x_8, 0, x_15);
x_17 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_8);
lean::cnstr_set(x_7, 0, x_17);
return x_7;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_18 = lean::cnstr_get(x_8, 0);
x_19 = lean::cnstr_get(x_8, 1);
x_20 = lean::cnstr_get(x_8, 2);
lean::inc(x_20);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_8);
x_21 = l_List_reverse___rarg(x_18);
x_22 = l_Lean_Parser_Syntax_mkNode(x_1, x_21);
x_23 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_19);
lean::cnstr_set(x_24, 2, x_23);
x_25 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_20, x_24);
lean::cnstr_set(x_7, 0, x_25);
return x_7;
}
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_26 = lean::cnstr_get(x_7, 1);
lean::inc(x_26);
lean::dec(x_7);
x_27 = lean::cnstr_get(x_8, 0);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_8, 1);
lean::inc(x_28);
x_29 = lean::cnstr_get(x_8, 2);
lean::inc(x_29);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 x_30 = x_8;
} else {
 lean::dec_ref(x_8);
 x_30 = lean::box(0);
}
x_31 = l_List_reverse___rarg(x_27);
x_32 = l_Lean_Parser_Syntax_mkNode(x_1, x_31);
x_33 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_30)) {
 x_34 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_34 = x_30;
}
lean::cnstr_set(x_34, 0, x_32);
lean::cnstr_set(x_34, 1, x_28);
lean::cnstr_set(x_34, 2, x_33);
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_29, x_34);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_26);
return x_36;
}
}
else
{
uint8 x_37; 
lean::dec(x_1);
x_37 = !lean::is_exclusive(x_7);
if (x_37 == 0)
{
obj* x_38; uint8 x_39; 
x_38 = lean::cnstr_get(x_7, 0);
lean::dec(x_38);
x_39 = !lean::is_exclusive(x_8);
if (x_39 == 0)
{
return x_7;
}
else
{
obj* x_40; uint8 x_41; obj* x_42; 
x_40 = lean::cnstr_get(x_8, 0);
x_41 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
lean::inc(x_40);
lean::dec(x_8);
x_42 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_41);
lean::cnstr_set(x_7, 0, x_42);
return x_7;
}
}
else
{
obj* x_43; obj* x_44; uint8 x_45; obj* x_46; obj* x_47; obj* x_48; 
x_43 = lean::cnstr_get(x_7, 1);
lean::inc(x_43);
lean::dec(x_7);
x_44 = lean::cnstr_get(x_8, 0);
lean::inc(x_44);
x_45 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_46 = x_8;
} else {
 lean::dec_ref(x_8);
 x_46 = lean::box(0);
}
if (lean::is_scalar(x_46)) {
 x_47 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_47 = x_46;
}
lean::cnstr_set(x_47, 0, x_44);
lean::cnstr_set_scalar(x_47, sizeof(void*)*1, x_45);
x_48 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_48, 0, x_47);
lean::cnstr_set(x_48, 1, x_43);
return x_48;
}
}
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__7(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_1);
x_8 = l_String_OldIterator_hasNext___main(x_3);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_7);
x_9 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_9;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = l_String_OldIterator_curr___main(x_3);
x_11 = l_Lean_isIdRest(x_10);
if (x_11 == 0)
{
obj* x_12; 
lean::dec(x_7);
x_12 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; 
x_13 = lean::string_push(x_2, x_10);
x_14 = l_String_OldIterator_next___main(x_3);
x_1 = x_7;
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
else
{
obj* x_16; 
lean::dec(x_1);
x_16 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_16;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__6___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = l_String_OldIterator_remaining___main(x_1);
x_4 = l_String_splitAux___main___closed__1;
x_5 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__7(x_3, x_4, x_1);
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_2);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__6(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__6___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__8(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_2);
lean::dec(x_1);
x_6 = lean::box(0);
x_7 = l_Lean_Parser_Combinators_choiceAux___main___rarg___closed__1;
x_8 = l_mjoin___rarg___closed__1;
x_9 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_7, x_8, x_6, x_6, x_3, x_4, x_5);
lean::dec(x_3);
return x_9;
}
else
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_1);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_11 = lean::cnstr_get(x_1, 0);
x_12 = lean::cnstr_get(x_1, 1);
x_13 = lean::mk_nat_obj(1u);
x_14 = lean::nat_add(x_2, x_13);
lean::inc(x_4);
lean::inc(x_3);
x_15 = lean::apply_3(x_11, x_3, x_4, x_5);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
uint8 x_17; 
x_17 = !lean::is_exclusive(x_15);
if (x_17 == 0)
{
obj* x_18; obj* x_19; uint8 x_20; 
x_18 = lean::cnstr_get(x_15, 1);
x_19 = lean::cnstr_get(x_15, 0);
lean::dec(x_19);
x_20 = !lean::is_exclusive(x_16);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_21 = lean::cnstr_get(x_16, 0);
x_22 = lean::cnstr_get(x_16, 2);
x_23 = lean::box(0);
x_24 = lean_name_mk_numeral(x_23, x_2);
x_25 = lean::box(0);
lean::cnstr_set(x_1, 1, x_25);
lean::cnstr_set(x_1, 0, x_21);
x_26 = l_Lean_Parser_Syntax_mkNode(x_24, x_1);
x_27 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_16, 2, x_27);
lean::cnstr_set(x_16, 0, x_26);
x_28 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_16);
if (lean::obj_tag(x_28) == 0)
{
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_4);
lean::dec(x_3);
lean::cnstr_set(x_15, 0, x_28);
return x_15;
}
else
{
uint8 x_29; 
x_29 = lean::cnstr_get_scalar<uint8>(x_28, sizeof(void*)*1);
if (x_29 == 0)
{
obj* x_30; obj* x_31; uint8 x_32; 
lean::free_heap_obj(x_15);
x_30 = lean::cnstr_get(x_28, 0);
lean::inc(x_30);
lean::dec(x_28);
x_31 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__8(x_12, x_14, x_3, x_4, x_18);
x_32 = !lean::is_exclusive(x_31);
if (x_32 == 0)
{
obj* x_33; obj* x_34; 
x_33 = lean::cnstr_get(x_31, 0);
x_34 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_30, x_33);
lean::cnstr_set(x_31, 0, x_34);
return x_31;
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_35 = lean::cnstr_get(x_31, 0);
x_36 = lean::cnstr_get(x_31, 1);
lean::inc(x_36);
lean::inc(x_35);
lean::dec(x_31);
x_37 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_30, x_35);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_36);
return x_38;
}
}
else
{
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_4);
lean::dec(x_3);
lean::cnstr_set(x_15, 0, x_28);
return x_15;
}
}
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; 
x_39 = lean::cnstr_get(x_16, 0);
x_40 = lean::cnstr_get(x_16, 1);
x_41 = lean::cnstr_get(x_16, 2);
lean::inc(x_41);
lean::inc(x_40);
lean::inc(x_39);
lean::dec(x_16);
x_42 = lean::box(0);
x_43 = lean_name_mk_numeral(x_42, x_2);
x_44 = lean::box(0);
lean::cnstr_set(x_1, 1, x_44);
lean::cnstr_set(x_1, 0, x_39);
x_45 = l_Lean_Parser_Syntax_mkNode(x_43, x_1);
x_46 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_47 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_40);
lean::cnstr_set(x_47, 2, x_46);
x_48 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_41, x_47);
if (lean::obj_tag(x_48) == 0)
{
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_4);
lean::dec(x_3);
lean::cnstr_set(x_15, 0, x_48);
return x_15;
}
else
{
uint8 x_49; 
x_49 = lean::cnstr_get_scalar<uint8>(x_48, sizeof(void*)*1);
if (x_49 == 0)
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::free_heap_obj(x_15);
x_50 = lean::cnstr_get(x_48, 0);
lean::inc(x_50);
lean::dec(x_48);
x_51 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__8(x_12, x_14, x_3, x_4, x_18);
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
x_53 = lean::cnstr_get(x_51, 1);
lean::inc(x_53);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_release(x_51, 0);
 lean::cnstr_release(x_51, 1);
 x_54 = x_51;
} else {
 lean::dec_ref(x_51);
 x_54 = lean::box(0);
}
x_55 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_50, x_52);
if (lean::is_scalar(x_54)) {
 x_56 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_56 = x_54;
}
lean::cnstr_set(x_56, 0, x_55);
lean::cnstr_set(x_56, 1, x_53);
return x_56;
}
else
{
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_4);
lean::dec(x_3);
lean::cnstr_set(x_15, 0, x_48);
return x_15;
}
}
}
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_57 = lean::cnstr_get(x_15, 1);
lean::inc(x_57);
lean::dec(x_15);
x_58 = lean::cnstr_get(x_16, 0);
lean::inc(x_58);
x_59 = lean::cnstr_get(x_16, 1);
lean::inc(x_59);
x_60 = lean::cnstr_get(x_16, 2);
lean::inc(x_60);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 lean::cnstr_release(x_16, 1);
 lean::cnstr_release(x_16, 2);
 x_61 = x_16;
} else {
 lean::dec_ref(x_16);
 x_61 = lean::box(0);
}
x_62 = lean::box(0);
x_63 = lean_name_mk_numeral(x_62, x_2);
x_64 = lean::box(0);
lean::cnstr_set(x_1, 1, x_64);
lean::cnstr_set(x_1, 0, x_58);
x_65 = l_Lean_Parser_Syntax_mkNode(x_63, x_1);
x_66 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_61)) {
 x_67 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_67 = x_61;
}
lean::cnstr_set(x_67, 0, x_65);
lean::cnstr_set(x_67, 1, x_59);
lean::cnstr_set(x_67, 2, x_66);
x_68 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_60, x_67);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_4);
lean::dec(x_3);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_57);
return x_69;
}
else
{
uint8 x_70; 
x_70 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
if (x_70 == 0)
{
obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_71 = lean::cnstr_get(x_68, 0);
lean::inc(x_71);
lean::dec(x_68);
x_72 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__8(x_12, x_14, x_3, x_4, x_57);
x_73 = lean::cnstr_get(x_72, 0);
lean::inc(x_73);
x_74 = lean::cnstr_get(x_72, 1);
lean::inc(x_74);
if (lean::is_exclusive(x_72)) {
 lean::cnstr_release(x_72, 0);
 lean::cnstr_release(x_72, 1);
 x_75 = x_72;
} else {
 lean::dec_ref(x_72);
 x_75 = lean::box(0);
}
x_76 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_71, x_73);
if (lean::is_scalar(x_75)) {
 x_77 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_77 = x_75;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_74);
return x_77;
}
else
{
obj* x_78; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_4);
lean::dec(x_3);
x_78 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_78, 0, x_68);
lean::cnstr_set(x_78, 1, x_57);
return x_78;
}
}
}
}
else
{
uint8 x_79; 
lean::free_heap_obj(x_1);
lean::dec(x_2);
x_79 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
if (x_79 == 0)
{
obj* x_80; obj* x_81; obj* x_82; uint8 x_83; 
x_80 = lean::cnstr_get(x_15, 1);
lean::inc(x_80);
lean::dec(x_15);
x_81 = lean::cnstr_get(x_16, 0);
lean::inc(x_81);
lean::dec(x_16);
x_82 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__8(x_12, x_14, x_3, x_4, x_80);
x_83 = !lean::is_exclusive(x_82);
if (x_83 == 0)
{
obj* x_84; obj* x_85; 
x_84 = lean::cnstr_get(x_82, 0);
x_85 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_81, x_84);
lean::cnstr_set(x_82, 0, x_85);
return x_82;
}
else
{
obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_86 = lean::cnstr_get(x_82, 0);
x_87 = lean::cnstr_get(x_82, 1);
lean::inc(x_87);
lean::inc(x_86);
lean::dec(x_82);
x_88 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_81, x_86);
x_89 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_87);
return x_89;
}
}
else
{
uint8 x_90; 
lean::dec(x_14);
lean::dec(x_12);
lean::dec(x_4);
lean::dec(x_3);
x_90 = !lean::is_exclusive(x_15);
if (x_90 == 0)
{
obj* x_91; uint8 x_92; 
x_91 = lean::cnstr_get(x_15, 0);
lean::dec(x_91);
x_92 = !lean::is_exclusive(x_16);
if (x_92 == 0)
{
return x_15;
}
else
{
obj* x_93; obj* x_94; 
x_93 = lean::cnstr_get(x_16, 0);
lean::inc(x_93);
lean::dec(x_16);
x_94 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_79);
lean::cnstr_set(x_15, 0, x_94);
return x_15;
}
}
else
{
obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
x_95 = lean::cnstr_get(x_15, 1);
lean::inc(x_95);
lean::dec(x_15);
x_96 = lean::cnstr_get(x_16, 0);
lean::inc(x_96);
if (lean::is_exclusive(x_16)) {
 lean::cnstr_release(x_16, 0);
 x_97 = x_16;
} else {
 lean::dec_ref(x_16);
 x_97 = lean::box(0);
}
if (lean::is_scalar(x_97)) {
 x_98 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_98 = x_97;
}
lean::cnstr_set(x_98, 0, x_96);
lean::cnstr_set_scalar(x_98, sizeof(void*)*1, x_79);
x_99 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_99, 0, x_98);
lean::cnstr_set(x_99, 1, x_95);
return x_99;
}
}
}
}
else
{
obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; 
x_100 = lean::cnstr_get(x_1, 0);
x_101 = lean::cnstr_get(x_1, 1);
lean::inc(x_101);
lean::inc(x_100);
lean::dec(x_1);
x_102 = lean::mk_nat_obj(1u);
x_103 = lean::nat_add(x_2, x_102);
lean::inc(x_4);
lean::inc(x_3);
x_104 = lean::apply_3(x_100, x_3, x_4, x_5);
x_105 = lean::cnstr_get(x_104, 0);
lean::inc(x_105);
if (lean::obj_tag(x_105) == 0)
{
obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
x_106 = lean::cnstr_get(x_104, 1);
lean::inc(x_106);
if (lean::is_exclusive(x_104)) {
 lean::cnstr_release(x_104, 0);
 lean::cnstr_release(x_104, 1);
 x_107 = x_104;
} else {
 lean::dec_ref(x_104);
 x_107 = lean::box(0);
}
x_108 = lean::cnstr_get(x_105, 0);
lean::inc(x_108);
x_109 = lean::cnstr_get(x_105, 1);
lean::inc(x_109);
x_110 = lean::cnstr_get(x_105, 2);
lean::inc(x_110);
if (lean::is_exclusive(x_105)) {
 lean::cnstr_release(x_105, 0);
 lean::cnstr_release(x_105, 1);
 lean::cnstr_release(x_105, 2);
 x_111 = x_105;
} else {
 lean::dec_ref(x_105);
 x_111 = lean::box(0);
}
x_112 = lean::box(0);
x_113 = lean_name_mk_numeral(x_112, x_2);
x_114 = lean::box(0);
x_115 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_115, 0, x_108);
lean::cnstr_set(x_115, 1, x_114);
x_116 = l_Lean_Parser_Syntax_mkNode(x_113, x_115);
x_117 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_111)) {
 x_118 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_118 = x_111;
}
lean::cnstr_set(x_118, 0, x_116);
lean::cnstr_set(x_118, 1, x_109);
lean::cnstr_set(x_118, 2, x_117);
x_119 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_110, x_118);
if (lean::obj_tag(x_119) == 0)
{
obj* x_120; 
lean::dec(x_103);
lean::dec(x_101);
lean::dec(x_4);
lean::dec(x_3);
if (lean::is_scalar(x_107)) {
 x_120 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_120 = x_107;
}
lean::cnstr_set(x_120, 0, x_119);
lean::cnstr_set(x_120, 1, x_106);
return x_120;
}
else
{
uint8 x_121; 
x_121 = lean::cnstr_get_scalar<uint8>(x_119, sizeof(void*)*1);
if (x_121 == 0)
{
obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; 
lean::dec(x_107);
x_122 = lean::cnstr_get(x_119, 0);
lean::inc(x_122);
lean::dec(x_119);
x_123 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__8(x_101, x_103, x_3, x_4, x_106);
x_124 = lean::cnstr_get(x_123, 0);
lean::inc(x_124);
x_125 = lean::cnstr_get(x_123, 1);
lean::inc(x_125);
if (lean::is_exclusive(x_123)) {
 lean::cnstr_release(x_123, 0);
 lean::cnstr_release(x_123, 1);
 x_126 = x_123;
} else {
 lean::dec_ref(x_123);
 x_126 = lean::box(0);
}
x_127 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_122, x_124);
if (lean::is_scalar(x_126)) {
 x_128 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_128 = x_126;
}
lean::cnstr_set(x_128, 0, x_127);
lean::cnstr_set(x_128, 1, x_125);
return x_128;
}
else
{
obj* x_129; 
lean::dec(x_103);
lean::dec(x_101);
lean::dec(x_4);
lean::dec(x_3);
if (lean::is_scalar(x_107)) {
 x_129 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_129 = x_107;
}
lean::cnstr_set(x_129, 0, x_119);
lean::cnstr_set(x_129, 1, x_106);
return x_129;
}
}
}
else
{
uint8 x_130; 
lean::dec(x_2);
x_130 = lean::cnstr_get_scalar<uint8>(x_105, sizeof(void*)*1);
if (x_130 == 0)
{
obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; 
x_131 = lean::cnstr_get(x_104, 1);
lean::inc(x_131);
lean::dec(x_104);
x_132 = lean::cnstr_get(x_105, 0);
lean::inc(x_132);
lean::dec(x_105);
x_133 = l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__8(x_101, x_103, x_3, x_4, x_131);
x_134 = lean::cnstr_get(x_133, 0);
lean::inc(x_134);
x_135 = lean::cnstr_get(x_133, 1);
lean::inc(x_135);
if (lean::is_exclusive(x_133)) {
 lean::cnstr_release(x_133, 0);
 lean::cnstr_release(x_133, 1);
 x_136 = x_133;
} else {
 lean::dec_ref(x_133);
 x_136 = lean::box(0);
}
x_137 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_132, x_134);
if (lean::is_scalar(x_136)) {
 x_138 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_138 = x_136;
}
lean::cnstr_set(x_138, 0, x_137);
lean::cnstr_set(x_138, 1, x_135);
return x_138;
}
else
{
obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; 
lean::dec(x_103);
lean::dec(x_101);
lean::dec(x_4);
lean::dec(x_3);
x_139 = lean::cnstr_get(x_104, 1);
lean::inc(x_139);
if (lean::is_exclusive(x_104)) {
 lean::cnstr_release(x_104, 0);
 lean::cnstr_release(x_104, 1);
 x_140 = x_104;
} else {
 lean::dec_ref(x_104);
 x_140 = lean::box(0);
}
x_141 = lean::cnstr_get(x_105, 0);
lean::inc(x_141);
if (lean::is_exclusive(x_105)) {
 lean::cnstr_release(x_105, 0);
 x_142 = x_105;
} else {
 lean::dec_ref(x_105);
 x_142 = lean::box(0);
}
if (lean::is_scalar(x_142)) {
 x_143 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_143 = x_142;
}
lean::cnstr_set(x_143, 0, x_141);
lean::cnstr_set_scalar(x_143, sizeof(void*)*1, x_130);
if (lean::is_scalar(x_140)) {
 x_144 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_144 = x_140;
}
lean::cnstr_set(x_144, 0, x_143);
lean::cnstr_set(x_144, 1, x_139);
return x_144;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_1);
x_3 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_2);
x_4 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_tokens___rarg(x_4);
lean::dec(x_4);
x_6 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_2);
lean::dec(x_2);
lean::dec(x_5);
x_7 = l_Lean_Parser_tokens___rarg(x_6);
lean::dec(x_6);
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_7, x_1);
lean::dec(x_7);
x_9 = l_Lean_Parser_tokens___rarg(x_8);
lean::dec(x_8);
return x_9;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__2(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__6___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__6(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
x_7 = l_Lean_Parser_MonadParsec_strCore___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__3(x_1, x_2, x_4, x_5, x_6);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_7);
if (x_9 == 0)
{
obj* x_10; uint8 x_11; 
x_10 = lean::cnstr_get(x_7, 0);
lean::dec(x_10);
x_11 = !lean::is_exclusive(x_8);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_12 = lean::cnstr_get(x_8, 1);
x_13 = lean::cnstr_get(x_8, 2);
x_14 = lean::cnstr_get(x_8, 0);
lean::dec(x_14);
lean::inc(x_12);
x_15 = l_Lean_Parser_mkRawRes(x_3, x_12);
x_16 = l_Lean_Parser_finishCommentBlock___closed__2;
lean::cnstr_set(x_8, 2, x_16);
lean::cnstr_set(x_8, 0, x_15);
x_17 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_8);
lean::cnstr_set(x_7, 0, x_17);
return x_7;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_18 = lean::cnstr_get(x_8, 1);
x_19 = lean::cnstr_get(x_8, 2);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_8);
lean::inc(x_18);
x_20 = l_Lean_Parser_mkRawRes(x_3, x_18);
x_21 = l_Lean_Parser_finishCommentBlock___closed__2;
x_22 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_22, 0, x_20);
lean::cnstr_set(x_22, 1, x_18);
lean::cnstr_set(x_22, 2, x_21);
x_23 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_19, x_22);
lean::cnstr_set(x_7, 0, x_23);
return x_7;
}
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_24 = lean::cnstr_get(x_7, 1);
lean::inc(x_24);
lean::dec(x_7);
x_25 = lean::cnstr_get(x_8, 1);
lean::inc(x_25);
x_26 = lean::cnstr_get(x_8, 2);
lean::inc(x_26);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 x_27 = x_8;
} else {
 lean::dec_ref(x_8);
 x_27 = lean::box(0);
}
lean::inc(x_25);
x_28 = l_Lean_Parser_mkRawRes(x_3, x_25);
x_29 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_27)) {
 x_30 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_30 = x_27;
}
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_25);
lean::cnstr_set(x_30, 2, x_29);
x_31 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_26, x_30);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_24);
return x_32;
}
}
else
{
uint8 x_33; 
lean::dec(x_3);
x_33 = !lean::is_exclusive(x_7);
if (x_33 == 0)
{
obj* x_34; uint8 x_35; 
x_34 = lean::cnstr_get(x_7, 0);
lean::dec(x_34);
x_35 = !lean::is_exclusive(x_8);
if (x_35 == 0)
{
return x_7;
}
else
{
obj* x_36; uint8 x_37; obj* x_38; 
x_36 = lean::cnstr_get(x_8, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
lean::inc(x_36);
lean::dec(x_8);
x_38 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set_scalar(x_38, sizeof(void*)*1, x_37);
lean::cnstr_set(x_7, 0, x_38);
return x_7;
}
}
else
{
obj* x_39; obj* x_40; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; 
x_39 = lean::cnstr_get(x_7, 1);
lean::inc(x_39);
lean::dec(x_7);
x_40 = lean::cnstr_get(x_8, 0);
lean::inc(x_40);
x_41 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_42 = x_8;
} else {
 lean::dec_ref(x_8);
 x_42 = lean::box(0);
}
if (lean::is_scalar(x_42)) {
 x_43 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_43 = x_42;
}
lean::cnstr_set(x_43, 0, x_40);
lean::cnstr_set_scalar(x_43, sizeof(void*)*1, x_41);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_39);
return x_44;
}
}
}
}
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__1(x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_5);
if (x_7 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::cnstr_get(x_5, 0);
lean::dec(x_8);
x_9 = !lean::is_exclusive(x_6);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_6, 1);
x_11 = lean::cnstr_get(x_6, 2);
x_12 = lean::cnstr_get(x_6, 0);
lean::dec(x_12);
lean::inc(x_10);
x_13 = l_Lean_Parser_mkRawRes(x_1, x_10);
x_14 = l_Lean_Parser_finishCommentBlock___closed__2;
lean::cnstr_set(x_6, 2, x_14);
lean::cnstr_set(x_6, 0, x_13);
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_6);
lean::cnstr_set(x_5, 0, x_15);
return x_5;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_16 = lean::cnstr_get(x_6, 1);
x_17 = lean::cnstr_get(x_6, 2);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_6);
lean::inc(x_16);
x_18 = l_Lean_Parser_mkRawRes(x_1, x_16);
x_19 = l_Lean_Parser_finishCommentBlock___closed__2;
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_16);
lean::cnstr_set(x_20, 2, x_19);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_20);
lean::cnstr_set(x_5, 0, x_21);
return x_5;
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_5, 1);
lean::inc(x_22);
lean::dec(x_5);
x_23 = lean::cnstr_get(x_6, 1);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_6, 2);
lean::inc(x_24);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_25 = x_6;
} else {
 lean::dec_ref(x_6);
 x_25 = lean::box(0);
}
lean::inc(x_23);
x_26 = l_Lean_Parser_mkRawRes(x_1, x_23);
x_27 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_25)) {
 x_28 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_28 = x_25;
}
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_23);
lean::cnstr_set(x_28, 2, x_27);
x_29 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_22);
return x_30;
}
}
else
{
uint8 x_31; 
lean::dec(x_1);
x_31 = !lean::is_exclusive(x_5);
if (x_31 == 0)
{
obj* x_32; uint8 x_33; 
x_32 = lean::cnstr_get(x_5, 0);
lean::dec(x_32);
x_33 = !lean::is_exclusive(x_6);
if (x_33 == 0)
{
return x_5;
}
else
{
obj* x_34; uint8 x_35; obj* x_36; 
x_34 = lean::cnstr_get(x_6, 0);
x_35 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
lean::inc(x_34);
lean::dec(x_6);
x_36 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_35);
lean::cnstr_set(x_5, 0, x_36);
return x_5;
}
}
else
{
obj* x_37; obj* x_38; uint8 x_39; obj* x_40; obj* x_41; obj* x_42; 
x_37 = lean::cnstr_get(x_5, 1);
lean::inc(x_37);
lean::dec(x_5);
x_38 = lean::cnstr_get(x_6, 0);
lean::inc(x_38);
x_39 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_40 = x_6;
} else {
 lean::dec_ref(x_6);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_38);
lean::cnstr_set_scalar(x_41, sizeof(void*)*1, x_39);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_37);
return x_42;
}
}
}
}
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; uint8 x_29; 
x_29 = l_String_OldIterator_hasNext___main(x_3);
if (x_29 == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_30 = lean::box(0);
x_31 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_32 = l_mjoin___rarg___closed__1;
x_33 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_31, x_32, x_30, x_30, x_2, x_3, x_4);
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
x_35 = lean::cnstr_get(x_33, 1);
lean::inc(x_35);
lean::dec(x_33);
x_36 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_37 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_36, x_34);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_38 = lean::cnstr_get(x_37, 1);
lean::inc(x_38);
x_39 = lean::cnstr_get(x_37, 2);
lean::inc(x_39);
lean::dec(x_37);
x_40 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__6___rarg(x_38, x_35);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_42 = lean::cnstr_get(x_40, 1);
lean::inc(x_42);
lean::dec(x_40);
x_43 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_39, x_41);
x_5 = x_43;
x_6 = x_42;
goto block_28;
}
else
{
uint8 x_44; 
x_44 = !lean::is_exclusive(x_37);
if (x_44 == 0)
{
x_5 = x_37;
x_6 = x_35;
goto block_28;
}
else
{
obj* x_45; uint8 x_46; obj* x_47; 
x_45 = lean::cnstr_get(x_37, 0);
x_46 = lean::cnstr_get_scalar<uint8>(x_37, sizeof(void*)*1);
lean::inc(x_45);
lean::dec(x_37);
x_47 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set_scalar(x_47, sizeof(void*)*1, x_46);
x_5 = x_47;
x_6 = x_35;
goto block_28;
}
}
}
else
{
uint32 x_48; uint8 x_49; 
x_48 = l_String_OldIterator_curr___main(x_3);
x_49 = l_Lean_isIdFirst(x_48);
if (x_49 == 0)
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_50 = l_Char_quoteCore(x_48);
x_51 = l_Char_HasRepr___closed__1;
x_52 = lean::string_append(x_51, x_50);
lean::dec(x_50);
x_53 = lean::string_append(x_52, x_51);
x_54 = lean::box(0);
x_55 = l_mjoin___rarg___closed__1;
x_56 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_53, x_55, x_54, x_54, x_2, x_3, x_4);
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_58 = lean::cnstr_get(x_56, 1);
lean::inc(x_58);
lean::dec(x_56);
x_59 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_60 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_59, x_57);
if (lean::obj_tag(x_60) == 0)
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_61 = lean::cnstr_get(x_60, 1);
lean::inc(x_61);
x_62 = lean::cnstr_get(x_60, 2);
lean::inc(x_62);
lean::dec(x_60);
x_63 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__6___rarg(x_61, x_58);
x_64 = lean::cnstr_get(x_63, 0);
lean::inc(x_64);
x_65 = lean::cnstr_get(x_63, 1);
lean::inc(x_65);
lean::dec(x_63);
x_66 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_62, x_64);
x_5 = x_66;
x_6 = x_65;
goto block_28;
}
else
{
uint8 x_67; 
x_67 = !lean::is_exclusive(x_60);
if (x_67 == 0)
{
x_5 = x_60;
x_6 = x_58;
goto block_28;
}
else
{
obj* x_68; uint8 x_69; obj* x_70; 
x_68 = lean::cnstr_get(x_60, 0);
x_69 = lean::cnstr_get_scalar<uint8>(x_60, sizeof(void*)*1);
lean::inc(x_68);
lean::dec(x_60);
x_70 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_70, 0, x_68);
lean::cnstr_set_scalar(x_70, sizeof(void*)*1, x_69);
x_5 = x_70;
x_6 = x_58;
goto block_28;
}
}
}
else
{
obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_71 = l_String_OldIterator_next___main(x_3);
x_72 = lean::box(0);
x_73 = l_Lean_Parser_MonadParsec_takeWhile___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__6___rarg(x_71, x_4);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_75 = lean::cnstr_get(x_73, 1);
lean::inc(x_75);
lean::dec(x_73);
x_76 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_72, x_74);
x_5 = x_76;
x_6 = x_75;
goto block_28;
}
}
block_28:
{
if (lean::obj_tag(x_5) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_5);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_8 = lean::cnstr_get(x_5, 1);
x_9 = lean::cnstr_get(x_5, 2);
x_10 = lean::cnstr_get(x_5, 0);
lean::dec(x_10);
lean::inc(x_8);
x_11 = l_Lean_Parser_mkRawRes(x_1, x_8);
x_12 = l_Lean_Parser_finishCommentBlock___closed__2;
lean::cnstr_set(x_5, 2, x_12);
lean::cnstr_set(x_5, 0, x_11);
x_13 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_5);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_6);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_15 = lean::cnstr_get(x_5, 1);
x_16 = lean::cnstr_get(x_5, 2);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_5);
lean::inc(x_15);
x_17 = l_Lean_Parser_mkRawRes(x_1, x_15);
x_18 = l_Lean_Parser_finishCommentBlock___closed__2;
x_19 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_15);
lean::cnstr_set(x_19, 2, x_18);
x_20 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_6);
return x_21;
}
}
else
{
uint8 x_22; 
lean::dec(x_1);
x_22 = !lean::is_exclusive(x_5);
if (x_22 == 0)
{
obj* x_23; 
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_5);
lean::cnstr_set(x_23, 1, x_6);
return x_23;
}
else
{
obj* x_24; uint8 x_25; obj* x_26; obj* x_27; 
x_24 = lean::cnstr_get(x_5, 0);
x_25 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
lean::inc(x_24);
lean::dec(x_5);
x_26 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set_scalar(x_26, sizeof(void*)*1, x_25);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_6);
return x_27;
}
}
}
}
}
obj* _init_l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; uint32 x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint32 x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_1 = lean::mk_string("");
x_2 = l_Lean_idBeginEscape;
lean::inc(x_1);
x_3 = lean::string_push(x_1, x_2);
lean::inc(x_3);
x_4 = l_String_quote(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__1___boxed), 6, 2);
lean::closure_set(x_8, 0, x_3);
lean::closure_set(x_8, 1, x_5);
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_9, 0, x_7);
lean::closure_set(x_9, 1, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__2___boxed), 4, 0);
lean::inc(x_7);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_11, 0, x_7);
lean::closure_set(x_11, 1, x_10);
x_12 = l_Lean_idEndEscape;
x_13 = lean::string_push(x_1, x_12);
lean::inc(x_13);
x_14 = l_String_quote(x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_15, 0, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__1___boxed), 6, 2);
lean::closure_set(x_16, 0, x_13);
lean::closure_set(x_16, 1, x_15);
lean::inc(x_7);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_17, 0, x_7);
lean::closure_set(x_17, 1, x_16);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_11);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_9);
lean::cnstr_set(x_21, 1, x_20);
x_22 = l_Lean_Parser_detailIdentPartEscaped;
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4), 5, 2);
lean::closure_set(x_23, 0, x_22);
lean::closure_set(x_23, 1, x_21);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__3___boxed), 4, 0);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_25, 0, x_7);
lean::closure_set(x_25, 1, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_18);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::mk_nat_obj(0u);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__8), 5, 2);
lean::closure_set(x_29, 0, x_27);
lean::closure_set(x_29, 1, x_28);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_18);
x_31 = l_Lean_Parser_BasicParserM_Monad;
x_32 = l_Lean_Parser_BasicParserM_MonadExcept;
x_33 = l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
x_34 = l_Lean_Parser_BasicParserM_Alternative;
x_35 = l_Lean_Parser_detailIdentPart;
x_36 = l_Lean_Parser_detailIdentPart_HasView;
x_37 = l_Lean_Parser_Combinators_node_view___rarg(x_31, x_32, x_33, x_34, x_35, x_30, x_36);
lean::dec(x_30);
return x_37;
}
}
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
return x_7;
}
}
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__2(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__3(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_Lean_Parser_detailIdentPart_Parser___closed__1() {
_start:
{
obj* x_1; uint32 x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint32 x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_1 = lean::mk_string("");
x_2 = l_Lean_idBeginEscape;
lean::inc(x_1);
x_3 = lean::string_push(x_1, x_2);
lean::inc(x_3);
x_4 = l_String_quote(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__1___boxed), 6, 2);
lean::closure_set(x_8, 0, x_3);
lean::closure_set(x_8, 1, x_5);
lean::inc(x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_9, 0, x_7);
lean::closure_set(x_9, 1, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__2___boxed), 4, 0);
lean::inc(x_7);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_11, 0, x_7);
lean::closure_set(x_11, 1, x_10);
x_12 = l_Lean_idEndEscape;
x_13 = lean::string_push(x_1, x_12);
lean::inc(x_13);
x_14 = l_String_quote(x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_15, 0, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__1___boxed), 6, 2);
lean::closure_set(x_16, 0, x_13);
lean::closure_set(x_16, 1, x_15);
lean::inc(x_7);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_17, 0, x_7);
lean::closure_set(x_17, 1, x_16);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_18);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_11);
lean::cnstr_set(x_20, 1, x_19);
x_21 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_21, 0, x_9);
lean::cnstr_set(x_21, 1, x_20);
x_22 = l_Lean_Parser_detailIdentPartEscaped;
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4), 5, 2);
lean::closure_set(x_23, 0, x_22);
lean::closure_set(x_23, 1, x_21);
x_24 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasView___lambda__3___boxed), 4, 0);
x_25 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_25, 0, x_7);
lean::closure_set(x_25, 1, x_24);
x_26 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_18);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_23);
lean::cnstr_set(x_27, 1, x_26);
x_28 = lean::mk_nat_obj(0u);
x_29 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_choiceAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__8), 5, 2);
lean::closure_set(x_29, 0, x_27);
lean::closure_set(x_29, 1, x_28);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_18);
return x_30;
}
}
obj* l_Lean_Parser_detailIdentPart_Parser(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_detailIdentPart;
x_5 = l_Lean_Parser_detailIdentPart_Parser___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4(x_4, x_5, x_1, x_2, x_3);
return x_6;
}
}
obj* _init_l_Lean_Parser_detailIdentSuffix() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("detailIdentSuffix");
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
obj* l_Lean_Parser_detailIdentSuffix_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_2 = lean::cnstr_get(x_1, 0);
x_3 = lean::cnstr_get(x_1, 1);
x_4 = lean::box(0);
lean::inc(x_3);
x_5 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_4);
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::box(3);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_5);
x_8 = l_Lean_Parser_detailIdentSuffix;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
return x_9;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
x_11 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_11, 0, x_10);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_5);
x_13 = l_Lean_Parser_detailIdentSuffix;
x_14 = l_Lean_Parser_Syntax_mkNode(x_13, x_12);
return x_14;
}
}
}
obj* _init_l_Lean_Parser_detailIdentSuffix_HasView_x27___elambda__2___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_detailIdentSuffix_HasView_x27___elambda__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_2);
x_3 = l_Lean_Parser_detailIdentSuffix_HasView_x27___elambda__2___closed__1;
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; 
lean::dec(x_6);
lean::free_heap_obj(x_2);
x_7 = l_Lean_Parser_detailIdentSuffix_HasView_x27___elambda__2___closed__1;
return x_7;
}
else
{
obj* x_8; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_6, 1);
lean::inc(x_9);
lean::dec(x_6);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
lean::cnstr_set(x_2, 0, x_10);
if (lean::obj_tag(x_9) == 0)
{
obj* x_11; obj* x_12; 
lean::dec(x_9);
x_11 = lean::box(3);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_2);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
else
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_9, 0);
lean::inc(x_13);
lean::dec(x_9);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_2);
lean::cnstr_set(x_14, 1, x_13);
return x_14;
}
}
else
{
obj* x_15; 
lean::dec(x_8);
lean::free_heap_obj(x_2);
x_15 = lean::cnstr_get(x_6, 1);
lean::inc(x_15);
lean::dec(x_6);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; 
lean::dec(x_15);
x_16 = l_Lean_Parser_detailIdentSuffix_HasView_x27___elambda__2___closed__1;
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; 
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
lean::dec(x_15);
x_18 = lean::box(0);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_17);
return x_19;
}
}
}
}
else
{
obj* x_20; obj* x_21; 
x_20 = lean::cnstr_get(x_2, 0);
lean::inc(x_20);
lean::dec(x_2);
x_21 = lean::cnstr_get(x_20, 1);
lean::inc(x_21);
lean::dec(x_20);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; 
lean::dec(x_21);
x_22 = l_Lean_Parser_detailIdentSuffix_HasView_x27___elambda__2___closed__1;
return x_22;
}
else
{
obj* x_23; 
x_23 = lean::cnstr_get(x_21, 0);
lean::inc(x_23);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; obj* x_25; obj* x_26; 
x_24 = lean::cnstr_get(x_21, 1);
lean::inc(x_24);
lean::dec(x_21);
x_25 = lean::cnstr_get(x_23, 0);
lean::inc(x_25);
lean::dec(x_23);
x_26 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
if (lean::obj_tag(x_24) == 0)
{
obj* x_27; obj* x_28; 
lean::dec(x_24);
x_27 = lean::box(3);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_27);
return x_28;
}
else
{
obj* x_29; obj* x_30; 
x_29 = lean::cnstr_get(x_24, 0);
lean::inc(x_29);
lean::dec(x_24);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_26);
lean::cnstr_set(x_30, 1, x_29);
return x_30;
}
}
else
{
obj* x_31; 
lean::dec(x_23);
x_31 = lean::cnstr_get(x_21, 1);
lean::inc(x_31);
lean::dec(x_21);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; 
lean::dec(x_31);
x_32 = l_Lean_Parser_detailIdentSuffix_HasView_x27___elambda__2___closed__1;
return x_32;
}
else
{
obj* x_33; obj* x_34; obj* x_35; 
x_33 = lean::cnstr_get(x_31, 0);
lean::inc(x_33);
lean::dec(x_31);
x_34 = lean::box(0);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_33);
return x_35;
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_detailIdentSuffix_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentSuffix_HasView_x27___elambda__2), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentSuffix_HasView_x27___elambda__1___boxed), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_detailIdentSuffix_HasView_x27___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_detailIdentSuffix_HasView_x27___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_detailIdentSuffix_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_detailIdentSuffix_HasView_x27;
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_9; uint8 x_10; obj* x_11; obj* x_12; 
x_9 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_9, 0, x_7);
lean::cnstr_set(x_9, 1, x_1);
lean::cnstr_set(x_9, 2, x_2);
lean::cnstr_set(x_9, 3, x_4);
x_10 = 0;
x_11 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set_scalar(x_11, sizeof(void*)*1, x_10);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_8);
return x_12;
}
else
{
obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; 
lean::dec(x_7);
x_13 = lean::cnstr_get(x_3, 0);
lean::inc(x_13);
x_14 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_1);
lean::cnstr_set(x_14, 2, x_2);
lean::cnstr_set(x_14, 3, x_4);
x_15 = 0;
x_16 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set_scalar(x_16, sizeof(void*)*1, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_8);
return x_17;
}
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg___boxed), 8, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1(uint32 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint8 x_6; 
x_6 = l_String_OldIterator_hasNext___main(x_4);
if (x_6 == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint8 x_11; 
x_7 = lean::box(0);
x_8 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_9 = l_mjoin___rarg___closed__1;
x_10 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_8, x_9, x_7, x_7, x_2, x_3, x_4, x_5);
x_11 = !lean::is_exclusive(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::cnstr_get(x_10, 0);
x_13 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_14 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_12);
lean::cnstr_set(x_10, 0, x_14);
return x_10;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_15 = lean::cnstr_get(x_10, 0);
x_16 = lean::cnstr_get(x_10, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_10);
x_17 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_18 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_15);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_16);
return x_19;
}
}
else
{
uint32 x_20; uint8 x_21; 
x_20 = l_String_OldIterator_curr___main(x_4);
x_21 = x_20 == x_1;
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; uint8 x_29; 
x_22 = l_Char_quoteCore(x_20);
x_23 = l_Char_HasRepr___closed__1;
x_24 = lean::string_append(x_23, x_22);
lean::dec(x_22);
x_25 = lean::string_append(x_24, x_23);
x_26 = lean::box(0);
x_27 = l_mjoin___rarg___closed__1;
x_28 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_25, x_27, x_26, x_26, x_2, x_3, x_4, x_5);
x_29 = !lean::is_exclusive(x_28);
if (x_29 == 0)
{
obj* x_30; obj* x_31; obj* x_32; 
x_30 = lean::cnstr_get(x_28, 0);
x_31 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_31, x_30);
lean::cnstr_set(x_28, 0, x_32);
return x_28;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_33 = lean::cnstr_get(x_28, 0);
x_34 = lean::cnstr_get(x_28, 1);
lean::inc(x_34);
lean::inc(x_33);
lean::dec(x_28);
x_35 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_36 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_35, x_33);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_34);
return x_37;
}
}
else
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_38 = l_String_OldIterator_next___main(x_4);
x_39 = lean::box(0);
x_40 = lean::box_uint32(x_20);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_38);
lean::cnstr_set(x_41, 2, x_39);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_5);
return x_42;
}
}
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__3(uint32 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_19; obj* x_20; 
lean::inc(x_4);
x_19 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1(x_1, x_2, x_3, x_4, x_5);
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; uint8 x_22; 
x_21 = lean::cnstr_get(x_19, 1);
lean::inc(x_21);
lean::dec(x_19);
x_22 = !lean::is_exclusive(x_20);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; uint32 x_26; obj* x_27; obj* x_28; 
x_23 = lean::cnstr_get(x_20, 1);
x_24 = lean::cnstr_get(x_20, 2);
x_25 = lean::cnstr_get(x_20, 0);
lean::dec(x_25);
x_26 = l_Lean_idBeginEscape;
lean::inc(x_23);
x_27 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1(x_26, x_2, x_3, x_23, x_21);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_30; 
lean::free_heap_obj(x_20);
lean::dec(x_23);
x_29 = lean::cnstr_get(x_27, 1);
lean::inc(x_29);
lean::dec(x_27);
x_30 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_28);
x_6 = x_30;
x_7 = x_29;
goto block_18;
}
else
{
uint8 x_31; 
x_31 = lean::cnstr_get_scalar<uint8>(x_28, sizeof(void*)*1);
if (x_31 == 0)
{
obj* x_32; obj* x_33; uint8 x_34; 
x_32 = lean::cnstr_get(x_27, 1);
lean::inc(x_32);
lean::dec(x_27);
x_33 = lean::cnstr_get(x_28, 0);
lean::inc(x_33);
lean::dec(x_28);
x_34 = l_String_OldIterator_hasNext___main(x_23);
if (x_34 == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::free_heap_obj(x_20);
x_35 = lean::box(0);
x_36 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_37 = l_mjoin___rarg___closed__1;
x_38 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_36, x_37, x_35, x_35, x_2, x_3, x_23, x_32);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_38, 1);
lean::inc(x_40);
lean::dec(x_38);
x_41 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_42 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_41, x_39);
x_43 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_42);
x_44 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_43);
x_6 = x_44;
x_7 = x_40;
goto block_18;
}
else
{
uint32 x_45; uint8 x_46; 
x_45 = l_String_OldIterator_curr___main(x_23);
x_46 = l_Lean_isIdFirst(x_45);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::free_heap_obj(x_20);
x_47 = l_Char_quoteCore(x_45);
x_48 = l_Char_HasRepr___closed__1;
x_49 = lean::string_append(x_48, x_47);
lean::dec(x_47);
x_50 = lean::string_append(x_49, x_48);
x_51 = lean::box(0);
x_52 = l_mjoin___rarg___closed__1;
x_53 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_50, x_52, x_51, x_51, x_2, x_3, x_23, x_32);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
x_55 = lean::cnstr_get(x_53, 1);
lean::inc(x_55);
lean::dec(x_53);
x_56 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_57 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_56, x_54);
x_58 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_57);
x_59 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_58);
x_6 = x_59;
x_7 = x_55;
goto block_18;
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_33);
x_60 = l_String_OldIterator_next___main(x_23);
x_61 = lean::box(0);
x_62 = lean::box_uint32(x_45);
lean::cnstr_set(x_20, 2, x_61);
lean::cnstr_set(x_20, 1, x_60);
lean::cnstr_set(x_20, 0, x_62);
x_63 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_20);
x_6 = x_63;
x_7 = x_32;
goto block_18;
}
}
}
else
{
obj* x_64; obj* x_65; 
lean::free_heap_obj(x_20);
lean::dec(x_23);
x_64 = lean::cnstr_get(x_27, 1);
lean::inc(x_64);
lean::dec(x_27);
x_65 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_28);
x_6 = x_65;
x_7 = x_64;
goto block_18;
}
}
}
else
{
obj* x_66; obj* x_67; uint32 x_68; obj* x_69; obj* x_70; 
x_66 = lean::cnstr_get(x_20, 1);
x_67 = lean::cnstr_get(x_20, 2);
lean::inc(x_67);
lean::inc(x_66);
lean::dec(x_20);
x_68 = l_Lean_idBeginEscape;
lean::inc(x_66);
x_69 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1(x_68, x_2, x_3, x_66, x_21);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
if (lean::obj_tag(x_70) == 0)
{
obj* x_71; obj* x_72; 
lean::dec(x_66);
x_71 = lean::cnstr_get(x_69, 1);
lean::inc(x_71);
lean::dec(x_69);
x_72 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_67, x_70);
x_6 = x_72;
x_7 = x_71;
goto block_18;
}
else
{
uint8 x_73; 
x_73 = lean::cnstr_get_scalar<uint8>(x_70, sizeof(void*)*1);
if (x_73 == 0)
{
obj* x_74; obj* x_75; uint8 x_76; 
x_74 = lean::cnstr_get(x_69, 1);
lean::inc(x_74);
lean::dec(x_69);
x_75 = lean::cnstr_get(x_70, 0);
lean::inc(x_75);
lean::dec(x_70);
x_76 = l_String_OldIterator_hasNext___main(x_66);
if (x_76 == 0)
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_77 = lean::box(0);
x_78 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_79 = l_mjoin___rarg___closed__1;
x_80 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_78, x_79, x_77, x_77, x_2, x_3, x_66, x_74);
x_81 = lean::cnstr_get(x_80, 0);
lean::inc(x_81);
x_82 = lean::cnstr_get(x_80, 1);
lean::inc(x_82);
lean::dec(x_80);
x_83 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_84 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_83, x_81);
x_85 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_75, x_84);
x_86 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_67, x_85);
x_6 = x_86;
x_7 = x_82;
goto block_18;
}
else
{
uint32 x_87; uint8 x_88; 
x_87 = l_String_OldIterator_curr___main(x_66);
x_88 = l_Lean_isIdFirst(x_87);
if (x_88 == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_89 = l_Char_quoteCore(x_87);
x_90 = l_Char_HasRepr___closed__1;
x_91 = lean::string_append(x_90, x_89);
lean::dec(x_89);
x_92 = lean::string_append(x_91, x_90);
x_93 = lean::box(0);
x_94 = l_mjoin___rarg___closed__1;
x_95 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_92, x_94, x_93, x_93, x_2, x_3, x_66, x_74);
x_96 = lean::cnstr_get(x_95, 0);
lean::inc(x_96);
x_97 = lean::cnstr_get(x_95, 1);
lean::inc(x_97);
lean::dec(x_95);
x_98 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_99 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_98, x_96);
x_100 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_75, x_99);
x_101 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_67, x_100);
x_6 = x_101;
x_7 = x_97;
goto block_18;
}
else
{
obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
lean::dec(x_75);
x_102 = l_String_OldIterator_next___main(x_66);
x_103 = lean::box(0);
x_104 = lean::box_uint32(x_87);
x_105 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_102);
lean::cnstr_set(x_105, 2, x_103);
x_106 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_67, x_105);
x_6 = x_106;
x_7 = x_74;
goto block_18;
}
}
}
else
{
obj* x_107; obj* x_108; 
lean::dec(x_66);
x_107 = lean::cnstr_get(x_69, 1);
lean::inc(x_107);
lean::dec(x_69);
x_108 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_67, x_70);
x_6 = x_108;
x_7 = x_107;
goto block_18;
}
}
}
}
else
{
obj* x_109; uint8 x_110; 
x_109 = lean::cnstr_get(x_19, 1);
lean::inc(x_109);
lean::dec(x_19);
x_110 = !lean::is_exclusive(x_20);
if (x_110 == 0)
{
x_6 = x_20;
x_7 = x_109;
goto block_18;
}
else
{
obj* x_111; uint8 x_112; obj* x_113; 
x_111 = lean::cnstr_get(x_20, 0);
x_112 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
lean::inc(x_111);
lean::dec(x_20);
x_113 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_113, 0, x_111);
lean::cnstr_set_scalar(x_113, sizeof(void*)*1, x_112);
x_6 = x_113;
x_7 = x_109;
goto block_18;
}
}
block_18:
{
if (lean::obj_tag(x_6) == 0)
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_6);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_6, 2);
lean::dec(x_9);
x_10 = lean::cnstr_get(x_6, 1);
lean::dec(x_10);
x_11 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_6, 2, x_11);
lean::cnstr_set(x_6, 1, x_4);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_6);
lean::cnstr_set(x_12, 1, x_7);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
lean::dec(x_6);
x_14 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_4);
lean::cnstr_set(x_15, 2, x_14);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_7);
return x_16;
}
}
else
{
obj* x_17; 
lean::dec(x_4);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_6);
lean::cnstr_set(x_17, 1, x_7);
return x_17;
}
}
}
}
obj* l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::apply_3(x_1, x_3, x_4, x_5);
return x_6;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__5(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; 
x_7 = l_String_isEmpty(x_1);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::string_length(x_1);
x_9 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_1);
lean::cnstr_set(x_10, 1, x_9);
lean::cnstr_set(x_10, 2, x_9);
lean::inc(x_5);
x_11 = l___private_init_lean_parser_parsec_2__strAux___main(x_8, x_10, x_5);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; obj* x_14; uint8 x_15; obj* x_16; obj* x_17; 
lean::dec(x_11);
lean::dec(x_1);
x_12 = lean::box(0);
x_13 = l_String_splitAux___main___closed__1;
x_14 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_14, 0, x_5);
lean::cnstr_set(x_14, 1, x_13);
lean::cnstr_set(x_14, 2, x_2);
lean::cnstr_set(x_14, 3, x_12);
x_15 = 0;
x_16 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set_scalar(x_16, sizeof(void*)*1, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_6);
return x_17;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_5);
lean::dec(x_2);
x_18 = lean::cnstr_get(x_11, 0);
lean::inc(x_18);
lean::dec(x_11);
x_19 = lean::box(0);
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_1);
lean::cnstr_set(x_20, 1, x_18);
lean::cnstr_set(x_20, 2, x_19);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_6);
return x_21;
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
lean::dec(x_2);
lean::dec(x_1);
x_22 = l_String_splitAux___main___closed__1;
x_23 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_5);
lean::cnstr_set(x_24, 2, x_23);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_6);
return x_25;
}
}
}
obj* l_ReaderT_bind___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__6___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
lean::inc(x_4);
lean::inc(x_3);
x_7 = lean::apply_4(x_1, x_3, x_4, x_5, x_6);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_9 = lean::cnstr_get(x_7, 1);
lean::inc(x_9);
lean::dec(x_7);
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_8, 2);
lean::inc(x_12);
lean::dec(x_8);
x_13 = lean::apply_5(x_2, x_10, x_3, x_4, x_11, x_9);
x_14 = !lean::is_exclusive(x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_13, 0);
x_16 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_15);
lean::cnstr_set(x_13, 0, x_16);
return x_13;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_17 = lean::cnstr_get(x_13, 0);
x_18 = lean::cnstr_get(x_13, 1);
lean::inc(x_18);
lean::inc(x_17);
lean::dec(x_13);
x_19 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_17);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8 x_21; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_21 = !lean::is_exclusive(x_7);
if (x_21 == 0)
{
obj* x_22; uint8 x_23; 
x_22 = lean::cnstr_get(x_7, 0);
lean::dec(x_22);
x_23 = !lean::is_exclusive(x_8);
if (x_23 == 0)
{
return x_7;
}
else
{
obj* x_24; uint8 x_25; obj* x_26; 
x_24 = lean::cnstr_get(x_8, 0);
x_25 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
lean::inc(x_24);
lean::dec(x_8);
x_26 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set_scalar(x_26, sizeof(void*)*1, x_25);
lean::cnstr_set(x_7, 0, x_26);
return x_7;
}
}
else
{
obj* x_27; obj* x_28; uint8 x_29; obj* x_30; obj* x_31; obj* x_32; 
x_27 = lean::cnstr_get(x_7, 1);
lean::inc(x_27);
lean::dec(x_7);
x_28 = lean::cnstr_get(x_8, 0);
lean::inc(x_28);
x_29 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_30 = x_8;
} else {
 lean::dec_ref(x_8);
 x_30 = lean::box(0);
}
if (lean::is_scalar(x_30)) {
 x_31 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_31 = x_30;
}
lean::cnstr_set(x_31, 0, x_28);
lean::cnstr_set_scalar(x_31, sizeof(void*)*1, x_29);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_27);
return x_32;
}
}
}
}
obj* l_ReaderT_bind___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__6(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__6___rarg), 6, 0);
return x_3;
}
}
obj* l_Lean_Parser_RecT_recurse___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__7(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = lean::apply_4(x_2, x_1, x_3, x_4, x_5);
return x_6;
}
}
obj* l_List_mfoldl___main___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__9(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_8 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_9 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_6);
lean::cnstr_set(x_9, 2, x_8);
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_7);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_67; obj* x_68; 
x_11 = lean::cnstr_get(x_3, 0);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_3, 1);
lean::inc(x_12);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 x_13 = x_3;
} else {
 lean::dec_ref(x_3);
 x_13 = lean::box(0);
}
lean::inc(x_5);
lean::inc(x_4);
x_67 = lean::apply_4(x_11, x_4, x_5, x_6, x_7);
x_68 = lean::cnstr_get(x_67, 0);
lean::inc(x_68);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; 
x_69 = lean::cnstr_get(x_67, 1);
lean::inc(x_69);
lean::dec(x_67);
x_14 = x_68;
x_15 = x_69;
goto block_66;
}
else
{
if (lean::obj_tag(x_2) == 0)
{
uint8 x_70; 
x_70 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
if (x_70 == 0)
{
obj* x_71; uint8 x_72; 
x_71 = lean::cnstr_get(x_67, 1);
lean::inc(x_71);
lean::dec(x_67);
x_72 = !lean::is_exclusive(x_68);
if (x_72 == 0)
{
uint8 x_73; 
x_73 = 0;
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_73);
x_14 = x_68;
x_15 = x_71;
goto block_66;
}
else
{
obj* x_74; uint8 x_75; obj* x_76; 
x_74 = lean::cnstr_get(x_68, 0);
lean::inc(x_74);
lean::dec(x_68);
x_75 = 0;
x_76 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_76, 0, x_74);
lean::cnstr_set_scalar(x_76, sizeof(void*)*1, x_75);
x_14 = x_76;
x_15 = x_71;
goto block_66;
}
}
else
{
obj* x_77; uint8 x_78; 
x_77 = lean::cnstr_get(x_67, 1);
lean::inc(x_77);
lean::dec(x_67);
x_78 = !lean::is_exclusive(x_68);
if (x_78 == 0)
{
uint8 x_79; 
x_79 = 1;
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_79);
x_14 = x_68;
x_15 = x_77;
goto block_66;
}
else
{
obj* x_80; uint8 x_81; obj* x_82; 
x_80 = lean::cnstr_get(x_68, 0);
lean::inc(x_80);
lean::dec(x_68);
x_81 = 1;
x_82 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_82, 0, x_80);
lean::cnstr_set_scalar(x_82, sizeof(void*)*1, x_81);
x_14 = x_82;
x_15 = x_77;
goto block_66;
}
}
}
else
{
obj* x_83; obj* x_84; 
x_83 = lean::cnstr_get(x_68, 0);
lean::inc(x_83);
x_84 = lean::cnstr_get(x_83, 3);
lean::inc(x_84);
if (lean::obj_tag(x_84) == 0)
{
obj* x_85; uint8 x_86; 
lean::dec(x_84);
x_85 = lean::cnstr_get(x_67, 1);
lean::inc(x_85);
lean::dec(x_67);
x_86 = !lean::is_exclusive(x_68);
if (x_86 == 0)
{
uint8 x_87; obj* x_88; uint8 x_89; 
x_87 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
x_88 = lean::cnstr_get(x_68, 0);
lean::dec(x_88);
x_89 = !lean::is_exclusive(x_83);
if (x_89 == 0)
{
obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_90 = lean::cnstr_get(x_83, 3);
lean::dec(x_90);
x_91 = lean::box(3);
lean::inc(x_2);
x_92 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_2);
x_93 = l_List_reverse___rarg(x_92);
lean::inc(x_1);
x_94 = l_Lean_Parser_Syntax_mkNode(x_1, x_93);
x_95 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_83, 3, x_95);
if (x_87 == 0)
{
uint8 x_96; 
x_96 = 0;
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_96);
x_14 = x_68;
x_15 = x_85;
goto block_66;
}
else
{
uint8 x_97; 
x_97 = 1;
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_97);
x_14 = x_68;
x_15 = x_85;
goto block_66;
}
}
else
{
obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_98 = lean::cnstr_get(x_83, 0);
x_99 = lean::cnstr_get(x_83, 1);
x_100 = lean::cnstr_get(x_83, 2);
lean::inc(x_100);
lean::inc(x_99);
lean::inc(x_98);
lean::dec(x_83);
x_101 = lean::box(3);
lean::inc(x_2);
x_102 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_2);
x_103 = l_List_reverse___rarg(x_102);
lean::inc(x_1);
x_104 = l_Lean_Parser_Syntax_mkNode(x_1, x_103);
x_105 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_105, 0, x_104);
x_106 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_106, 0, x_98);
lean::cnstr_set(x_106, 1, x_99);
lean::cnstr_set(x_106, 2, x_100);
lean::cnstr_set(x_106, 3, x_105);
if (x_87 == 0)
{
uint8 x_107; 
x_107 = 0;
lean::cnstr_set(x_68, 0, x_106);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_107);
x_14 = x_68;
x_15 = x_85;
goto block_66;
}
else
{
uint8 x_108; 
x_108 = 1;
lean::cnstr_set(x_68, 0, x_106);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_108);
x_14 = x_68;
x_15 = x_85;
goto block_66;
}
}
}
else
{
uint8 x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
x_109 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
lean::dec(x_68);
x_110 = lean::cnstr_get(x_83, 0);
lean::inc(x_110);
x_111 = lean::cnstr_get(x_83, 1);
lean::inc(x_111);
x_112 = lean::cnstr_get(x_83, 2);
lean::inc(x_112);
if (lean::is_exclusive(x_83)) {
 lean::cnstr_release(x_83, 0);
 lean::cnstr_release(x_83, 1);
 lean::cnstr_release(x_83, 2);
 lean::cnstr_release(x_83, 3);
 x_113 = x_83;
} else {
 lean::dec_ref(x_83);
 x_113 = lean::box(0);
}
x_114 = lean::box(3);
lean::inc(x_2);
x_115 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_115, 0, x_114);
lean::cnstr_set(x_115, 1, x_2);
x_116 = l_List_reverse___rarg(x_115);
lean::inc(x_1);
x_117 = l_Lean_Parser_Syntax_mkNode(x_1, x_116);
x_118 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_118, 0, x_117);
if (lean::is_scalar(x_113)) {
 x_119 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_119 = x_113;
}
lean::cnstr_set(x_119, 0, x_110);
lean::cnstr_set(x_119, 1, x_111);
lean::cnstr_set(x_119, 2, x_112);
lean::cnstr_set(x_119, 3, x_118);
if (x_109 == 0)
{
uint8 x_120; obj* x_121; 
x_120 = 0;
x_121 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_121, 0, x_119);
lean::cnstr_set_scalar(x_121, sizeof(void*)*1, x_120);
x_14 = x_121;
x_15 = x_85;
goto block_66;
}
else
{
uint8 x_122; obj* x_123; 
x_122 = 1;
x_123 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_123, 0, x_119);
lean::cnstr_set_scalar(x_123, sizeof(void*)*1, x_122);
x_14 = x_123;
x_15 = x_85;
goto block_66;
}
}
}
else
{
obj* x_124; uint8 x_125; 
x_124 = lean::cnstr_get(x_67, 1);
lean::inc(x_124);
lean::dec(x_67);
x_125 = !lean::is_exclusive(x_68);
if (x_125 == 0)
{
uint8 x_126; obj* x_127; uint8 x_128; 
x_126 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
x_127 = lean::cnstr_get(x_68, 0);
lean::dec(x_127);
x_128 = !lean::is_exclusive(x_83);
if (x_128 == 0)
{
obj* x_129; uint8 x_130; 
x_129 = lean::cnstr_get(x_83, 3);
lean::dec(x_129);
x_130 = !lean::is_exclusive(x_84);
if (x_130 == 0)
{
obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
x_131 = lean::cnstr_get(x_84, 0);
lean::inc(x_2);
x_132 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_132, 0, x_131);
lean::cnstr_set(x_132, 1, x_2);
x_133 = l_List_reverse___rarg(x_132);
lean::inc(x_1);
x_134 = l_Lean_Parser_Syntax_mkNode(x_1, x_133);
lean::cnstr_set(x_84, 0, x_134);
if (x_126 == 0)
{
uint8 x_135; 
x_135 = 0;
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_135);
x_14 = x_68;
x_15 = x_124;
goto block_66;
}
else
{
uint8 x_136; 
x_136 = 1;
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_136);
x_14 = x_68;
x_15 = x_124;
goto block_66;
}
}
else
{
obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
x_137 = lean::cnstr_get(x_84, 0);
lean::inc(x_137);
lean::dec(x_84);
lean::inc(x_2);
x_138 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_138, 0, x_137);
lean::cnstr_set(x_138, 1, x_2);
x_139 = l_List_reverse___rarg(x_138);
lean::inc(x_1);
x_140 = l_Lean_Parser_Syntax_mkNode(x_1, x_139);
x_141 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_141, 0, x_140);
lean::cnstr_set(x_83, 3, x_141);
if (x_126 == 0)
{
uint8 x_142; 
x_142 = 0;
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_142);
x_14 = x_68;
x_15 = x_124;
goto block_66;
}
else
{
uint8 x_143; 
x_143 = 1;
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_143);
x_14 = x_68;
x_15 = x_124;
goto block_66;
}
}
}
else
{
obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; 
x_144 = lean::cnstr_get(x_83, 0);
x_145 = lean::cnstr_get(x_83, 1);
x_146 = lean::cnstr_get(x_83, 2);
lean::inc(x_146);
lean::inc(x_145);
lean::inc(x_144);
lean::dec(x_83);
x_147 = lean::cnstr_get(x_84, 0);
lean::inc(x_147);
if (lean::is_exclusive(x_84)) {
 lean::cnstr_release(x_84, 0);
 x_148 = x_84;
} else {
 lean::dec_ref(x_84);
 x_148 = lean::box(0);
}
lean::inc(x_2);
x_149 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_149, 0, x_147);
lean::cnstr_set(x_149, 1, x_2);
x_150 = l_List_reverse___rarg(x_149);
lean::inc(x_1);
x_151 = l_Lean_Parser_Syntax_mkNode(x_1, x_150);
if (lean::is_scalar(x_148)) {
 x_152 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_152 = x_148;
}
lean::cnstr_set(x_152, 0, x_151);
x_153 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_153, 0, x_144);
lean::cnstr_set(x_153, 1, x_145);
lean::cnstr_set(x_153, 2, x_146);
lean::cnstr_set(x_153, 3, x_152);
if (x_126 == 0)
{
uint8 x_154; 
x_154 = 0;
lean::cnstr_set(x_68, 0, x_153);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_154);
x_14 = x_68;
x_15 = x_124;
goto block_66;
}
else
{
uint8 x_155; 
x_155 = 1;
lean::cnstr_set(x_68, 0, x_153);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_155);
x_14 = x_68;
x_15 = x_124;
goto block_66;
}
}
}
else
{
uint8 x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; 
x_156 = lean::cnstr_get_scalar<uint8>(x_68, sizeof(void*)*1);
lean::dec(x_68);
x_157 = lean::cnstr_get(x_83, 0);
lean::inc(x_157);
x_158 = lean::cnstr_get(x_83, 1);
lean::inc(x_158);
x_159 = lean::cnstr_get(x_83, 2);
lean::inc(x_159);
if (lean::is_exclusive(x_83)) {
 lean::cnstr_release(x_83, 0);
 lean::cnstr_release(x_83, 1);
 lean::cnstr_release(x_83, 2);
 lean::cnstr_release(x_83, 3);
 x_160 = x_83;
} else {
 lean::dec_ref(x_83);
 x_160 = lean::box(0);
}
x_161 = lean::cnstr_get(x_84, 0);
lean::inc(x_161);
if (lean::is_exclusive(x_84)) {
 lean::cnstr_release(x_84, 0);
 x_162 = x_84;
} else {
 lean::dec_ref(x_84);
 x_162 = lean::box(0);
}
lean::inc(x_2);
x_163 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_163, 0, x_161);
lean::cnstr_set(x_163, 1, x_2);
x_164 = l_List_reverse___rarg(x_163);
lean::inc(x_1);
x_165 = l_Lean_Parser_Syntax_mkNode(x_1, x_164);
if (lean::is_scalar(x_162)) {
 x_166 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_166 = x_162;
}
lean::cnstr_set(x_166, 0, x_165);
if (lean::is_scalar(x_160)) {
 x_167 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_167 = x_160;
}
lean::cnstr_set(x_167, 0, x_157);
lean::cnstr_set(x_167, 1, x_158);
lean::cnstr_set(x_167, 2, x_159);
lean::cnstr_set(x_167, 3, x_166);
if (x_156 == 0)
{
uint8 x_168; obj* x_169; 
x_168 = 0;
x_169 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_169, 0, x_167);
lean::cnstr_set_scalar(x_169, sizeof(void*)*1, x_168);
x_14 = x_169;
x_15 = x_124;
goto block_66;
}
else
{
uint8 x_170; obj* x_171; 
x_170 = 1;
x_171 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_171, 0, x_167);
lean::cnstr_set_scalar(x_171, sizeof(void*)*1, x_170);
x_14 = x_171;
x_15 = x_124;
goto block_66;
}
}
}
}
}
block_66:
{
if (lean::obj_tag(x_14) == 0)
{
uint8 x_16; 
x_16 = !lean::is_exclusive(x_14);
if (x_16 == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_17 = lean::cnstr_get(x_14, 0);
x_18 = lean::cnstr_get(x_14, 2);
if (lean::is_scalar(x_13)) {
 x_19 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_19 = x_13;
}
lean::cnstr_set(x_19, 0, x_17);
lean::cnstr_set(x_19, 1, x_2);
x_20 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_14, 2, x_20);
lean::cnstr_set(x_14, 0, x_19);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_14);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; uint8 x_26; 
x_22 = lean::cnstr_get(x_21, 0);
lean::inc(x_22);
x_23 = lean::cnstr_get(x_21, 1);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_21, 2);
lean::inc(x_24);
lean::dec(x_21);
x_25 = l_List_mfoldl___main___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__9(x_1, x_22, x_12, x_4, x_5, x_23, x_15);
x_26 = !lean::is_exclusive(x_25);
if (x_26 == 0)
{
obj* x_27; obj* x_28; 
x_27 = lean::cnstr_get(x_25, 0);
x_28 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_27);
lean::cnstr_set(x_25, 0, x_28);
return x_25;
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_29 = lean::cnstr_get(x_25, 0);
x_30 = lean::cnstr_get(x_25, 1);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_25);
x_31 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_29);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_30);
return x_32;
}
}
else
{
uint8 x_33; 
lean::dec(x_12);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
x_33 = !lean::is_exclusive(x_21);
if (x_33 == 0)
{
obj* x_34; 
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_21);
lean::cnstr_set(x_34, 1, x_15);
return x_34;
}
else
{
obj* x_35; uint8 x_36; obj* x_37; obj* x_38; 
x_35 = lean::cnstr_get(x_21, 0);
x_36 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
lean::inc(x_35);
lean::dec(x_21);
x_37 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set_scalar(x_37, sizeof(void*)*1, x_36);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_15);
return x_38;
}
}
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_39 = lean::cnstr_get(x_14, 0);
x_40 = lean::cnstr_get(x_14, 1);
x_41 = lean::cnstr_get(x_14, 2);
lean::inc(x_41);
lean::inc(x_40);
lean::inc(x_39);
lean::dec(x_14);
if (lean::is_scalar(x_13)) {
 x_42 = lean::alloc_cnstr(1, 2, 0);
} else {
 x_42 = x_13;
}
lean::cnstr_set(x_42, 0, x_39);
lean::cnstr_set(x_42, 1, x_2);
x_43 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_44 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_44, 0, x_42);
lean::cnstr_set(x_44, 1, x_40);
lean::cnstr_set(x_44, 2, x_43);
x_45 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_41, x_44);
if (lean::obj_tag(x_45) == 0)
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_47 = lean::cnstr_get(x_45, 1);
lean::inc(x_47);
x_48 = lean::cnstr_get(x_45, 2);
lean::inc(x_48);
lean::dec(x_45);
x_49 = l_List_mfoldl___main___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__9(x_1, x_46, x_12, x_4, x_5, x_47, x_15);
x_50 = lean::cnstr_get(x_49, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_49, 1);
lean::inc(x_51);
if (lean::is_exclusive(x_49)) {
 lean::cnstr_release(x_49, 0);
 lean::cnstr_release(x_49, 1);
 x_52 = x_49;
} else {
 lean::dec_ref(x_49);
 x_52 = lean::box(0);
}
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_48, x_50);
if (lean::is_scalar(x_52)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_52;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_51);
return x_54;
}
else
{
obj* x_55; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_12);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
x_55 = lean::cnstr_get(x_45, 0);
lean::inc(x_55);
x_56 = lean::cnstr_get_scalar<uint8>(x_45, sizeof(void*)*1);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 x_57 = x_45;
} else {
 lean::dec_ref(x_45);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_55);
lean::cnstr_set_scalar(x_58, sizeof(void*)*1, x_56);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_15);
return x_59;
}
}
}
else
{
uint8 x_60; 
lean::dec(x_13);
lean::dec(x_12);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_2);
lean::dec(x_1);
x_60 = !lean::is_exclusive(x_14);
if (x_60 == 0)
{
obj* x_61; 
x_61 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_61, 0, x_14);
lean::cnstr_set(x_61, 1, x_15);
return x_61;
}
else
{
obj* x_62; uint8 x_63; obj* x_64; obj* x_65; 
x_62 = lean::cnstr_get(x_14, 0);
x_63 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
lean::inc(x_62);
lean::dec(x_14);
x_64 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_64, 0, x_62);
lean::cnstr_set_scalar(x_64, sizeof(void*)*1, x_63);
x_65 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::cnstr_set(x_65, 1, x_15);
return x_65;
}
}
}
}
}
}
obj* l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__8(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = lean::box(0);
lean::inc(x_1);
x_8 = l_List_mfoldl___main___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__9(x_1, x_7, x_2, x_3, x_4, x_5, x_6);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_8);
if (x_10 == 0)
{
obj* x_11; uint8 x_12; 
x_11 = lean::cnstr_get(x_8, 0);
lean::dec(x_11);
x_12 = !lean::is_exclusive(x_9);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_13 = lean::cnstr_get(x_9, 0);
x_14 = lean::cnstr_get(x_9, 2);
x_15 = l_List_reverse___rarg(x_13);
x_16 = l_Lean_Parser_Syntax_mkNode(x_1, x_15);
x_17 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_9, 2, x_17);
lean::cnstr_set(x_9, 0, x_16);
x_18 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_9);
lean::cnstr_set(x_8, 0, x_18);
return x_8;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_19 = lean::cnstr_get(x_9, 0);
x_20 = lean::cnstr_get(x_9, 1);
x_21 = lean::cnstr_get(x_9, 2);
lean::inc(x_21);
lean::inc(x_20);
lean::inc(x_19);
lean::dec(x_9);
x_22 = l_List_reverse___rarg(x_19);
x_23 = l_Lean_Parser_Syntax_mkNode(x_1, x_22);
x_24 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set(x_25, 1, x_20);
lean::cnstr_set(x_25, 2, x_24);
x_26 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_25);
lean::cnstr_set(x_8, 0, x_26);
return x_8;
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_27 = lean::cnstr_get(x_8, 1);
lean::inc(x_27);
lean::dec(x_8);
x_28 = lean::cnstr_get(x_9, 0);
lean::inc(x_28);
x_29 = lean::cnstr_get(x_9, 1);
lean::inc(x_29);
x_30 = lean::cnstr_get(x_9, 2);
lean::inc(x_30);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 x_31 = x_9;
} else {
 lean::dec_ref(x_9);
 x_31 = lean::box(0);
}
x_32 = l_List_reverse___rarg(x_28);
x_33 = l_Lean_Parser_Syntax_mkNode(x_1, x_32);
x_34 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_31)) {
 x_35 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_35 = x_31;
}
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set(x_35, 1, x_29);
lean::cnstr_set(x_35, 2, x_34);
x_36 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_30, x_35);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_27);
return x_37;
}
}
else
{
uint8 x_38; 
lean::dec(x_1);
x_38 = !lean::is_exclusive(x_8);
if (x_38 == 0)
{
obj* x_39; uint8 x_40; 
x_39 = lean::cnstr_get(x_8, 0);
lean::dec(x_39);
x_40 = !lean::is_exclusive(x_9);
if (x_40 == 0)
{
return x_8;
}
else
{
obj* x_41; uint8 x_42; obj* x_43; 
x_41 = lean::cnstr_get(x_9, 0);
x_42 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
lean::inc(x_41);
lean::dec(x_9);
x_43 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set_scalar(x_43, sizeof(void*)*1, x_42);
lean::cnstr_set(x_8, 0, x_43);
return x_8;
}
}
else
{
obj* x_44; obj* x_45; uint8 x_46; obj* x_47; obj* x_48; obj* x_49; 
x_44 = lean::cnstr_get(x_8, 1);
lean::inc(x_44);
lean::dec(x_8);
x_45 = lean::cnstr_get(x_9, 0);
lean::inc(x_45);
x_46 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_47 = x_9;
} else {
 lean::dec_ref(x_9);
 x_47 = lean::box(0);
}
if (lean::is_scalar(x_47)) {
 x_48 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_48 = x_47;
}
lean::cnstr_set(x_48, 0, x_45);
lean::cnstr_set_scalar(x_48, sizeof(void*)*1, x_46);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_44);
return x_49;
}
}
}
}
obj* _init_l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_1);
x_3 = l_Lean_Parser_List_cons_tokens___rarg(x_1, x_2);
lean::dec(x_2);
x_4 = l_Lean_Parser_tokens___rarg(x_3);
lean::dec(x_3);
x_5 = l_Lean_Parser_tokens___rarg(x_4);
lean::dec(x_4);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_3);
return x_9;
}
}
obj* l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint32 x_6; obj* x_7; 
x_6 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_7 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1(x_6, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint32 x_6; obj* x_7; 
x_6 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_7 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__3(x_6, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
}
obj* l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__5___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__5(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_3);
return x_7;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___spec__1(uint32 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_19; obj* x_20; 
lean::inc(x_4);
x_19 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1(x_1, x_2, x_3, x_4, x_5);
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; uint8 x_22; 
x_21 = lean::cnstr_get(x_19, 1);
lean::inc(x_21);
lean::dec(x_19);
x_22 = !lean::is_exclusive(x_20);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; uint32 x_26; obj* x_27; obj* x_28; 
x_23 = lean::cnstr_get(x_20, 1);
x_24 = lean::cnstr_get(x_20, 2);
x_25 = lean::cnstr_get(x_20, 0);
lean::dec(x_25);
x_26 = l_Lean_idBeginEscape;
lean::inc(x_23);
x_27 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1(x_26, x_2, x_3, x_23, x_21);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_30; 
lean::free_heap_obj(x_20);
lean::dec(x_23);
x_29 = lean::cnstr_get(x_27, 1);
lean::inc(x_29);
lean::dec(x_27);
x_30 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_28);
x_6 = x_30;
x_7 = x_29;
goto block_18;
}
else
{
uint8 x_31; 
x_31 = lean::cnstr_get_scalar<uint8>(x_28, sizeof(void*)*1);
if (x_31 == 0)
{
obj* x_32; obj* x_33; uint8 x_34; 
x_32 = lean::cnstr_get(x_27, 1);
lean::inc(x_32);
lean::dec(x_27);
x_33 = lean::cnstr_get(x_28, 0);
lean::inc(x_33);
lean::dec(x_28);
x_34 = l_String_OldIterator_hasNext___main(x_23);
if (x_34 == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::free_heap_obj(x_20);
x_35 = lean::box(0);
x_36 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_37 = l_mjoin___rarg___closed__1;
x_38 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_36, x_37, x_35, x_35, x_2, x_3, x_23, x_32);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_38, 1);
lean::inc(x_40);
lean::dec(x_38);
x_41 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_42 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_41, x_39);
x_43 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_42);
x_44 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_43);
x_6 = x_44;
x_7 = x_40;
goto block_18;
}
else
{
uint32 x_45; uint8 x_46; 
x_45 = l_String_OldIterator_curr___main(x_23);
x_46 = l_Lean_isIdFirst(x_45);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::free_heap_obj(x_20);
x_47 = l_Char_quoteCore(x_45);
x_48 = l_Char_HasRepr___closed__1;
x_49 = lean::string_append(x_48, x_47);
lean::dec(x_47);
x_50 = lean::string_append(x_49, x_48);
x_51 = lean::box(0);
x_52 = l_mjoin___rarg___closed__1;
x_53 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_50, x_52, x_51, x_51, x_2, x_3, x_23, x_32);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
x_55 = lean::cnstr_get(x_53, 1);
lean::inc(x_55);
lean::dec(x_53);
x_56 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_57 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_56, x_54);
x_58 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_57);
x_59 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_58);
x_6 = x_59;
x_7 = x_55;
goto block_18;
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_33);
x_60 = l_String_OldIterator_next___main(x_23);
x_61 = lean::box(0);
x_62 = lean::box_uint32(x_45);
lean::cnstr_set(x_20, 2, x_61);
lean::cnstr_set(x_20, 1, x_60);
lean::cnstr_set(x_20, 0, x_62);
x_63 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_20);
x_6 = x_63;
x_7 = x_32;
goto block_18;
}
}
}
else
{
obj* x_64; obj* x_65; 
lean::free_heap_obj(x_20);
lean::dec(x_23);
x_64 = lean::cnstr_get(x_27, 1);
lean::inc(x_64);
lean::dec(x_27);
x_65 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_28);
x_6 = x_65;
x_7 = x_64;
goto block_18;
}
}
}
else
{
obj* x_66; obj* x_67; uint32 x_68; obj* x_69; obj* x_70; 
x_66 = lean::cnstr_get(x_20, 1);
x_67 = lean::cnstr_get(x_20, 2);
lean::inc(x_67);
lean::inc(x_66);
lean::dec(x_20);
x_68 = l_Lean_idBeginEscape;
lean::inc(x_66);
x_69 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1(x_68, x_2, x_3, x_66, x_21);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
if (lean::obj_tag(x_70) == 0)
{
obj* x_71; obj* x_72; 
lean::dec(x_66);
x_71 = lean::cnstr_get(x_69, 1);
lean::inc(x_71);
lean::dec(x_69);
x_72 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_67, x_70);
x_6 = x_72;
x_7 = x_71;
goto block_18;
}
else
{
uint8 x_73; 
x_73 = lean::cnstr_get_scalar<uint8>(x_70, sizeof(void*)*1);
if (x_73 == 0)
{
obj* x_74; obj* x_75; uint8 x_76; 
x_74 = lean::cnstr_get(x_69, 1);
lean::inc(x_74);
lean::dec(x_69);
x_75 = lean::cnstr_get(x_70, 0);
lean::inc(x_75);
lean::dec(x_70);
x_76 = l_String_OldIterator_hasNext___main(x_66);
if (x_76 == 0)
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_77 = lean::box(0);
x_78 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_79 = l_mjoin___rarg___closed__1;
x_80 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_78, x_79, x_77, x_77, x_2, x_3, x_66, x_74);
x_81 = lean::cnstr_get(x_80, 0);
lean::inc(x_81);
x_82 = lean::cnstr_get(x_80, 1);
lean::inc(x_82);
lean::dec(x_80);
x_83 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_84 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_83, x_81);
x_85 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_75, x_84);
x_86 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_67, x_85);
x_6 = x_86;
x_7 = x_82;
goto block_18;
}
else
{
uint32 x_87; uint8 x_88; 
x_87 = l_String_OldIterator_curr___main(x_66);
x_88 = l_Lean_isIdFirst(x_87);
if (x_88 == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_89 = l_Char_quoteCore(x_87);
x_90 = l_Char_HasRepr___closed__1;
x_91 = lean::string_append(x_90, x_89);
lean::dec(x_89);
x_92 = lean::string_append(x_91, x_90);
x_93 = lean::box(0);
x_94 = l_mjoin___rarg___closed__1;
x_95 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_92, x_94, x_93, x_93, x_2, x_3, x_66, x_74);
x_96 = lean::cnstr_get(x_95, 0);
lean::inc(x_96);
x_97 = lean::cnstr_get(x_95, 1);
lean::inc(x_97);
lean::dec(x_95);
x_98 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_99 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_98, x_96);
x_100 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_75, x_99);
x_101 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_67, x_100);
x_6 = x_101;
x_7 = x_97;
goto block_18;
}
else
{
obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
lean::dec(x_75);
x_102 = l_String_OldIterator_next___main(x_66);
x_103 = lean::box(0);
x_104 = lean::box_uint32(x_87);
x_105 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_102);
lean::cnstr_set(x_105, 2, x_103);
x_106 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_67, x_105);
x_6 = x_106;
x_7 = x_74;
goto block_18;
}
}
}
else
{
obj* x_107; obj* x_108; 
lean::dec(x_66);
x_107 = lean::cnstr_get(x_69, 1);
lean::inc(x_107);
lean::dec(x_69);
x_108 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_67, x_70);
x_6 = x_108;
x_7 = x_107;
goto block_18;
}
}
}
}
else
{
obj* x_109; uint8 x_110; 
x_109 = lean::cnstr_get(x_19, 1);
lean::inc(x_109);
lean::dec(x_19);
x_110 = !lean::is_exclusive(x_20);
if (x_110 == 0)
{
x_6 = x_20;
x_7 = x_109;
goto block_18;
}
else
{
obj* x_111; uint8 x_112; obj* x_113; 
x_111 = lean::cnstr_get(x_20, 0);
x_112 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
lean::inc(x_111);
lean::dec(x_20);
x_113 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_113, 0, x_111);
lean::cnstr_set_scalar(x_113, sizeof(void*)*1, x_112);
x_6 = x_113;
x_7 = x_109;
goto block_18;
}
}
block_18:
{
if (lean::obj_tag(x_6) == 0)
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_6);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_6, 2);
lean::dec(x_9);
x_10 = lean::cnstr_get(x_6, 1);
lean::dec(x_10);
x_11 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_6, 2, x_11);
lean::cnstr_set(x_6, 1, x_4);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_6);
lean::cnstr_set(x_12, 1, x_7);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
lean::dec(x_6);
x_14 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_4);
lean::cnstr_set(x_15, 2, x_14);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_7);
return x_16;
}
}
else
{
obj* x_17; 
lean::dec(x_4);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_6);
lean::cnstr_set(x_17, 1, x_7);
return x_17;
}
}
}
}
obj* l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__1(uint32 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___spec__1(x_1, x_2, x_3, x_4, x_5);
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_6, 0);
x_9 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_8);
lean::cnstr_set(x_6, 0, x_9);
return x_6;
}
else
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_6, 0);
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
lean::inc(x_10);
lean::dec(x_6);
x_12 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_10);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_12);
lean::cnstr_set(x_13, 1, x_11);
return x_13;
}
}
}
obj* l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
x_7 = l_Lean_Name_toString___closed__1;
x_8 = l_Lean_Parser_MonadParsec_strCore___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__5(x_7, x_1, x_3, x_4, x_5, x_6);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_8);
if (x_10 == 0)
{
obj* x_11; uint8 x_12; 
x_11 = lean::cnstr_get(x_8, 0);
lean::dec(x_11);
x_12 = !lean::is_exclusive(x_9);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_13 = lean::cnstr_get(x_9, 1);
x_14 = lean::cnstr_get(x_9, 2);
x_15 = lean::cnstr_get(x_9, 0);
lean::dec(x_15);
lean::inc(x_13);
x_16 = l_Lean_Parser_mkRawRes(x_2, x_13);
x_17 = l_Lean_Parser_finishCommentBlock___closed__2;
lean::cnstr_set(x_9, 2, x_17);
lean::cnstr_set(x_9, 0, x_16);
x_18 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_9);
lean::cnstr_set(x_8, 0, x_18);
return x_8;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_19 = lean::cnstr_get(x_9, 1);
x_20 = lean::cnstr_get(x_9, 2);
lean::inc(x_20);
lean::inc(x_19);
lean::dec(x_9);
lean::inc(x_19);
x_21 = l_Lean_Parser_mkRawRes(x_2, x_19);
x_22 = l_Lean_Parser_finishCommentBlock___closed__2;
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_19);
lean::cnstr_set(x_23, 2, x_22);
x_24 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_20, x_23);
lean::cnstr_set(x_8, 0, x_24);
return x_8;
}
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_25 = lean::cnstr_get(x_8, 1);
lean::inc(x_25);
lean::dec(x_8);
x_26 = lean::cnstr_get(x_9, 1);
lean::inc(x_26);
x_27 = lean::cnstr_get(x_9, 2);
lean::inc(x_27);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 x_28 = x_9;
} else {
 lean::dec_ref(x_9);
 x_28 = lean::box(0);
}
lean::inc(x_26);
x_29 = l_Lean_Parser_mkRawRes(x_2, x_26);
x_30 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_28)) {
 x_31 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_31 = x_28;
}
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set(x_31, 1, x_26);
lean::cnstr_set(x_31, 2, x_30);
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_27, x_31);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_25);
return x_33;
}
}
else
{
uint8 x_34; 
lean::dec(x_2);
x_34 = !lean::is_exclusive(x_8);
if (x_34 == 0)
{
obj* x_35; uint8 x_36; 
x_35 = lean::cnstr_get(x_8, 0);
lean::dec(x_35);
x_36 = !lean::is_exclusive(x_9);
if (x_36 == 0)
{
return x_8;
}
else
{
obj* x_37; uint8 x_38; obj* x_39; 
x_37 = lean::cnstr_get(x_9, 0);
x_38 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
lean::inc(x_37);
lean::dec(x_9);
x_39 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set_scalar(x_39, sizeof(void*)*1, x_38);
lean::cnstr_set(x_8, 0, x_39);
return x_8;
}
}
else
{
obj* x_40; obj* x_41; uint8 x_42; obj* x_43; obj* x_44; obj* x_45; 
x_40 = lean::cnstr_get(x_8, 1);
lean::inc(x_40);
lean::dec(x_8);
x_41 = lean::cnstr_get(x_9, 0);
lean::inc(x_41);
x_42 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_43 = x_9;
} else {
 lean::dec_ref(x_9);
 x_43 = lean::box(0);
}
if (lean::is_scalar(x_43)) {
 x_44 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_44 = x_43;
}
lean::cnstr_set(x_44, 0, x_41);
lean::cnstr_set_scalar(x_44, sizeof(void*)*1, x_42);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_40);
return x_45;
}
}
}
}
obj* _init_l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint32 x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_1 = l_Lean_Parser_BasicParserM_Monad;
x_2 = l_ReaderT_Monad___rarg(x_1);
x_3 = l_Lean_Parser_BasicParserM_MonadExcept;
x_4 = l_ReaderT_MonadExcept___rarg(x_3);
x_5 = l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
x_6 = l_Lean_Parser_RecT_Lean_Parser_MonadParsec___rarg(x_1, lean::box(0), x_5);
x_7 = l_Lean_Parser_BasicParserM_Alternative;
x_8 = l_ReaderT_Alternative___rarg(x_1, x_7);
x_9 = 46;
x_10 = lean::box_uint32(x_9);
x_11 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__1___boxed), 5, 1);
lean::closure_set(x_11, 0, x_10);
x_12 = lean::mk_string(".");
x_13 = l_String_quote(x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_16, 0, x_15);
x_17 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed), 5, 1);
lean::closure_set(x_17, 0, x_16);
x_18 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__2___boxed), 6, 1);
lean::closure_set(x_18, 0, x_14);
x_19 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__6___rarg), 6, 2);
lean::closure_set(x_19, 0, x_17);
lean::closure_set(x_19, 1, x_18);
x_20 = lean::box(0);
x_21 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_recurse___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__7), 5, 1);
lean::closure_set(x_21, 0, x_20);
x_22 = lean::box(0);
x_23 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_23, 0, x_21);
lean::cnstr_set(x_23, 1, x_22);
x_24 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_24, 0, x_19);
lean::cnstr_set(x_24, 1, x_23);
x_25 = l_Lean_Parser_detailIdentSuffix;
lean::inc(x_24);
x_26 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__8), 6, 2);
lean::closure_set(x_26, 0, x_25);
lean::closure_set(x_26, 1, x_24);
x_27 = l_Lean_Parser_detailIdentSuffix_HasView;
x_28 = l_Lean_Parser_Combinators_node_view___rarg(x_2, x_4, x_6, x_8, x_25, x_24, x_27);
lean::dec(x_24);
lean::dec(x_6);
lean::dec(x_4);
lean::dec(x_2);
x_29 = l_Lean_Parser_Combinators_seqRight_view___rarg(x_8, lean::box(0), lean::box(0), x_11, x_26, x_28);
lean::dec(x_26);
lean::dec(x_11);
lean::dec(x_8);
return x_29;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint32 x_6; obj* x_7; 
x_6 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_7 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___spec__1(x_6, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
}
obj* l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint32 x_6; obj* x_7; 
x_6 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_7 = l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__1(x_6, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_2);
return x_7;
}
}
obj* l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_4);
lean::dec(x_3);
return x_7;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser___spec__1(obj* x_1, obj* x_2, uint32 x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_19; obj* x_20; 
lean::inc(x_4);
x_19 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1(x_3, x_1, x_2, x_4, x_5);
x_20 = lean::cnstr_get(x_19, 0);
lean::inc(x_20);
if (lean::obj_tag(x_20) == 0)
{
obj* x_21; uint8 x_22; 
x_21 = lean::cnstr_get(x_19, 1);
lean::inc(x_21);
lean::dec(x_19);
x_22 = !lean::is_exclusive(x_20);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; uint32 x_26; obj* x_27; obj* x_28; 
x_23 = lean::cnstr_get(x_20, 1);
x_24 = lean::cnstr_get(x_20, 2);
x_25 = lean::cnstr_get(x_20, 0);
lean::dec(x_25);
x_26 = l_Lean_idBeginEscape;
lean::inc(x_23);
x_27 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1(x_26, x_1, x_2, x_23, x_21);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_30; 
lean::free_heap_obj(x_20);
lean::dec(x_23);
x_29 = lean::cnstr_get(x_27, 1);
lean::inc(x_29);
lean::dec(x_27);
x_30 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_28);
x_6 = x_30;
x_7 = x_29;
goto block_18;
}
else
{
uint8 x_31; 
x_31 = lean::cnstr_get_scalar<uint8>(x_28, sizeof(void*)*1);
if (x_31 == 0)
{
obj* x_32; obj* x_33; uint8 x_34; 
x_32 = lean::cnstr_get(x_27, 1);
lean::inc(x_32);
lean::dec(x_27);
x_33 = lean::cnstr_get(x_28, 0);
lean::inc(x_33);
lean::dec(x_28);
x_34 = l_String_OldIterator_hasNext___main(x_23);
if (x_34 == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::free_heap_obj(x_20);
x_35 = lean::box(0);
x_36 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_37 = l_mjoin___rarg___closed__1;
x_38 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_36, x_37, x_35, x_35, x_1, x_2, x_23, x_32);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_38, 1);
lean::inc(x_40);
lean::dec(x_38);
x_41 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_42 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_41, x_39);
x_43 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_42);
x_44 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_43);
x_6 = x_44;
x_7 = x_40;
goto block_18;
}
else
{
uint32 x_45; uint8 x_46; 
x_45 = l_String_OldIterator_curr___main(x_23);
x_46 = l_Lean_isIdFirst(x_45);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::free_heap_obj(x_20);
x_47 = l_Char_quoteCore(x_45);
x_48 = l_Char_HasRepr___closed__1;
x_49 = lean::string_append(x_48, x_47);
lean::dec(x_47);
x_50 = lean::string_append(x_49, x_48);
x_51 = lean::box(0);
x_52 = l_mjoin___rarg___closed__1;
x_53 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_50, x_52, x_51, x_51, x_1, x_2, x_23, x_32);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
x_55 = lean::cnstr_get(x_53, 1);
lean::inc(x_55);
lean::dec(x_53);
x_56 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_57 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_56, x_54);
x_58 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_33, x_57);
x_59 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_58);
x_6 = x_59;
x_7 = x_55;
goto block_18;
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_33);
x_60 = l_String_OldIterator_next___main(x_23);
x_61 = lean::box(0);
x_62 = lean::box_uint32(x_45);
lean::cnstr_set(x_20, 2, x_61);
lean::cnstr_set(x_20, 1, x_60);
lean::cnstr_set(x_20, 0, x_62);
x_63 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_20);
x_6 = x_63;
x_7 = x_32;
goto block_18;
}
}
}
else
{
obj* x_64; obj* x_65; 
lean::free_heap_obj(x_20);
lean::dec(x_23);
x_64 = lean::cnstr_get(x_27, 1);
lean::inc(x_64);
lean::dec(x_27);
x_65 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_28);
x_6 = x_65;
x_7 = x_64;
goto block_18;
}
}
}
else
{
obj* x_66; obj* x_67; uint32 x_68; obj* x_69; obj* x_70; 
x_66 = lean::cnstr_get(x_20, 1);
x_67 = lean::cnstr_get(x_20, 2);
lean::inc(x_67);
lean::inc(x_66);
lean::dec(x_20);
x_68 = l_Lean_idBeginEscape;
lean::inc(x_66);
x_69 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__1(x_68, x_1, x_2, x_66, x_21);
x_70 = lean::cnstr_get(x_69, 0);
lean::inc(x_70);
if (lean::obj_tag(x_70) == 0)
{
obj* x_71; obj* x_72; 
lean::dec(x_66);
x_71 = lean::cnstr_get(x_69, 1);
lean::inc(x_71);
lean::dec(x_69);
x_72 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_67, x_70);
x_6 = x_72;
x_7 = x_71;
goto block_18;
}
else
{
uint8 x_73; 
x_73 = lean::cnstr_get_scalar<uint8>(x_70, sizeof(void*)*1);
if (x_73 == 0)
{
obj* x_74; obj* x_75; uint8 x_76; 
x_74 = lean::cnstr_get(x_69, 1);
lean::inc(x_74);
lean::dec(x_69);
x_75 = lean::cnstr_get(x_70, 0);
lean::inc(x_75);
lean::dec(x_70);
x_76 = l_String_OldIterator_hasNext___main(x_66);
if (x_76 == 0)
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_77 = lean::box(0);
x_78 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_79 = l_mjoin___rarg___closed__1;
x_80 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_78, x_79, x_77, x_77, x_1, x_2, x_66, x_74);
x_81 = lean::cnstr_get(x_80, 0);
lean::inc(x_81);
x_82 = lean::cnstr_get(x_80, 1);
lean::inc(x_82);
lean::dec(x_80);
x_83 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_84 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_83, x_81);
x_85 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_75, x_84);
x_86 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_67, x_85);
x_6 = x_86;
x_7 = x_82;
goto block_18;
}
else
{
uint32 x_87; uint8 x_88; 
x_87 = l_String_OldIterator_curr___main(x_66);
x_88 = l_Lean_isIdFirst(x_87);
if (x_88 == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_89 = l_Char_quoteCore(x_87);
x_90 = l_Char_HasRepr___closed__1;
x_91 = lean::string_append(x_90, x_89);
lean::dec(x_89);
x_92 = lean::string_append(x_91, x_90);
x_93 = lean::box(0);
x_94 = l_mjoin___rarg___closed__1;
x_95 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__2___rarg(x_92, x_94, x_93, x_93, x_1, x_2, x_66, x_74);
x_96 = lean::cnstr_get(x_95, 0);
lean::inc(x_96);
x_97 = lean::cnstr_get(x_95, 1);
lean::inc(x_97);
lean::dec(x_95);
x_98 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_99 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_98, x_96);
x_100 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_75, x_99);
x_101 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_67, x_100);
x_6 = x_101;
x_7 = x_97;
goto block_18;
}
else
{
obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
lean::dec(x_75);
x_102 = l_String_OldIterator_next___main(x_66);
x_103 = lean::box(0);
x_104 = lean::box_uint32(x_87);
x_105 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_102);
lean::cnstr_set(x_105, 2, x_103);
x_106 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_67, x_105);
x_6 = x_106;
x_7 = x_74;
goto block_18;
}
}
}
else
{
obj* x_107; obj* x_108; 
lean::dec(x_66);
x_107 = lean::cnstr_get(x_69, 1);
lean::inc(x_107);
lean::dec(x_69);
x_108 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_67, x_70);
x_6 = x_108;
x_7 = x_107;
goto block_18;
}
}
}
}
else
{
obj* x_109; uint8 x_110; 
x_109 = lean::cnstr_get(x_19, 1);
lean::inc(x_109);
lean::dec(x_19);
x_110 = !lean::is_exclusive(x_20);
if (x_110 == 0)
{
x_6 = x_20;
x_7 = x_109;
goto block_18;
}
else
{
obj* x_111; uint8 x_112; obj* x_113; 
x_111 = lean::cnstr_get(x_20, 0);
x_112 = lean::cnstr_get_scalar<uint8>(x_20, sizeof(void*)*1);
lean::inc(x_111);
lean::dec(x_20);
x_113 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_113, 0, x_111);
lean::cnstr_set_scalar(x_113, sizeof(void*)*1, x_112);
x_6 = x_113;
x_7 = x_109;
goto block_18;
}
}
block_18:
{
if (lean::obj_tag(x_6) == 0)
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_6);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_6, 2);
lean::dec(x_9);
x_10 = lean::cnstr_get(x_6, 1);
lean::dec(x_10);
x_11 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_6, 2, x_11);
lean::cnstr_set(x_6, 1, x_4);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_6);
lean::cnstr_set(x_12, 1, x_7);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
lean::dec(x_6);
x_14 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_4);
lean::cnstr_set(x_15, 2, x_14);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_7);
return x_16;
}
}
else
{
obj* x_17; 
lean::dec(x_4);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_6);
lean::cnstr_set(x_17, 1, x_7);
return x_17;
}
}
}
}
obj* _init_l_Lean_Parser_detailIdentSuffix_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_1 = lean::mk_string(".");
x_2 = l_String_quote(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed), 5, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasView___lambda__2___boxed), 6, 1);
lean::closure_set(x_7, 0, x_3);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__6___rarg), 6, 2);
lean::closure_set(x_8, 0, x_6);
lean::closure_set(x_8, 1, x_7);
x_9 = lean::box(0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_RecT_recurse___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__7), 5, 1);
lean::closure_set(x_10, 0, x_9);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_8);
lean::cnstr_set(x_13, 1, x_12);
return x_13;
}
}
obj* l_Lean_Parser_detailIdentSuffix_Parser(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; uint8 x_7; 
x_5 = 46;
x_6 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser___spec__1(x_1, x_2, x_5, x_3, x_4);
x_7 = !lean::is_exclusive(x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; 
x_8 = lean::cnstr_get(x_6, 0);
x_9 = lean::cnstr_get(x_6, 1);
x_10 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_8);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint8 x_16; 
lean::free_heap_obj(x_6);
x_11 = lean::cnstr_get(x_10, 1);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_10, 2);
lean::inc(x_12);
lean::dec(x_10);
x_13 = l_Lean_Parser_detailIdentSuffix;
x_14 = l_Lean_Parser_detailIdentSuffix_Parser___closed__1;
x_15 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__8(x_13, x_14, x_1, x_2, x_11, x_9);
x_16 = !lean::is_exclusive(x_15);
if (x_16 == 0)
{
obj* x_17; obj* x_18; 
x_17 = lean::cnstr_get(x_15, 0);
x_18 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_17);
lean::cnstr_set(x_15, 0, x_18);
return x_15;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_19 = lean::cnstr_get(x_15, 0);
x_20 = lean::cnstr_get(x_15, 1);
lean::inc(x_20);
lean::inc(x_19);
lean::dec(x_15);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_19);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8 x_23; 
lean::dec(x_2);
lean::dec(x_1);
x_23 = !lean::is_exclusive(x_10);
if (x_23 == 0)
{
lean::cnstr_set(x_6, 0, x_10);
return x_6;
}
else
{
obj* x_24; uint8 x_25; obj* x_26; 
x_24 = lean::cnstr_get(x_10, 0);
x_25 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
lean::inc(x_24);
lean::dec(x_10);
x_26 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_26, 0, x_24);
lean::cnstr_set_scalar(x_26, sizeof(void*)*1, x_25);
lean::cnstr_set(x_6, 0, x_26);
return x_6;
}
}
}
else
{
obj* x_27; obj* x_28; obj* x_29; 
x_27 = lean::cnstr_get(x_6, 0);
x_28 = lean::cnstr_get(x_6, 1);
lean::inc(x_28);
lean::inc(x_27);
lean::dec(x_6);
x_29 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_27);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_30 = lean::cnstr_get(x_29, 1);
lean::inc(x_30);
x_31 = lean::cnstr_get(x_29, 2);
lean::inc(x_31);
lean::dec(x_29);
x_32 = l_Lean_Parser_detailIdentSuffix;
x_33 = l_Lean_Parser_detailIdentSuffix_Parser___closed__1;
x_34 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__8(x_32, x_33, x_1, x_2, x_30, x_28);
x_35 = lean::cnstr_get(x_34, 0);
lean::inc(x_35);
x_36 = lean::cnstr_get(x_34, 1);
lean::inc(x_36);
if (lean::is_exclusive(x_34)) {
 lean::cnstr_release(x_34, 0);
 lean::cnstr_release(x_34, 1);
 x_37 = x_34;
} else {
 lean::dec_ref(x_34);
 x_37 = lean::box(0);
}
x_38 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_31, x_35);
if (lean::is_scalar(x_37)) {
 x_39 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_39 = x_37;
}
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_36);
return x_39;
}
else
{
obj* x_40; uint8 x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::dec(x_2);
lean::dec(x_1);
x_40 = lean::cnstr_get(x_29, 0);
lean::inc(x_40);
x_41 = lean::cnstr_get_scalar<uint8>(x_29, sizeof(void*)*1);
if (lean::is_exclusive(x_29)) {
 lean::cnstr_release(x_29, 0);
 x_42 = x_29;
} else {
 lean::dec_ref(x_29);
 x_42 = lean::box(0);
}
if (lean::is_scalar(x_42)) {
 x_43 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_43 = x_42;
}
lean::cnstr_set(x_43, 0, x_40);
lean::cnstr_set_scalar(x_43, sizeof(void*)*1, x_41);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_28);
return x_44;
}
}
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint32 x_6; obj* x_7; 
x_6 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_7 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_detailIdentSuffix_Parser___spec__1(x_1, x_2, x_6, x_4, x_5);
lean::dec(x_2);
lean::dec(x_1);
return x_7;
}
}
obj* _init_l_Lean_Parser_detailIdent() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("detailIdent");
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
obj* _init_l_Lean_Parser_detailIdent_HasView_x27___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; 
x_1 = lean::box(0);
x_2 = l_Lean_Parser_noKind;
x_3 = l_Lean_Parser_Syntax_mkNode(x_2, x_1);
x_4 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_1);
return x_4;
}
}
obj* l_Lean_Parser_detailIdent_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::cnstr_get(x_1, 1);
lean::inc(x_3);
lean::dec(x_1);
x_4 = l_Lean_Parser_detailIdentPart_HasView;
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
x_6 = lean::apply_1(x_5, x_2);
if (lean::obj_tag(x_3) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::dec(x_3);
x_7 = l_Lean_Parser_detailIdent_HasView_x27___elambda__1___closed__1;
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = l_Lean_Parser_detailIdent;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_11 = lean::cnstr_get(x_3, 0);
lean::inc(x_11);
lean::dec(x_3);
x_12 = lean::box(0);
x_13 = l_Lean_Parser_detailIdentSuffix_HasView;
x_14 = lean::cnstr_get(x_13, 1);
lean::inc(x_14);
x_15 = lean::apply_1(x_14, x_11);
x_16 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_12);
x_17 = l_Lean_Parser_noKind;
x_18 = l_Lean_Parser_Syntax_mkNode(x_17, x_16);
x_19 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_12);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_6);
lean::cnstr_set(x_20, 1, x_19);
x_21 = l_Lean_Parser_detailIdent;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
}
}
obj* _init_l_Lean_Parser_detailIdent_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_detailIdentSuffix_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
return x_5;
}
}
obj* _init_l_Lean_Parser_detailIdent_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = l_Lean_Parser_detailIdentPart_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
x_3 = lean::box(3);
x_4 = lean::apply_1(x_2, x_3);
x_5 = l_Lean_Parser_Syntax_asNode___main(x_3);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; 
lean::dec(x_5);
x_6 = l_Lean_Parser_detailIdent_HasView_x27___lambda__1___closed__1;
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_4);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
else
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_5);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_5, 0);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; 
lean::dec(x_10);
lean::free_heap_obj(x_5);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_4);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
else
{
obj* x_13; 
x_13 = lean::cnstr_get(x_10, 1);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
lean::dec(x_13);
x_14 = lean::cnstr_get(x_10, 0);
lean::inc(x_14);
lean::dec(x_10);
x_15 = l_Lean_Parser_detailIdentSuffix_HasView;
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_17 = lean::apply_1(x_16, x_14);
lean::cnstr_set(x_5, 0, x_17);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_4);
lean::cnstr_set(x_18, 1, x_5);
return x_18;
}
else
{
obj* x_19; obj* x_20; 
lean::dec(x_13);
lean::dec(x_10);
lean::free_heap_obj(x_5);
x_19 = l_Lean_Parser_detailIdent_HasView_x27___lambda__1___closed__1;
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_4);
lean::cnstr_set(x_20, 1, x_19);
return x_20;
}
}
}
else
{
obj* x_21; obj* x_22; 
x_21 = lean::cnstr_get(x_5, 0);
lean::inc(x_21);
lean::dec(x_5);
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
lean::dec(x_21);
if (lean::obj_tag(x_22) == 0)
{
obj* x_23; obj* x_24; 
lean::dec(x_22);
x_23 = lean::box(0);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_4);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
else
{
obj* x_25; 
x_25 = lean::cnstr_get(x_22, 1);
lean::inc(x_25);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
lean::dec(x_25);
x_26 = lean::cnstr_get(x_22, 0);
lean::inc(x_26);
lean::dec(x_22);
x_27 = l_Lean_Parser_detailIdentSuffix_HasView;
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
x_29 = lean::apply_1(x_28, x_26);
x_30 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_30, 0, x_29);
x_31 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_31, 0, x_4);
lean::cnstr_set(x_31, 1, x_30);
return x_31;
}
else
{
obj* x_32; obj* x_33; 
lean::dec(x_25);
lean::dec(x_22);
x_32 = l_Lean_Parser_detailIdent_HasView_x27___lambda__1___closed__1;
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_4);
lean::cnstr_set(x_33, 1, x_32);
return x_33;
}
}
}
}
}
}
obj* l_Lean_Parser_detailIdent_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_68; 
x_68 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_68) == 0)
{
obj* x_69; 
lean::dec(x_68);
x_69 = l_Lean_Parser_detailIdent_HasView_x27___lambda__1___closed__2;
return x_69;
}
else
{
obj* x_70; obj* x_71; 
x_70 = lean::cnstr_get(x_68, 0);
lean::inc(x_70);
lean::dec(x_68);
x_71 = lean::cnstr_get(x_70, 1);
lean::inc(x_71);
lean::dec(x_70);
if (lean::obj_tag(x_71) == 0)
{
obj* x_72; 
x_72 = lean::box(3);
x_2 = x_71;
x_3 = x_72;
goto block_67;
}
else
{
obj* x_73; obj* x_74; 
x_73 = lean::cnstr_get(x_71, 0);
lean::inc(x_73);
x_74 = lean::cnstr_get(x_71, 1);
lean::inc(x_74);
lean::dec(x_71);
x_2 = x_74;
x_3 = x_73;
goto block_67;
}
}
block_67:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_detailIdentPart_HasView;
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::apply_1(x_5, x_3);
if (lean::obj_tag(x_2) == 0)
{
obj* x_7; obj* x_8; 
lean::dec(x_2);
x_7 = lean::box(3);
x_8 = l_Lean_Parser_Syntax_asNode___main(x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; 
lean::dec(x_8);
x_9 = l_Lean_Parser_detailIdent_HasView_x27___lambda__1___closed__1;
x_10 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_10, 0, x_6);
lean::cnstr_set(x_10, 1, x_9);
return x_10;
}
else
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_8);
if (x_11 == 0)
{
obj* x_12; obj* x_13; 
x_12 = lean::cnstr_get(x_8, 0);
x_13 = lean::cnstr_get(x_12, 1);
lean::inc(x_13);
lean::dec(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; 
lean::dec(x_13);
lean::free_heap_obj(x_8);
x_14 = lean::box(0);
x_15 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_15, 0, x_6);
lean::cnstr_set(x_15, 1, x_14);
return x_15;
}
else
{
obj* x_16; 
x_16 = lean::cnstr_get(x_13, 1);
lean::inc(x_16);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_16);
x_17 = lean::cnstr_get(x_13, 0);
lean::inc(x_17);
lean::dec(x_13);
x_18 = l_Lean_Parser_detailIdentSuffix_HasView;
x_19 = lean::cnstr_get(x_18, 0);
lean::inc(x_19);
x_20 = lean::apply_1(x_19, x_17);
lean::cnstr_set(x_8, 0, x_20);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_6);
lean::cnstr_set(x_21, 1, x_8);
return x_21;
}
else
{
obj* x_22; obj* x_23; 
lean::dec(x_16);
lean::dec(x_13);
lean::free_heap_obj(x_8);
x_22 = l_Lean_Parser_detailIdent_HasView_x27___lambda__1___closed__1;
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_6);
lean::cnstr_set(x_23, 1, x_22);
return x_23;
}
}
}
else
{
obj* x_24; obj* x_25; 
x_24 = lean::cnstr_get(x_8, 0);
lean::inc(x_24);
lean::dec(x_8);
x_25 = lean::cnstr_get(x_24, 1);
lean::inc(x_25);
lean::dec(x_24);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; 
lean::dec(x_25);
x_26 = lean::box(0);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_6);
lean::cnstr_set(x_27, 1, x_26);
return x_27;
}
else
{
obj* x_28; 
x_28 = lean::cnstr_get(x_25, 1);
lean::inc(x_28);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
lean::dec(x_28);
x_29 = lean::cnstr_get(x_25, 0);
lean::inc(x_29);
lean::dec(x_25);
x_30 = l_Lean_Parser_detailIdentSuffix_HasView;
x_31 = lean::cnstr_get(x_30, 0);
lean::inc(x_31);
x_32 = lean::apply_1(x_31, x_29);
x_33 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_33, 0, x_32);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_6);
lean::cnstr_set(x_34, 1, x_33);
return x_34;
}
else
{
obj* x_35; obj* x_36; 
lean::dec(x_28);
lean::dec(x_25);
x_35 = l_Lean_Parser_detailIdent_HasView_x27___lambda__1___closed__1;
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_6);
lean::cnstr_set(x_36, 1, x_35);
return x_36;
}
}
}
}
}
else
{
obj* x_37; obj* x_38; 
x_37 = lean::cnstr_get(x_2, 0);
lean::inc(x_37);
lean::dec(x_2);
x_38 = l_Lean_Parser_Syntax_asNode___main(x_37);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; obj* x_40; 
lean::dec(x_38);
x_39 = l_Lean_Parser_detailIdent_HasView_x27___lambda__1___closed__1;
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_6);
lean::cnstr_set(x_40, 1, x_39);
return x_40;
}
else
{
uint8 x_41; 
x_41 = !lean::is_exclusive(x_38);
if (x_41 == 0)
{
obj* x_42; obj* x_43; 
x_42 = lean::cnstr_get(x_38, 0);
x_43 = lean::cnstr_get(x_42, 1);
lean::inc(x_43);
lean::dec(x_42);
if (lean::obj_tag(x_43) == 0)
{
obj* x_44; obj* x_45; 
lean::dec(x_43);
lean::free_heap_obj(x_38);
x_44 = lean::box(0);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_6);
lean::cnstr_set(x_45, 1, x_44);
return x_45;
}
else
{
obj* x_46; 
x_46 = lean::cnstr_get(x_43, 1);
lean::inc(x_46);
if (lean::obj_tag(x_46) == 0)
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
lean::dec(x_46);
x_47 = lean::cnstr_get(x_43, 0);
lean::inc(x_47);
lean::dec(x_43);
x_48 = l_Lean_Parser_detailIdentSuffix_HasView;
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_50 = lean::apply_1(x_49, x_47);
lean::cnstr_set(x_38, 0, x_50);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_6);
lean::cnstr_set(x_51, 1, x_38);
return x_51;
}
else
{
obj* x_52; obj* x_53; 
lean::dec(x_46);
lean::dec(x_43);
lean::free_heap_obj(x_38);
x_52 = l_Lean_Parser_detailIdent_HasView_x27___lambda__1___closed__1;
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_6);
lean::cnstr_set(x_53, 1, x_52);
return x_53;
}
}
}
else
{
obj* x_54; obj* x_55; 
x_54 = lean::cnstr_get(x_38, 0);
lean::inc(x_54);
lean::dec(x_38);
x_55 = lean::cnstr_get(x_54, 1);
lean::inc(x_55);
lean::dec(x_54);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; obj* x_57; 
lean::dec(x_55);
x_56 = lean::box(0);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_6);
lean::cnstr_set(x_57, 1, x_56);
return x_57;
}
else
{
obj* x_58; 
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
if (lean::obj_tag(x_58) == 0)
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_58);
x_59 = lean::cnstr_get(x_55, 0);
lean::inc(x_59);
lean::dec(x_55);
x_60 = l_Lean_Parser_detailIdentSuffix_HasView;
x_61 = lean::cnstr_get(x_60, 0);
lean::inc(x_61);
x_62 = lean::apply_1(x_61, x_59);
x_63 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_63, 0, x_62);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_6);
lean::cnstr_set(x_64, 1, x_63);
return x_64;
}
else
{
obj* x_65; obj* x_66; 
lean::dec(x_58);
lean::dec(x_55);
x_65 = l_Lean_Parser_detailIdent_HasView_x27___lambda__1___closed__1;
x_66 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_66, 0, x_6);
lean::cnstr_set(x_66, 1, x_65);
return x_66;
}
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_detailIdent_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdent_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdent_HasView_x27___elambda__1), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_detailIdent_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_detailIdent_HasView_x27;
return x_1;
}
}
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_detailIdent_x27___spec__1(obj* x_1, uint8 x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
if (x_2 == 0)
{
obj* x_53; obj* x_54; obj* x_55; obj* x_94; obj* x_95; 
x_53 = lean::box(0);
lean::inc(x_5);
x_94 = lean::apply_4(x_1, x_3, x_4, x_5, x_6);
x_95 = lean::cnstr_get(x_94, 0);
lean::inc(x_95);
if (lean::obj_tag(x_95) == 0)
{
obj* x_96; 
x_96 = lean::cnstr_get(x_94, 1);
lean::inc(x_96);
lean::dec(x_94);
x_54 = x_95;
x_55 = x_96;
goto block_93;
}
else
{
obj* x_97; obj* x_98; 
x_97 = lean::cnstr_get(x_95, 0);
lean::inc(x_97);
x_98 = lean::cnstr_get(x_97, 3);
lean::inc(x_98);
if (lean::obj_tag(x_98) == 0)
{
obj* x_99; uint8 x_100; 
lean::dec(x_98);
x_99 = lean::cnstr_get(x_94, 1);
lean::inc(x_99);
lean::dec(x_94);
x_100 = !lean::is_exclusive(x_95);
if (x_100 == 0)
{
uint8 x_101; obj* x_102; uint8 x_103; 
x_101 = lean::cnstr_get_scalar<uint8>(x_95, sizeof(void*)*1);
x_102 = lean::cnstr_get(x_95, 0);
lean::dec(x_102);
x_103 = !lean::is_exclusive(x_97);
if (x_103 == 0)
{
obj* x_104; obj* x_105; 
x_104 = lean::cnstr_get(x_97, 3);
lean::dec(x_104);
x_105 = l_Lean_Parser_Combinators_optional___rarg___lambda__1___closed__1;
lean::cnstr_set(x_97, 3, x_105);
if (x_101 == 0)
{
uint8 x_106; 
x_106 = 0;
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_106);
x_54 = x_95;
x_55 = x_99;
goto block_93;
}
else
{
uint8 x_107; 
x_107 = 1;
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_107);
x_54 = x_95;
x_55 = x_99;
goto block_93;
}
}
else
{
obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_108 = lean::cnstr_get(x_97, 0);
x_109 = lean::cnstr_get(x_97, 1);
x_110 = lean::cnstr_get(x_97, 2);
lean::inc(x_110);
lean::inc(x_109);
lean::inc(x_108);
lean::dec(x_97);
x_111 = l_Lean_Parser_Combinators_optional___rarg___lambda__1___closed__1;
x_112 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_112, 0, x_108);
lean::cnstr_set(x_112, 1, x_109);
lean::cnstr_set(x_112, 2, x_110);
lean::cnstr_set(x_112, 3, x_111);
if (x_101 == 0)
{
uint8 x_113; 
x_113 = 0;
lean::cnstr_set(x_95, 0, x_112);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_113);
x_54 = x_95;
x_55 = x_99;
goto block_93;
}
else
{
uint8 x_114; 
x_114 = 1;
lean::cnstr_set(x_95, 0, x_112);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_114);
x_54 = x_95;
x_55 = x_99;
goto block_93;
}
}
}
else
{
uint8 x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; 
x_115 = lean::cnstr_get_scalar<uint8>(x_95, sizeof(void*)*1);
lean::dec(x_95);
x_116 = lean::cnstr_get(x_97, 0);
lean::inc(x_116);
x_117 = lean::cnstr_get(x_97, 1);
lean::inc(x_117);
x_118 = lean::cnstr_get(x_97, 2);
lean::inc(x_118);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_release(x_97, 0);
 lean::cnstr_release(x_97, 1);
 lean::cnstr_release(x_97, 2);
 lean::cnstr_release(x_97, 3);
 x_119 = x_97;
} else {
 lean::dec_ref(x_97);
 x_119 = lean::box(0);
}
x_120 = l_Lean_Parser_Combinators_optional___rarg___lambda__1___closed__1;
if (lean::is_scalar(x_119)) {
 x_121 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_121 = x_119;
}
lean::cnstr_set(x_121, 0, x_116);
lean::cnstr_set(x_121, 1, x_117);
lean::cnstr_set(x_121, 2, x_118);
lean::cnstr_set(x_121, 3, x_120);
if (x_115 == 0)
{
uint8 x_122; obj* x_123; 
x_122 = 0;
x_123 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_123, 0, x_121);
lean::cnstr_set_scalar(x_123, sizeof(void*)*1, x_122);
x_54 = x_123;
x_55 = x_99;
goto block_93;
}
else
{
uint8 x_124; obj* x_125; 
x_124 = 1;
x_125 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_125, 0, x_121);
lean::cnstr_set_scalar(x_125, sizeof(void*)*1, x_124);
x_54 = x_125;
x_55 = x_99;
goto block_93;
}
}
}
else
{
obj* x_126; uint8 x_127; 
x_126 = lean::cnstr_get(x_94, 1);
lean::inc(x_126);
lean::dec(x_94);
x_127 = !lean::is_exclusive(x_95);
if (x_127 == 0)
{
uint8 x_128; obj* x_129; uint8 x_130; 
x_128 = lean::cnstr_get_scalar<uint8>(x_95, sizeof(void*)*1);
x_129 = lean::cnstr_get(x_95, 0);
lean::dec(x_129);
x_130 = !lean::is_exclusive(x_97);
if (x_130 == 0)
{
obj* x_131; uint8 x_132; 
x_131 = lean::cnstr_get(x_97, 3);
lean::dec(x_131);
x_132 = !lean::is_exclusive(x_98);
if (x_132 == 0)
{
obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; 
x_133 = lean::cnstr_get(x_98, 0);
x_134 = lean::box(0);
x_135 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_135, 0, x_133);
lean::cnstr_set(x_135, 1, x_134);
x_136 = l_Lean_Parser_noKind;
x_137 = l_Lean_Parser_Syntax_mkNode(x_136, x_135);
lean::cnstr_set(x_98, 0, x_137);
if (x_128 == 0)
{
uint8 x_138; 
x_138 = 0;
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_138);
x_54 = x_95;
x_55 = x_126;
goto block_93;
}
else
{
uint8 x_139; 
x_139 = 1;
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_139);
x_54 = x_95;
x_55 = x_126;
goto block_93;
}
}
else
{
obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; 
x_140 = lean::cnstr_get(x_98, 0);
lean::inc(x_140);
lean::dec(x_98);
x_141 = lean::box(0);
x_142 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_142, 0, x_140);
lean::cnstr_set(x_142, 1, x_141);
x_143 = l_Lean_Parser_noKind;
x_144 = l_Lean_Parser_Syntax_mkNode(x_143, x_142);
x_145 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_145, 0, x_144);
lean::cnstr_set(x_97, 3, x_145);
if (x_128 == 0)
{
uint8 x_146; 
x_146 = 0;
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_146);
x_54 = x_95;
x_55 = x_126;
goto block_93;
}
else
{
uint8 x_147; 
x_147 = 1;
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_147);
x_54 = x_95;
x_55 = x_126;
goto block_93;
}
}
}
else
{
obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
x_148 = lean::cnstr_get(x_97, 0);
x_149 = lean::cnstr_get(x_97, 1);
x_150 = lean::cnstr_get(x_97, 2);
lean::inc(x_150);
lean::inc(x_149);
lean::inc(x_148);
lean::dec(x_97);
x_151 = lean::cnstr_get(x_98, 0);
lean::inc(x_151);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 x_152 = x_98;
} else {
 lean::dec_ref(x_98);
 x_152 = lean::box(0);
}
x_153 = lean::box(0);
x_154 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_154, 0, x_151);
lean::cnstr_set(x_154, 1, x_153);
x_155 = l_Lean_Parser_noKind;
x_156 = l_Lean_Parser_Syntax_mkNode(x_155, x_154);
if (lean::is_scalar(x_152)) {
 x_157 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_157 = x_152;
}
lean::cnstr_set(x_157, 0, x_156);
x_158 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_158, 0, x_148);
lean::cnstr_set(x_158, 1, x_149);
lean::cnstr_set(x_158, 2, x_150);
lean::cnstr_set(x_158, 3, x_157);
if (x_128 == 0)
{
uint8 x_159; 
x_159 = 0;
lean::cnstr_set(x_95, 0, x_158);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_159);
x_54 = x_95;
x_55 = x_126;
goto block_93;
}
else
{
uint8 x_160; 
x_160 = 1;
lean::cnstr_set(x_95, 0, x_158);
lean::cnstr_set_scalar(x_95, sizeof(void*)*1, x_160);
x_54 = x_95;
x_55 = x_126;
goto block_93;
}
}
}
else
{
uint8 x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; 
x_161 = lean::cnstr_get_scalar<uint8>(x_95, sizeof(void*)*1);
lean::dec(x_95);
x_162 = lean::cnstr_get(x_97, 0);
lean::inc(x_162);
x_163 = lean::cnstr_get(x_97, 1);
lean::inc(x_163);
x_164 = lean::cnstr_get(x_97, 2);
lean::inc(x_164);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_release(x_97, 0);
 lean::cnstr_release(x_97, 1);
 lean::cnstr_release(x_97, 2);
 lean::cnstr_release(x_97, 3);
 x_165 = x_97;
} else {
 lean::dec_ref(x_97);
 x_165 = lean::box(0);
}
x_166 = lean::cnstr_get(x_98, 0);
lean::inc(x_166);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 x_167 = x_98;
} else {
 lean::dec_ref(x_98);
 x_167 = lean::box(0);
}
x_168 = lean::box(0);
x_169 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_169, 0, x_166);
lean::cnstr_set(x_169, 1, x_168);
x_170 = l_Lean_Parser_noKind;
x_171 = l_Lean_Parser_Syntax_mkNode(x_170, x_169);
if (lean::is_scalar(x_167)) {
 x_172 = lean::alloc_cnstr(1, 1, 0);
} else {
 x_172 = x_167;
}
lean::cnstr_set(x_172, 0, x_171);
if (lean::is_scalar(x_165)) {
 x_173 = lean::alloc_cnstr(0, 4, 0);
} else {
 x_173 = x_165;
}
lean::cnstr_set(x_173, 0, x_162);
lean::cnstr_set(x_173, 1, x_163);
lean::cnstr_set(x_173, 2, x_164);
lean::cnstr_set(x_173, 3, x_172);
if (x_161 == 0)
{
uint8 x_174; obj* x_175; 
x_174 = 0;
x_175 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_175, 0, x_173);
lean::cnstr_set_scalar(x_175, sizeof(void*)*1, x_174);
x_54 = x_175;
x_55 = x_126;
goto block_93;
}
else
{
uint8 x_176; obj* x_177; 
x_176 = 1;
x_177 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_177, 0, x_173);
lean::cnstr_set_scalar(x_177, sizeof(void*)*1, x_176);
x_54 = x_177;
x_55 = x_126;
goto block_93;
}
}
}
}
block_93:
{
if (lean::obj_tag(x_54) == 0)
{
uint8 x_56; 
x_56 = !lean::is_exclusive(x_54);
if (x_56 == 0)
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_57 = lean::cnstr_get(x_54, 0);
x_58 = lean::cnstr_get(x_54, 2);
x_59 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_59, 0, x_57);
x_60 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_54, 2, x_60);
lean::cnstr_set(x_54, 0, x_59);
x_61 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_54);
if (lean::obj_tag(x_61) == 0)
{
lean::dec(x_5);
x_7 = x_61;
x_8 = x_55;
goto block_52;
}
else
{
uint8 x_62; 
x_62 = lean::cnstr_get_scalar<uint8>(x_61, sizeof(void*)*1);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_63 = lean::cnstr_get(x_61, 0);
lean::inc(x_63);
lean::dec(x_61);
x_64 = lean::cnstr_get(x_63, 2);
lean::inc(x_64);
lean::dec(x_63);
x_65 = l_mjoin___rarg___closed__1;
x_66 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_66, 0, x_64);
lean::closure_set(x_66, 1, x_65);
x_67 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_67, 0, x_66);
x_68 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_68, 0, x_53);
lean::cnstr_set(x_68, 1, x_5);
lean::cnstr_set(x_68, 2, x_67);
x_7 = x_68;
x_8 = x_55;
goto block_52;
}
else
{
lean::dec(x_5);
x_7 = x_61;
x_8 = x_55;
goto block_52;
}
}
}
else
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_69 = lean::cnstr_get(x_54, 0);
x_70 = lean::cnstr_get(x_54, 1);
x_71 = lean::cnstr_get(x_54, 2);
lean::inc(x_71);
lean::inc(x_70);
lean::inc(x_69);
lean::dec(x_54);
x_72 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_72, 0, x_69);
x_73 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_74 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_74, 0, x_72);
lean::cnstr_set(x_74, 1, x_70);
lean::cnstr_set(x_74, 2, x_73);
x_75 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_71, x_74);
if (lean::obj_tag(x_75) == 0)
{
lean::dec(x_5);
x_7 = x_75;
x_8 = x_55;
goto block_52;
}
else
{
uint8 x_76; 
x_76 = lean::cnstr_get_scalar<uint8>(x_75, sizeof(void*)*1);
if (x_76 == 0)
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; 
x_77 = lean::cnstr_get(x_75, 0);
lean::inc(x_77);
lean::dec(x_75);
x_78 = lean::cnstr_get(x_77, 2);
lean::inc(x_78);
lean::dec(x_77);
x_79 = l_mjoin___rarg___closed__1;
x_80 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_80, 0, x_78);
lean::closure_set(x_80, 1, x_79);
x_81 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_81, 0, x_80);
x_82 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_82, 0, x_53);
lean::cnstr_set(x_82, 1, x_5);
lean::cnstr_set(x_82, 2, x_81);
x_7 = x_82;
x_8 = x_55;
goto block_52;
}
else
{
lean::dec(x_5);
x_7 = x_75;
x_8 = x_55;
goto block_52;
}
}
}
}
else
{
uint8 x_83; 
x_83 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*1);
if (x_83 == 0)
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
x_84 = lean::cnstr_get(x_54, 0);
lean::inc(x_84);
lean::dec(x_54);
x_85 = lean::cnstr_get(x_84, 2);
lean::inc(x_85);
lean::dec(x_84);
x_86 = l_mjoin___rarg___closed__1;
x_87 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_87, 0, x_85);
lean::closure_set(x_87, 1, x_86);
x_88 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_88, 0, x_87);
x_89 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_89, 0, x_53);
lean::cnstr_set(x_89, 1, x_5);
lean::cnstr_set(x_89, 2, x_88);
x_7 = x_89;
x_8 = x_55;
goto block_52;
}
else
{
uint8 x_90; 
lean::dec(x_5);
x_90 = !lean::is_exclusive(x_54);
if (x_90 == 0)
{
x_7 = x_54;
x_8 = x_55;
goto block_52;
}
else
{
obj* x_91; obj* x_92; 
x_91 = lean::cnstr_get(x_54, 0);
lean::inc(x_91);
lean::dec(x_54);
x_92 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set_scalar(x_92, sizeof(void*)*1, x_83);
x_7 = x_92;
x_8 = x_55;
goto block_52;
}
}
}
}
}
else
{
obj* x_178; 
x_178 = lean::apply_4(x_1, x_3, x_4, x_5, x_6);
return x_178;
}
block_52:
{
if (lean::obj_tag(x_7) == 0)
{
obj* x_9; 
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
lean::dec(x_9);
x_10 = !lean::is_exclusive(x_7);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_11 = lean::cnstr_get(x_7, 2);
x_12 = lean::cnstr_get(x_7, 0);
lean::dec(x_12);
x_13 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_14 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_7, 2, x_14);
lean::cnstr_set(x_7, 0, x_13);
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_7);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_8);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_17 = lean::cnstr_get(x_7, 1);
x_18 = lean::cnstr_get(x_7, 2);
lean::inc(x_18);
lean::inc(x_17);
lean::dec(x_7);
x_19 = l_Lean_Parser_Combinators_many___rarg___closed__1;
x_20 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_21 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_21, 0, x_19);
lean::cnstr_set(x_21, 1, x_17);
lean::cnstr_set(x_21, 2, x_20);
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_8);
return x_23;
}
}
else
{
uint8 x_24; 
x_24 = !lean::is_exclusive(x_7);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_25 = lean::cnstr_get(x_7, 2);
x_26 = lean::cnstr_get(x_7, 0);
lean::dec(x_26);
x_27 = lean::cnstr_get(x_9, 0);
lean::inc(x_27);
lean::dec(x_9);
x_28 = lean::box(0);
x_29 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set(x_29, 1, x_28);
x_30 = l_Lean_Parser_noKind;
x_31 = l_Lean_Parser_Syntax_mkNode(x_30, x_29);
x_32 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_7, 2, x_32);
lean::cnstr_set(x_7, 0, x_31);
x_33 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_25, x_7);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_8);
return x_34;
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_35 = lean::cnstr_get(x_7, 1);
x_36 = lean::cnstr_get(x_7, 2);
lean::inc(x_36);
lean::inc(x_35);
lean::dec(x_7);
x_37 = lean::cnstr_get(x_9, 0);
lean::inc(x_37);
lean::dec(x_9);
x_38 = lean::box(0);
x_39 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_39, 0, x_37);
lean::cnstr_set(x_39, 1, x_38);
x_40 = l_Lean_Parser_noKind;
x_41 = l_Lean_Parser_Syntax_mkNode(x_40, x_39);
x_42 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_43 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_35);
lean::cnstr_set(x_43, 2, x_42);
x_44 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_36, x_43);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_8);
return x_45;
}
}
}
else
{
uint8 x_46; 
x_46 = !lean::is_exclusive(x_7);
if (x_46 == 0)
{
obj* x_47; 
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_7);
lean::cnstr_set(x_47, 1, x_8);
return x_47;
}
else
{
obj* x_48; uint8 x_49; obj* x_50; obj* x_51; 
x_48 = lean::cnstr_get(x_7, 0);
x_49 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
lean::inc(x_48);
lean::dec(x_7);
x_50 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_50, 0, x_48);
lean::cnstr_set_scalar(x_50, sizeof(void*)*1, x_49);
x_51 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_51, 0, x_50);
lean::cnstr_set(x_51, 1, x_8);
return x_51;
}
}
}
}
}
obj* _init_l_Lean_Parser_detailIdent_x27___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; uint8 x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentPart_Parser), 3, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__4___rarg___boxed), 5, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdentSuffix_Parser), 4, 0);
x_4 = 0;
x_5 = lean::box(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_optional___at_Lean_Parser_detailIdent_x27___spec__1___boxed), 6, 2);
lean::closure_set(x_6, 0, x_3);
lean::closure_set(x_6, 1, x_5);
x_7 = lean::box(0);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_7);
x_9 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_9, 0, x_2);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
obj* l_Lean_Parser_detailIdent_x27(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_Lean_Parser_detailIdent;
x_6 = l_Lean_Parser_detailIdent_x27___closed__1;
x_7 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentSuffix_Parser_Lean_Parser_HasTokens___spec__8(x_5, x_6, x_1, x_2, x_3, x_4);
return x_7;
}
}
obj* l_Lean_Parser_Combinators_optional___at_Lean_Parser_detailIdent_x27___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint8 x_7; obj* x_8; 
x_7 = lean::unbox(x_2);
lean::dec(x_2);
x_8 = l_Lean_Parser_Combinators_optional___at_Lean_Parser_detailIdent_x27___spec__1(x_1, x_7, x_3, x_4, x_5, x_6);
return x_8;
}
}
obj* l_Lean_Parser_detailIdent_Parser___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::box(0);
x_6 = l_Lean_Parser_RecT_runParsec___rarg___lambda__1___closed__1;
x_7 = l_mjoin___rarg___closed__1;
x_8 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_6, x_7, x_5, x_5, x_2, x_3, x_4);
return x_8;
}
}
obj* l_Lean_Parser_detailIdent_Parser___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_detailIdent_x27(x_1, x_3, x_4, x_5);
return x_6;
}
}
obj* _init_l_Lean_Parser_detailIdent_Parser___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdent_Parser___lambda__1___boxed), 4, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_detailIdent_Parser___lambda__2___boxed), 5, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_fixCore___rarg___boxed), 3, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_detailIdent_Parser(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Parser_detailIdent_Parser___closed__1;
x_5 = l_Lean_Parser_detailIdent_x27(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_Lean_Parser_detailIdent_Parser___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_detailIdent_Parser___lambda__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_detailIdent_Parser___lambda__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_detailIdent_Parser___lambda__2(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_curr___at___private_init_lean_parser_token_4__ident_x27___spec__2___rarg(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = l_String_OldIterator_curr___main(x_1);
x_4 = l_Lean_Parser_finishCommentBlock___closed__2;
x_5 = lean::box_uint32(x_3);
x_6 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_4);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_curr___at___private_init_lean_parser_token_4__ident_x27___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_curr___at___private_init_lean_parser_token_4__ident_x27___spec__2___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x27___spec__4(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_String_OldIterator_remaining___main(x_3);
x_6 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__7(x_5, x_1, x_3);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_4);
return x_7;
}
}
obj* l_Lean_Parser_idPartDefault___at___private_init_lean_parser_token_4__ident_x27___spec__3(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_String_OldIterator_hasNext___main(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_5 = lean::box(0);
x_6 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_7 = l_mjoin___rarg___closed__1;
x_8 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_6, x_7, x_5, x_5, x_1, x_2, x_3);
x_9 = !lean::is_exclusive(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_8, 0);
x_11 = lean::cnstr_get(x_8, 1);
x_12 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_13 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_10);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint32 x_18; obj* x_19; obj* x_20; uint8 x_21; 
lean::free_heap_obj(x_8);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_13, 1);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_13, 2);
lean::inc(x_16);
lean::dec(x_13);
x_17 = l_String_splitAux___main___closed__1;
x_18 = lean::unbox_uint32(x_14);
lean::dec(x_14);
x_19 = lean::string_push(x_17, x_18);
x_20 = l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x27___spec__4(x_19, x_1, x_15, x_11);
x_21 = !lean::is_exclusive(x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_23; 
x_22 = lean::cnstr_get(x_20, 0);
x_23 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_22);
lean::cnstr_set(x_20, 0, x_23);
return x_20;
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_24 = lean::cnstr_get(x_20, 0);
x_25 = lean::cnstr_get(x_20, 1);
lean::inc(x_25);
lean::inc(x_24);
lean::dec(x_20);
x_26 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_24);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8 x_28; 
x_28 = !lean::is_exclusive(x_13);
if (x_28 == 0)
{
lean::cnstr_set(x_8, 0, x_13);
return x_8;
}
else
{
obj* x_29; uint8 x_30; obj* x_31; 
x_29 = lean::cnstr_get(x_13, 0);
x_30 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
lean::inc(x_29);
lean::dec(x_13);
x_31 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set_scalar(x_31, sizeof(void*)*1, x_30);
lean::cnstr_set(x_8, 0, x_31);
return x_8;
}
}
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_32 = lean::cnstr_get(x_8, 0);
x_33 = lean::cnstr_get(x_8, 1);
lean::inc(x_33);
lean::inc(x_32);
lean::dec(x_8);
x_34 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_34, x_32);
if (lean::obj_tag(x_35) == 0)
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; uint32 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_35, 1);
lean::inc(x_37);
x_38 = lean::cnstr_get(x_35, 2);
lean::inc(x_38);
lean::dec(x_35);
x_39 = l_String_splitAux___main___closed__1;
x_40 = lean::unbox_uint32(x_36);
lean::dec(x_36);
x_41 = lean::string_push(x_39, x_40);
x_42 = l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x27___spec__4(x_41, x_1, x_37, x_33);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_42, 1);
lean::inc(x_44);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 lean::cnstr_release(x_42, 1);
 x_45 = x_42;
} else {
 lean::dec_ref(x_42);
 x_45 = lean::box(0);
}
x_46 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_43);
if (lean::is_scalar(x_45)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_45;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_44);
return x_47;
}
else
{
obj* x_48; uint8 x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::cnstr_get(x_35, 0);
lean::inc(x_48);
x_49 = lean::cnstr_get_scalar<uint8>(x_35, sizeof(void*)*1);
if (lean::is_exclusive(x_35)) {
 lean::cnstr_release(x_35, 0);
 x_50 = x_35;
} else {
 lean::dec_ref(x_35);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_48);
lean::cnstr_set_scalar(x_51, sizeof(void*)*1, x_49);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_33);
return x_52;
}
}
}
else
{
uint32 x_53; uint8 x_54; 
x_53 = l_String_OldIterator_curr___main(x_2);
x_54 = l_Lean_isIdFirst(x_53);
if (x_54 == 0)
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; uint8 x_62; 
x_55 = l_Char_quoteCore(x_53);
x_56 = l_Char_HasRepr___closed__1;
x_57 = lean::string_append(x_56, x_55);
lean::dec(x_55);
x_58 = lean::string_append(x_57, x_56);
x_59 = lean::box(0);
x_60 = l_mjoin___rarg___closed__1;
x_61 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_58, x_60, x_59, x_59, x_1, x_2, x_3);
x_62 = !lean::is_exclusive(x_61);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_63 = lean::cnstr_get(x_61, 0);
x_64 = lean::cnstr_get(x_61, 1);
x_65 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_66 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_65, x_63);
if (lean::obj_tag(x_66) == 0)
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; uint32 x_71; obj* x_72; obj* x_73; uint8 x_74; 
lean::free_heap_obj(x_61);
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
x_68 = lean::cnstr_get(x_66, 1);
lean::inc(x_68);
x_69 = lean::cnstr_get(x_66, 2);
lean::inc(x_69);
lean::dec(x_66);
x_70 = l_String_splitAux___main___closed__1;
x_71 = lean::unbox_uint32(x_67);
lean::dec(x_67);
x_72 = lean::string_push(x_70, x_71);
x_73 = l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x27___spec__4(x_72, x_1, x_68, x_64);
x_74 = !lean::is_exclusive(x_73);
if (x_74 == 0)
{
obj* x_75; obj* x_76; 
x_75 = lean::cnstr_get(x_73, 0);
x_76 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_69, x_75);
lean::cnstr_set(x_73, 0, x_76);
return x_73;
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_77 = lean::cnstr_get(x_73, 0);
x_78 = lean::cnstr_get(x_73, 1);
lean::inc(x_78);
lean::inc(x_77);
lean::dec(x_73);
x_79 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_69, x_77);
x_80 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_78);
return x_80;
}
}
else
{
uint8 x_81; 
x_81 = !lean::is_exclusive(x_66);
if (x_81 == 0)
{
lean::cnstr_set(x_61, 0, x_66);
return x_61;
}
else
{
obj* x_82; uint8 x_83; obj* x_84; 
x_82 = lean::cnstr_get(x_66, 0);
x_83 = lean::cnstr_get_scalar<uint8>(x_66, sizeof(void*)*1);
lean::inc(x_82);
lean::dec(x_66);
x_84 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_84, 0, x_82);
lean::cnstr_set_scalar(x_84, sizeof(void*)*1, x_83);
lean::cnstr_set(x_61, 0, x_84);
return x_61;
}
}
}
else
{
obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_85 = lean::cnstr_get(x_61, 0);
x_86 = lean::cnstr_get(x_61, 1);
lean::inc(x_86);
lean::inc(x_85);
lean::dec(x_61);
x_87 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_88 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_87, x_85);
if (lean::obj_tag(x_88) == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; uint32 x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_89 = lean::cnstr_get(x_88, 0);
lean::inc(x_89);
x_90 = lean::cnstr_get(x_88, 1);
lean::inc(x_90);
x_91 = lean::cnstr_get(x_88, 2);
lean::inc(x_91);
lean::dec(x_88);
x_92 = l_String_splitAux___main___closed__1;
x_93 = lean::unbox_uint32(x_89);
lean::dec(x_89);
x_94 = lean::string_push(x_92, x_93);
x_95 = l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x27___spec__4(x_94, x_1, x_90, x_86);
x_96 = lean::cnstr_get(x_95, 0);
lean::inc(x_96);
x_97 = lean::cnstr_get(x_95, 1);
lean::inc(x_97);
if (lean::is_exclusive(x_95)) {
 lean::cnstr_release(x_95, 0);
 lean::cnstr_release(x_95, 1);
 x_98 = x_95;
} else {
 lean::dec_ref(x_95);
 x_98 = lean::box(0);
}
x_99 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_91, x_96);
if (lean::is_scalar(x_98)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_98;
}
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_97);
return x_100;
}
else
{
obj* x_101; uint8 x_102; obj* x_103; obj* x_104; obj* x_105; 
x_101 = lean::cnstr_get(x_88, 0);
lean::inc(x_101);
x_102 = lean::cnstr_get_scalar<uint8>(x_88, sizeof(void*)*1);
if (lean::is_exclusive(x_88)) {
 lean::cnstr_release(x_88, 0);
 x_103 = x_88;
} else {
 lean::dec_ref(x_88);
 x_103 = lean::box(0);
}
if (lean::is_scalar(x_103)) {
 x_104 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_104 = x_103;
}
lean::cnstr_set(x_104, 0, x_101);
lean::cnstr_set_scalar(x_104, sizeof(void*)*1, x_102);
x_105 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_86);
return x_105;
}
}
}
else
{
obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; uint8 x_111; 
x_106 = l_String_OldIterator_next___main(x_2);
x_107 = lean::box(0);
x_108 = l_String_splitAux___main___closed__1;
x_109 = lean::string_push(x_108, x_53);
x_110 = l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x27___spec__4(x_109, x_1, x_106, x_3);
x_111 = !lean::is_exclusive(x_110);
if (x_111 == 0)
{
obj* x_112; obj* x_113; 
x_112 = lean::cnstr_get(x_110, 0);
x_113 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_107, x_112);
lean::cnstr_set(x_110, 0, x_113);
return x_110;
}
else
{
obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
x_114 = lean::cnstr_get(x_110, 0);
x_115 = lean::cnstr_get(x_110, 1);
lean::inc(x_115);
lean::inc(x_114);
lean::dec(x_110);
x_116 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_107, x_114);
x_117 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_117, 0, x_116);
lean::cnstr_set(x_117, 1, x_115);
return x_117;
}
}
}
}
}
obj* l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6(uint32 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint8 x_5; 
x_5 = l_String_OldIterator_hasNext___main(x_3);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint8 x_10; 
x_6 = lean::box(0);
x_7 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_8 = l_mjoin___rarg___closed__1;
x_9 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_7, x_8, x_6, x_6, x_2, x_3, x_4);
x_10 = !lean::is_exclusive(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; 
x_11 = lean::cnstr_get(x_9, 0);
x_12 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_13 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_11);
lean::cnstr_set(x_9, 0, x_13);
return x_9;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_9, 0);
x_15 = lean::cnstr_get(x_9, 1);
lean::inc(x_15);
lean::inc(x_14);
lean::dec(x_9);
x_16 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_17 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_14);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_15);
return x_18;
}
}
else
{
uint32 x_19; uint8 x_20; 
x_19 = l_String_OldIterator_curr___main(x_3);
x_20 = x_19 == x_1;
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; uint8 x_28; 
x_21 = l_Char_quoteCore(x_19);
x_22 = l_Char_HasRepr___closed__1;
x_23 = lean::string_append(x_22, x_21);
lean::dec(x_21);
x_24 = lean::string_append(x_23, x_22);
x_25 = lean::box(0);
x_26 = l_mjoin___rarg___closed__1;
x_27 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_24, x_26, x_25, x_25, x_2, x_3, x_4);
x_28 = !lean::is_exclusive(x_27);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = lean::cnstr_get(x_27, 0);
x_30 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_31 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_30, x_29);
lean::cnstr_set(x_27, 0, x_31);
return x_27;
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_32 = lean::cnstr_get(x_27, 0);
x_33 = lean::cnstr_get(x_27, 1);
lean::inc(x_33);
lean::inc(x_32);
lean::dec(x_27);
x_34 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_34, x_32);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_33);
return x_36;
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_37 = l_String_OldIterator_next___main(x_3);
x_38 = lean::box(0);
x_39 = lean::box_uint32(x_19);
x_40 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_37);
lean::cnstr_set(x_40, 2, x_38);
x_41 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_41, 0, x_40);
lean::cnstr_set(x_41, 1, x_4);
return x_41;
}
}
}
}
obj* l_Lean_Parser_idPartEscaped___at___private_init_lean_parser_token_4__ident_x27___spec__5(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_idBeginEscape;
x_5 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6(x_4, x_1, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_7 = lean::cnstr_get(x_5, 1);
lean::inc(x_7);
lean::dec(x_5);
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_6, 2);
lean::inc(x_9);
lean::dec(x_6);
x_10 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__1(x_1, x_8, x_7);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; uint32 x_16; obj* x_17; obj* x_18; 
x_12 = lean::cnstr_get(x_10, 1);
lean::inc(x_12);
lean::dec(x_10);
x_13 = lean::cnstr_get(x_11, 0);
lean::inc(x_13);
x_14 = lean::cnstr_get(x_11, 1);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_11, 2);
lean::inc(x_15);
lean::dec(x_11);
x_16 = l_Lean_idEndEscape;
x_17 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6(x_16, x_1, x_14, x_12);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
if (lean::obj_tag(x_18) == 0)
{
uint8 x_19; 
x_19 = !lean::is_exclusive(x_17);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = lean::cnstr_get(x_17, 0);
lean::dec(x_20);
x_21 = !lean::is_exclusive(x_18);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_22 = lean::cnstr_get(x_18, 2);
x_23 = lean::cnstr_get(x_18, 0);
lean::dec(x_23);
x_24 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_18, 2, x_24);
lean::cnstr_set(x_18, 0, x_13);
x_25 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_18);
x_26 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_25);
x_27 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_26);
lean::cnstr_set(x_17, 0, x_27);
return x_17;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_28 = lean::cnstr_get(x_18, 1);
x_29 = lean::cnstr_get(x_18, 2);
lean::inc(x_29);
lean::inc(x_28);
lean::dec(x_18);
x_30 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_31 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_31, 0, x_13);
lean::cnstr_set(x_31, 1, x_28);
lean::cnstr_set(x_31, 2, x_30);
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_29, x_31);
x_33 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_32);
x_34 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_33);
lean::cnstr_set(x_17, 0, x_34);
return x_17;
}
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_35 = lean::cnstr_get(x_17, 1);
lean::inc(x_35);
lean::dec(x_17);
x_36 = lean::cnstr_get(x_18, 1);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_18, 2);
lean::inc(x_37);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_release(x_18, 0);
 lean::cnstr_release(x_18, 1);
 lean::cnstr_release(x_18, 2);
 x_38 = x_18;
} else {
 lean::dec_ref(x_18);
 x_38 = lean::box(0);
}
x_39 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_38)) {
 x_40 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_40 = x_38;
}
lean::cnstr_set(x_40, 0, x_13);
lean::cnstr_set(x_40, 1, x_36);
lean::cnstr_set(x_40, 2, x_39);
x_41 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_37, x_40);
x_42 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_41);
x_43 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_42);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_35);
return x_44;
}
}
else
{
uint8 x_45; 
lean::dec(x_13);
x_45 = !lean::is_exclusive(x_17);
if (x_45 == 0)
{
obj* x_46; uint8 x_47; 
x_46 = lean::cnstr_get(x_17, 0);
lean::dec(x_46);
x_47 = !lean::is_exclusive(x_18);
if (x_47 == 0)
{
obj* x_48; obj* x_49; 
x_48 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_18);
x_49 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_48);
lean::cnstr_set(x_17, 0, x_49);
return x_17;
}
else
{
obj* x_50; uint8 x_51; obj* x_52; obj* x_53; obj* x_54; 
x_50 = lean::cnstr_get(x_18, 0);
x_51 = lean::cnstr_get_scalar<uint8>(x_18, sizeof(void*)*1);
lean::inc(x_50);
lean::dec(x_18);
x_52 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_52, 0, x_50);
lean::cnstr_set_scalar(x_52, sizeof(void*)*1, x_51);
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_52);
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_53);
lean::cnstr_set(x_17, 0, x_54);
return x_17;
}
}
else
{
obj* x_55; obj* x_56; uint8 x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_55 = lean::cnstr_get(x_17, 1);
lean::inc(x_55);
lean::dec(x_17);
x_56 = lean::cnstr_get(x_18, 0);
lean::inc(x_56);
x_57 = lean::cnstr_get_scalar<uint8>(x_18, sizeof(void*)*1);
if (lean::is_exclusive(x_18)) {
 lean::cnstr_release(x_18, 0);
 x_58 = x_18;
} else {
 lean::dec_ref(x_18);
 x_58 = lean::box(0);
}
if (lean::is_scalar(x_58)) {
 x_59 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_59 = x_58;
}
lean::cnstr_set(x_59, 0, x_56);
lean::cnstr_set_scalar(x_59, sizeof(void*)*1, x_57);
x_60 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_59);
x_61 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_60);
x_62 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_62, 0, x_61);
lean::cnstr_set(x_62, 1, x_55);
return x_62;
}
}
}
else
{
uint8 x_63; 
x_63 = !lean::is_exclusive(x_10);
if (x_63 == 0)
{
obj* x_64; uint8 x_65; 
x_64 = lean::cnstr_get(x_10, 0);
lean::dec(x_64);
x_65 = !lean::is_exclusive(x_11);
if (x_65 == 0)
{
obj* x_66; 
x_66 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_11);
lean::cnstr_set(x_10, 0, x_66);
return x_10;
}
else
{
obj* x_67; uint8 x_68; obj* x_69; obj* x_70; 
x_67 = lean::cnstr_get(x_11, 0);
x_68 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
lean::inc(x_67);
lean::dec(x_11);
x_69 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_69, 0, x_67);
lean::cnstr_set_scalar(x_69, sizeof(void*)*1, x_68);
x_70 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_69);
lean::cnstr_set(x_10, 0, x_70);
return x_10;
}
}
else
{
obj* x_71; obj* x_72; uint8 x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_71 = lean::cnstr_get(x_10, 1);
lean::inc(x_71);
lean::dec(x_10);
x_72 = lean::cnstr_get(x_11, 0);
lean::inc(x_72);
x_73 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_74 = x_11;
} else {
 lean::dec_ref(x_11);
 x_74 = lean::box(0);
}
if (lean::is_scalar(x_74)) {
 x_75 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_75 = x_74;
}
lean::cnstr_set(x_75, 0, x_72);
lean::cnstr_set_scalar(x_75, sizeof(void*)*1, x_73);
x_76 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_75);
x_77 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_71);
return x_77;
}
}
}
else
{
uint8 x_78; 
x_78 = !lean::is_exclusive(x_5);
if (x_78 == 0)
{
obj* x_79; uint8 x_80; 
x_79 = lean::cnstr_get(x_5, 0);
lean::dec(x_79);
x_80 = !lean::is_exclusive(x_6);
if (x_80 == 0)
{
return x_5;
}
else
{
obj* x_81; uint8 x_82; obj* x_83; 
x_81 = lean::cnstr_get(x_6, 0);
x_82 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
lean::inc(x_81);
lean::dec(x_6);
x_83 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_83, 0, x_81);
lean::cnstr_set_scalar(x_83, sizeof(void*)*1, x_82);
lean::cnstr_set(x_5, 0, x_83);
return x_5;
}
}
else
{
obj* x_84; obj* x_85; uint8 x_86; obj* x_87; obj* x_88; obj* x_89; 
x_84 = lean::cnstr_get(x_5, 1);
lean::inc(x_84);
lean::dec(x_5);
x_85 = lean::cnstr_get(x_6, 0);
lean::inc(x_85);
x_86 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_87 = x_6;
} else {
 lean::dec_ref(x_6);
 x_87 = lean::box(0);
}
if (lean::is_scalar(x_87)) {
 x_88 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_88 = x_87;
}
lean::cnstr_set(x_88, 0, x_85);
lean::cnstr_set_scalar(x_88, sizeof(void*)*1, x_86);
x_89 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_84);
return x_89;
}
}
}
}
obj* l_Lean_Parser_idPart___at___private_init_lean_parser_token_4__ident_x27___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Parser_MonadParsec_curr___at___private_init_lean_parser_token_4__ident_x27___spec__2___rarg(x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_4);
if (x_6 == 0)
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::cnstr_get(x_4, 1);
x_8 = lean::cnstr_get(x_4, 0);
lean::dec(x_8);
x_9 = !lean::is_exclusive(x_5);
if (x_9 == 0)
{
obj* x_10; obj* x_11; uint32 x_12; uint8 x_13; obj* x_14; obj* x_15; obj* x_16; 
x_10 = lean::cnstr_get(x_5, 0);
x_11 = lean::cnstr_get(x_5, 2);
x_12 = lean::unbox_uint32(x_10);
lean::dec(x_10);
x_13 = l_Lean_isIdBeginEscape(x_12);
x_14 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_15 = lean::box(x_13);
lean::cnstr_set(x_5, 2, x_14);
lean::cnstr_set(x_5, 0, x_15);
x_16 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_5);
if (lean::obj_tag(x_16) == 0)
{
obj* x_17; uint8 x_18; 
lean::free_heap_obj(x_4);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
x_18 = lean::unbox(x_17);
lean::dec(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; uint8 x_22; 
x_19 = lean::cnstr_get(x_16, 1);
lean::inc(x_19);
x_20 = lean::cnstr_get(x_16, 2);
lean::inc(x_20);
lean::dec(x_16);
x_21 = l_Lean_Parser_idPartDefault___at___private_init_lean_parser_token_4__ident_x27___spec__3(x_1, x_19, x_7);
x_22 = !lean::is_exclusive(x_21);
if (x_22 == 0)
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_21, 0);
x_24 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_20, x_23);
lean::cnstr_set(x_21, 0, x_24);
return x_21;
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_25 = lean::cnstr_get(x_21, 0);
x_26 = lean::cnstr_get(x_21, 1);
lean::inc(x_26);
lean::inc(x_25);
lean::dec(x_21);
x_27 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_20, x_25);
x_28 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_28, 1, x_26);
return x_28;
}
}
else
{
obj* x_29; obj* x_30; obj* x_31; uint8 x_32; 
x_29 = lean::cnstr_get(x_16, 1);
lean::inc(x_29);
x_30 = lean::cnstr_get(x_16, 2);
lean::inc(x_30);
lean::dec(x_16);
x_31 = l_Lean_Parser_idPartEscaped___at___private_init_lean_parser_token_4__ident_x27___spec__5(x_1, x_29, x_7);
x_32 = !lean::is_exclusive(x_31);
if (x_32 == 0)
{
obj* x_33; obj* x_34; 
x_33 = lean::cnstr_get(x_31, 0);
x_34 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_30, x_33);
lean::cnstr_set(x_31, 0, x_34);
return x_31;
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_35 = lean::cnstr_get(x_31, 0);
x_36 = lean::cnstr_get(x_31, 1);
lean::inc(x_36);
lean::inc(x_35);
lean::dec(x_31);
x_37 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_30, x_35);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_36);
return x_38;
}
}
}
else
{
uint8 x_39; 
x_39 = !lean::is_exclusive(x_16);
if (x_39 == 0)
{
lean::cnstr_set(x_4, 0, x_16);
return x_4;
}
else
{
obj* x_40; uint8 x_41; obj* x_42; 
x_40 = lean::cnstr_get(x_16, 0);
x_41 = lean::cnstr_get_scalar<uint8>(x_16, sizeof(void*)*1);
lean::inc(x_40);
lean::dec(x_16);
x_42 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_42, 0, x_40);
lean::cnstr_set_scalar(x_42, sizeof(void*)*1, x_41);
lean::cnstr_set(x_4, 0, x_42);
return x_4;
}
}
}
else
{
obj* x_43; obj* x_44; obj* x_45; uint32 x_46; uint8 x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_43 = lean::cnstr_get(x_5, 0);
x_44 = lean::cnstr_get(x_5, 1);
x_45 = lean::cnstr_get(x_5, 2);
lean::inc(x_45);
lean::inc(x_44);
lean::inc(x_43);
lean::dec(x_5);
x_46 = lean::unbox_uint32(x_43);
lean::dec(x_43);
x_47 = l_Lean_isIdBeginEscape(x_46);
x_48 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_49 = lean::box(x_47);
x_50 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_44);
lean::cnstr_set(x_50, 2, x_48);
x_51 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_45, x_50);
if (lean::obj_tag(x_51) == 0)
{
obj* x_52; uint8 x_53; 
lean::free_heap_obj(x_4);
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
x_53 = lean::unbox(x_52);
lean::dec(x_52);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_54 = lean::cnstr_get(x_51, 1);
lean::inc(x_54);
x_55 = lean::cnstr_get(x_51, 2);
lean::inc(x_55);
lean::dec(x_51);
x_56 = l_Lean_Parser_idPartDefault___at___private_init_lean_parser_token_4__ident_x27___spec__3(x_1, x_54, x_7);
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_58 = lean::cnstr_get(x_56, 1);
lean::inc(x_58);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 lean::cnstr_release(x_56, 1);
 x_59 = x_56;
} else {
 lean::dec_ref(x_56);
 x_59 = lean::box(0);
}
x_60 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_55, x_57);
if (lean::is_scalar(x_59)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_59;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_58);
return x_61;
}
else
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_62 = lean::cnstr_get(x_51, 1);
lean::inc(x_62);
x_63 = lean::cnstr_get(x_51, 2);
lean::inc(x_63);
lean::dec(x_51);
x_64 = l_Lean_Parser_idPartEscaped___at___private_init_lean_parser_token_4__ident_x27___spec__5(x_1, x_62, x_7);
x_65 = lean::cnstr_get(x_64, 0);
lean::inc(x_65);
x_66 = lean::cnstr_get(x_64, 1);
lean::inc(x_66);
if (lean::is_exclusive(x_64)) {
 lean::cnstr_release(x_64, 0);
 lean::cnstr_release(x_64, 1);
 x_67 = x_64;
} else {
 lean::dec_ref(x_64);
 x_67 = lean::box(0);
}
x_68 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_63, x_65);
if (lean::is_scalar(x_67)) {
 x_69 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_69 = x_67;
}
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_66);
return x_69;
}
}
else
{
obj* x_70; uint8 x_71; obj* x_72; obj* x_73; 
x_70 = lean::cnstr_get(x_51, 0);
lean::inc(x_70);
x_71 = lean::cnstr_get_scalar<uint8>(x_51, sizeof(void*)*1);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_release(x_51, 0);
 x_72 = x_51;
} else {
 lean::dec_ref(x_51);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_70);
lean::cnstr_set_scalar(x_73, sizeof(void*)*1, x_71);
lean::cnstr_set(x_4, 0, x_73);
return x_4;
}
}
}
else
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; uint32 x_79; uint8 x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_74 = lean::cnstr_get(x_4, 1);
lean::inc(x_74);
lean::dec(x_4);
x_75 = lean::cnstr_get(x_5, 0);
lean::inc(x_75);
x_76 = lean::cnstr_get(x_5, 1);
lean::inc(x_76);
x_77 = lean::cnstr_get(x_5, 2);
lean::inc(x_77);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_78 = x_5;
} else {
 lean::dec_ref(x_5);
 x_78 = lean::box(0);
}
x_79 = lean::unbox_uint32(x_75);
lean::dec(x_75);
x_80 = l_Lean_isIdBeginEscape(x_79);
x_81 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_82 = lean::box(x_80);
if (lean::is_scalar(x_78)) {
 x_83 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_83 = x_78;
}
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_76);
lean::cnstr_set(x_83, 2, x_81);
x_84 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_77, x_83);
if (lean::obj_tag(x_84) == 0)
{
obj* x_85; uint8 x_86; 
x_85 = lean::cnstr_get(x_84, 0);
lean::inc(x_85);
x_86 = lean::unbox(x_85);
lean::dec(x_85);
if (x_86 == 0)
{
obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_87 = lean::cnstr_get(x_84, 1);
lean::inc(x_87);
x_88 = lean::cnstr_get(x_84, 2);
lean::inc(x_88);
lean::dec(x_84);
x_89 = l_Lean_Parser_idPartDefault___at___private_init_lean_parser_token_4__ident_x27___spec__3(x_1, x_87, x_74);
x_90 = lean::cnstr_get(x_89, 0);
lean::inc(x_90);
x_91 = lean::cnstr_get(x_89, 1);
lean::inc(x_91);
if (lean::is_exclusive(x_89)) {
 lean::cnstr_release(x_89, 0);
 lean::cnstr_release(x_89, 1);
 x_92 = x_89;
} else {
 lean::dec_ref(x_89);
 x_92 = lean::box(0);
}
x_93 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_88, x_90);
if (lean::is_scalar(x_92)) {
 x_94 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_94 = x_92;
}
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_91);
return x_94;
}
else
{
obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
x_95 = lean::cnstr_get(x_84, 1);
lean::inc(x_95);
x_96 = lean::cnstr_get(x_84, 2);
lean::inc(x_96);
lean::dec(x_84);
x_97 = l_Lean_Parser_idPartEscaped___at___private_init_lean_parser_token_4__ident_x27___spec__5(x_1, x_95, x_74);
x_98 = lean::cnstr_get(x_97, 0);
lean::inc(x_98);
x_99 = lean::cnstr_get(x_97, 1);
lean::inc(x_99);
if (lean::is_exclusive(x_97)) {
 lean::cnstr_release(x_97, 0);
 lean::cnstr_release(x_97, 1);
 x_100 = x_97;
} else {
 lean::dec_ref(x_97);
 x_100 = lean::box(0);
}
x_101 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_96, x_98);
if (lean::is_scalar(x_100)) {
 x_102 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_102 = x_100;
}
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_99);
return x_102;
}
}
else
{
obj* x_103; uint8 x_104; obj* x_105; obj* x_106; obj* x_107; 
x_103 = lean::cnstr_get(x_84, 0);
lean::inc(x_103);
x_104 = lean::cnstr_get_scalar<uint8>(x_84, sizeof(void*)*1);
if (lean::is_exclusive(x_84)) {
 lean::cnstr_release(x_84, 0);
 x_105 = x_84;
} else {
 lean::dec_ref(x_84);
 x_105 = lean::box(0);
}
if (lean::is_scalar(x_105)) {
 x_106 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_106 = x_105;
}
lean::cnstr_set(x_106, 0, x_103);
lean::cnstr_set_scalar(x_106, sizeof(void*)*1, x_104);
x_107 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_107, 0, x_106);
lean::cnstr_set(x_107, 1, x_74);
return x_107;
}
}
}
else
{
uint8 x_108; 
x_108 = !lean::is_exclusive(x_4);
if (x_108 == 0)
{
obj* x_109; uint8 x_110; 
x_109 = lean::cnstr_get(x_4, 0);
lean::dec(x_109);
x_110 = !lean::is_exclusive(x_5);
if (x_110 == 0)
{
return x_4;
}
else
{
obj* x_111; uint8 x_112; obj* x_113; 
x_111 = lean::cnstr_get(x_5, 0);
x_112 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
lean::inc(x_111);
lean::dec(x_5);
x_113 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_113, 0, x_111);
lean::cnstr_set_scalar(x_113, sizeof(void*)*1, x_112);
lean::cnstr_set(x_4, 0, x_113);
return x_4;
}
}
else
{
obj* x_114; obj* x_115; uint8 x_116; obj* x_117; obj* x_118; obj* x_119; 
x_114 = lean::cnstr_get(x_4, 1);
lean::inc(x_114);
lean::dec(x_4);
x_115 = lean::cnstr_get(x_5, 0);
lean::inc(x_115);
x_116 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_117 = x_5;
} else {
 lean::dec_ref(x_5);
 x_117 = lean::box(0);
}
if (lean::is_scalar(x_117)) {
 x_118 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_118 = x_117;
}
lean::cnstr_set(x_118, 0, x_115);
lean::cnstr_set_scalar(x_118, sizeof(void*)*1, x_116);
x_119 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_119, 0, x_118);
lean::cnstr_set(x_119, 1, x_114);
return x_119;
}
}
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_4__ident_x27___spec__7(obj* x_1, obj* x_2, uint32 x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_20; obj* x_21; 
lean::inc(x_5);
x_20 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6(x_3, x_4, x_5, x_6);
x_21 = lean::cnstr_get(x_20, 0);
lean::inc(x_21);
if (lean::obj_tag(x_21) == 0)
{
obj* x_22; uint8 x_23; 
x_22 = lean::cnstr_get(x_20, 1);
lean::inc(x_22);
lean::dec(x_20);
x_23 = !lean::is_exclusive(x_21);
if (x_23 == 0)
{
obj* x_24; obj* x_25; obj* x_26; uint32 x_27; obj* x_28; obj* x_29; 
x_24 = lean::cnstr_get(x_21, 1);
x_25 = lean::cnstr_get(x_21, 2);
x_26 = lean::cnstr_get(x_21, 0);
lean::dec(x_26);
x_27 = l_Lean_idBeginEscape;
lean::inc(x_24);
x_28 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6(x_27, x_4, x_24, x_22);
x_29 = lean::cnstr_get(x_28, 0);
lean::inc(x_29);
if (lean::obj_tag(x_29) == 0)
{
obj* x_30; obj* x_31; 
lean::free_heap_obj(x_21);
lean::dec(x_24);
lean::dec(x_2);
lean::dec(x_1);
x_30 = lean::cnstr_get(x_28, 1);
lean::inc(x_30);
lean::dec(x_28);
x_31 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_25, x_29);
x_7 = x_31;
x_8 = x_30;
goto block_19;
}
else
{
uint8 x_32; 
x_32 = lean::cnstr_get_scalar<uint8>(x_29, sizeof(void*)*1);
if (x_32 == 0)
{
obj* x_33; obj* x_34; uint8 x_35; 
x_33 = lean::cnstr_get(x_28, 1);
lean::inc(x_33);
lean::dec(x_28);
x_34 = lean::cnstr_get(x_29, 0);
lean::inc(x_34);
lean::dec(x_29);
x_35 = l_String_OldIterator_hasNext___main(x_24);
if (x_35 == 0)
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::free_heap_obj(x_21);
x_36 = lean::box(0);
x_37 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_38 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_37, x_1, x_36, x_36, x_4, x_24, x_33);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_38, 1);
lean::inc(x_40);
lean::dec(x_38);
x_41 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_2, x_39);
x_42 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_34, x_41);
x_43 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_25, x_42);
x_7 = x_43;
x_8 = x_40;
goto block_19;
}
else
{
uint32 x_44; uint8 x_45; 
x_44 = l_String_OldIterator_curr___main(x_24);
x_45 = l_Lean_isIdFirst(x_44);
if (x_45 == 0)
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
lean::free_heap_obj(x_21);
x_46 = l_Char_quoteCore(x_44);
x_47 = l_Char_HasRepr___closed__1;
x_48 = lean::string_append(x_47, x_46);
lean::dec(x_46);
x_49 = lean::string_append(x_48, x_47);
x_50 = lean::box(0);
x_51 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_49, x_1, x_50, x_50, x_4, x_24, x_33);
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
x_53 = lean::cnstr_get(x_51, 1);
lean::inc(x_53);
lean::dec(x_51);
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_2, x_52);
x_55 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_34, x_54);
x_56 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_25, x_55);
x_7 = x_56;
x_8 = x_53;
goto block_19;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
lean::dec(x_34);
lean::dec(x_2);
lean::dec(x_1);
x_57 = l_String_OldIterator_next___main(x_24);
x_58 = lean::box(0);
x_59 = lean::box_uint32(x_44);
lean::cnstr_set(x_21, 2, x_58);
lean::cnstr_set(x_21, 1, x_57);
lean::cnstr_set(x_21, 0, x_59);
x_60 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_25, x_21);
x_7 = x_60;
x_8 = x_33;
goto block_19;
}
}
}
else
{
obj* x_61; obj* x_62; 
lean::free_heap_obj(x_21);
lean::dec(x_24);
lean::dec(x_2);
lean::dec(x_1);
x_61 = lean::cnstr_get(x_28, 1);
lean::inc(x_61);
lean::dec(x_28);
x_62 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_25, x_29);
x_7 = x_62;
x_8 = x_61;
goto block_19;
}
}
}
else
{
obj* x_63; obj* x_64; uint32 x_65; obj* x_66; obj* x_67; 
x_63 = lean::cnstr_get(x_21, 1);
x_64 = lean::cnstr_get(x_21, 2);
lean::inc(x_64);
lean::inc(x_63);
lean::dec(x_21);
x_65 = l_Lean_idBeginEscape;
lean::inc(x_63);
x_66 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6(x_65, x_4, x_63, x_22);
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
if (lean::obj_tag(x_67) == 0)
{
obj* x_68; obj* x_69; 
lean::dec(x_63);
lean::dec(x_2);
lean::dec(x_1);
x_68 = lean::cnstr_get(x_66, 1);
lean::inc(x_68);
lean::dec(x_66);
x_69 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_64, x_67);
x_7 = x_69;
x_8 = x_68;
goto block_19;
}
else
{
uint8 x_70; 
x_70 = lean::cnstr_get_scalar<uint8>(x_67, sizeof(void*)*1);
if (x_70 == 0)
{
obj* x_71; obj* x_72; uint8 x_73; 
x_71 = lean::cnstr_get(x_66, 1);
lean::inc(x_71);
lean::dec(x_66);
x_72 = lean::cnstr_get(x_67, 0);
lean::inc(x_72);
lean::dec(x_67);
x_73 = l_String_OldIterator_hasNext___main(x_63);
if (x_73 == 0)
{
obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_74 = lean::box(0);
x_75 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_76 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_75, x_1, x_74, x_74, x_4, x_63, x_71);
x_77 = lean::cnstr_get(x_76, 0);
lean::inc(x_77);
x_78 = lean::cnstr_get(x_76, 1);
lean::inc(x_78);
lean::dec(x_76);
x_79 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_2, x_77);
x_80 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_72, x_79);
x_81 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_64, x_80);
x_7 = x_81;
x_8 = x_78;
goto block_19;
}
else
{
uint32 x_82; uint8 x_83; 
x_82 = l_String_OldIterator_curr___main(x_63);
x_83 = l_Lean_isIdFirst(x_82);
if (x_83 == 0)
{
obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_84 = l_Char_quoteCore(x_82);
x_85 = l_Char_HasRepr___closed__1;
x_86 = lean::string_append(x_85, x_84);
lean::dec(x_84);
x_87 = lean::string_append(x_86, x_85);
x_88 = lean::box(0);
x_89 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_87, x_1, x_88, x_88, x_4, x_63, x_71);
x_90 = lean::cnstr_get(x_89, 0);
lean::inc(x_90);
x_91 = lean::cnstr_get(x_89, 1);
lean::inc(x_91);
lean::dec(x_89);
x_92 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_2, x_90);
x_93 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_72, x_92);
x_94 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_64, x_93);
x_7 = x_94;
x_8 = x_91;
goto block_19;
}
else
{
obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; 
lean::dec(x_72);
lean::dec(x_2);
lean::dec(x_1);
x_95 = l_String_OldIterator_next___main(x_63);
x_96 = lean::box(0);
x_97 = lean::box_uint32(x_82);
x_98 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_98, 0, x_97);
lean::cnstr_set(x_98, 1, x_95);
lean::cnstr_set(x_98, 2, x_96);
x_99 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_64, x_98);
x_7 = x_99;
x_8 = x_71;
goto block_19;
}
}
}
else
{
obj* x_100; obj* x_101; 
lean::dec(x_63);
lean::dec(x_2);
lean::dec(x_1);
x_100 = lean::cnstr_get(x_66, 1);
lean::inc(x_100);
lean::dec(x_66);
x_101 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_64, x_67);
x_7 = x_101;
x_8 = x_100;
goto block_19;
}
}
}
}
else
{
obj* x_102; uint8 x_103; 
lean::dec(x_2);
lean::dec(x_1);
x_102 = lean::cnstr_get(x_20, 1);
lean::inc(x_102);
lean::dec(x_20);
x_103 = !lean::is_exclusive(x_21);
if (x_103 == 0)
{
x_7 = x_21;
x_8 = x_102;
goto block_19;
}
else
{
obj* x_104; uint8 x_105; obj* x_106; 
x_104 = lean::cnstr_get(x_21, 0);
x_105 = lean::cnstr_get_scalar<uint8>(x_21, sizeof(void*)*1);
lean::inc(x_104);
lean::dec(x_21);
x_106 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_106, 0, x_104);
lean::cnstr_set_scalar(x_106, sizeof(void*)*1, x_105);
x_7 = x_106;
x_8 = x_102;
goto block_19;
}
}
block_19:
{
if (lean::obj_tag(x_7) == 0)
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_7);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_7, 2);
lean::dec(x_10);
x_11 = lean::cnstr_get(x_7, 1);
lean::dec(x_11);
x_12 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_7, 2, x_12);
lean::cnstr_set(x_7, 1, x_5);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_7);
lean::cnstr_set(x_13, 1, x_8);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
lean::dec(x_7);
x_15 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_16 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_16, 0, x_14);
lean::cnstr_set(x_16, 1, x_5);
lean::cnstr_set(x_16, 2, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_8);
return x_17;
}
}
else
{
obj* x_18; 
lean::dec(x_5);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_7);
lean::cnstr_set(x_18, 1, x_8);
return x_18;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at___private_init_lean_parser_token_4__ident_x27___spec__9(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; uint8 x_8; 
x_7 = lean::mk_nat_obj(0u);
x_8 = lean::nat_dec_eq(x_3, x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = lean::mk_nat_obj(1u);
x_10 = lean::nat_sub(x_3, x_9);
lean::inc(x_1);
lean::inc(x_5);
lean::inc(x_4);
x_11 = lean::apply_3(x_1, x_4, x_5, x_6);
x_12 = lean::cnstr_get(x_11, 0);
lean::inc(x_12);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; uint8 x_14; 
x_13 = lean::cnstr_get(x_11, 1);
lean::inc(x_13);
lean::dec(x_11);
x_14 = !lean::is_exclusive(x_12);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; 
x_15 = lean::cnstr_get(x_12, 0);
x_16 = lean::cnstr_get(x_12, 1);
x_17 = lean::cnstr_get(x_12, 2);
lean::inc(x_2);
x_18 = lean_name_mk_string(x_2, x_15);
x_19 = l_Lean_Parser_MonadParsec_foldlAux___main___at___private_init_lean_parser_token_4__ident_x27___spec__9(x_1, x_18, x_10, x_4, x_16, x_13);
lean::dec(x_10);
x_20 = !lean::is_exclusive(x_19);
if (x_20 == 0)
{
obj* x_21; obj* x_22; 
x_21 = lean::cnstr_get(x_19, 0);
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_21);
if (lean::obj_tag(x_22) == 0)
{
lean::free_heap_obj(x_12);
lean::dec(x_5);
lean::dec(x_2);
lean::cnstr_set(x_19, 0, x_22);
return x_19;
}
else
{
uint8 x_23; 
x_23 = lean::cnstr_get_scalar<uint8>(x_22, sizeof(void*)*1);
if (x_23 == 0)
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_24 = lean::cnstr_get(x_22, 0);
lean::inc(x_24);
lean::dec(x_22);
x_25 = lean::cnstr_get(x_24, 2);
lean::inc(x_25);
lean::dec(x_24);
x_26 = l_mjoin___rarg___closed__1;
x_27 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_27, 0, x_25);
lean::closure_set(x_27, 1, x_26);
x_28 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_28, 0, x_27);
lean::cnstr_set(x_12, 2, x_28);
lean::cnstr_set(x_12, 1, x_5);
lean::cnstr_set(x_12, 0, x_2);
lean::cnstr_set(x_19, 0, x_12);
return x_19;
}
else
{
lean::free_heap_obj(x_12);
lean::dec(x_5);
lean::dec(x_2);
lean::cnstr_set(x_19, 0, x_22);
return x_19;
}
}
}
else
{
obj* x_29; obj* x_30; obj* x_31; 
x_29 = lean::cnstr_get(x_19, 0);
x_30 = lean::cnstr_get(x_19, 1);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_19);
x_31 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_29);
if (lean::obj_tag(x_31) == 0)
{
obj* x_32; 
lean::free_heap_obj(x_12);
lean::dec(x_5);
lean::dec(x_2);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_30);
return x_32;
}
else
{
uint8 x_33; 
x_33 = lean::cnstr_get_scalar<uint8>(x_31, sizeof(void*)*1);
if (x_33 == 0)
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_34 = lean::cnstr_get(x_31, 0);
lean::inc(x_34);
lean::dec(x_31);
x_35 = lean::cnstr_get(x_34, 2);
lean::inc(x_35);
lean::dec(x_34);
x_36 = l_mjoin___rarg___closed__1;
x_37 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_37, 0, x_35);
lean::closure_set(x_37, 1, x_36);
x_38 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_12, 2, x_38);
lean::cnstr_set(x_12, 1, x_5);
lean::cnstr_set(x_12, 0, x_2);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_12);
lean::cnstr_set(x_39, 1, x_30);
return x_39;
}
else
{
obj* x_40; 
lean::free_heap_obj(x_12);
lean::dec(x_5);
lean::dec(x_2);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_31);
lean::cnstr_set(x_40, 1, x_30);
return x_40;
}
}
}
}
else
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_41 = lean::cnstr_get(x_12, 0);
x_42 = lean::cnstr_get(x_12, 1);
x_43 = lean::cnstr_get(x_12, 2);
lean::inc(x_43);
lean::inc(x_42);
lean::inc(x_41);
lean::dec(x_12);
lean::inc(x_2);
x_44 = lean_name_mk_string(x_2, x_41);
x_45 = l_Lean_Parser_MonadParsec_foldlAux___main___at___private_init_lean_parser_token_4__ident_x27___spec__9(x_1, x_44, x_10, x_4, x_42, x_13);
lean::dec(x_10);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_47 = lean::cnstr_get(x_45, 1);
lean::inc(x_47);
if (lean::is_exclusive(x_45)) {
 lean::cnstr_release(x_45, 0);
 lean::cnstr_release(x_45, 1);
 x_48 = x_45;
} else {
 lean::dec_ref(x_45);
 x_48 = lean::box(0);
}
x_49 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_43, x_46);
if (lean::obj_tag(x_49) == 0)
{
obj* x_50; 
lean::dec(x_5);
lean::dec(x_2);
if (lean::is_scalar(x_48)) {
 x_50 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_50 = x_48;
}
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_47);
return x_50;
}
else
{
uint8 x_51; 
x_51 = lean::cnstr_get_scalar<uint8>(x_49, sizeof(void*)*1);
if (x_51 == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_52 = lean::cnstr_get(x_49, 0);
lean::inc(x_52);
lean::dec(x_49);
x_53 = lean::cnstr_get(x_52, 2);
lean::inc(x_53);
lean::dec(x_52);
x_54 = l_mjoin___rarg___closed__1;
x_55 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_55, 0, x_53);
lean::closure_set(x_55, 1, x_54);
x_56 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_56, 0, x_55);
x_57 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_57, 0, x_2);
lean::cnstr_set(x_57, 1, x_5);
lean::cnstr_set(x_57, 2, x_56);
if (lean::is_scalar(x_48)) {
 x_58 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_58 = x_48;
}
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_47);
return x_58;
}
else
{
obj* x_59; 
lean::dec(x_5);
lean::dec(x_2);
if (lean::is_scalar(x_48)) {
 x_59 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_59 = x_48;
}
lean::cnstr_set(x_59, 0, x_49);
lean::cnstr_set(x_59, 1, x_47);
return x_59;
}
}
}
}
else
{
uint8 x_60; 
lean::dec(x_10);
lean::dec(x_4);
lean::dec(x_1);
x_60 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
if (x_60 == 0)
{
uint8 x_61; 
x_61 = !lean::is_exclusive(x_11);
if (x_61 == 0)
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_62 = lean::cnstr_get(x_11, 0);
lean::dec(x_62);
x_63 = lean::cnstr_get(x_12, 0);
lean::inc(x_63);
lean::dec(x_12);
x_64 = lean::cnstr_get(x_63, 2);
lean::inc(x_64);
lean::dec(x_63);
x_65 = l_mjoin___rarg___closed__1;
x_66 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_66, 0, x_64);
lean::closure_set(x_66, 1, x_65);
x_67 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_67, 0, x_66);
x_68 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_68, 0, x_2);
lean::cnstr_set(x_68, 1, x_5);
lean::cnstr_set(x_68, 2, x_67);
lean::cnstr_set(x_11, 0, x_68);
return x_11;
}
else
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_69 = lean::cnstr_get(x_11, 1);
lean::inc(x_69);
lean::dec(x_11);
x_70 = lean::cnstr_get(x_12, 0);
lean::inc(x_70);
lean::dec(x_12);
x_71 = lean::cnstr_get(x_70, 2);
lean::inc(x_71);
lean::dec(x_70);
x_72 = l_mjoin___rarg___closed__1;
x_73 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_73, 0, x_71);
lean::closure_set(x_73, 1, x_72);
x_74 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_74, 0, x_73);
x_75 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_75, 0, x_2);
lean::cnstr_set(x_75, 1, x_5);
lean::cnstr_set(x_75, 2, x_74);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_69);
return x_76;
}
}
else
{
uint8 x_77; 
lean::dec(x_5);
lean::dec(x_2);
x_77 = !lean::is_exclusive(x_11);
if (x_77 == 0)
{
obj* x_78; uint8 x_79; 
x_78 = lean::cnstr_get(x_11, 0);
lean::dec(x_78);
x_79 = !lean::is_exclusive(x_12);
if (x_79 == 0)
{
return x_11;
}
else
{
obj* x_80; obj* x_81; 
x_80 = lean::cnstr_get(x_12, 0);
lean::inc(x_80);
lean::dec(x_12);
x_81 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set_scalar(x_81, sizeof(void*)*1, x_60);
lean::cnstr_set(x_11, 0, x_81);
return x_11;
}
}
else
{
obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
x_82 = lean::cnstr_get(x_11, 1);
lean::inc(x_82);
lean::dec(x_11);
x_83 = lean::cnstr_get(x_12, 0);
lean::inc(x_83);
if (lean::is_exclusive(x_12)) {
 lean::cnstr_release(x_12, 0);
 x_84 = x_12;
} else {
 lean::dec_ref(x_12);
 x_84 = lean::box(0);
}
if (lean::is_scalar(x_84)) {
 x_85 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_85 = x_84;
}
lean::cnstr_set(x_85, 0, x_83);
lean::cnstr_set_scalar(x_85, sizeof(void*)*1, x_60);
x_86 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_82);
return x_86;
}
}
}
}
else
{
obj* x_87; obj* x_88; obj* x_89; 
lean::dec(x_4);
lean::dec(x_1);
x_87 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_88 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_88, 0, x_2);
lean::cnstr_set(x_88, 1, x_5);
lean::cnstr_set(x_88, 2, x_87);
x_89 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_6);
return x_89;
}
}
}
obj* l_Lean_Parser_MonadParsec_foldl___at___private_init_lean_parser_token_4__ident_x27___spec__8(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = l_String_OldIterator_remaining___main(x_4);
x_7 = l_Lean_Parser_MonadParsec_foldlAux___main___at___private_init_lean_parser_token_4__ident_x27___spec__9(x_2, x_1, x_6, x_3, x_4, x_5);
lean::dec(x_6);
x_8 = !lean::is_exclusive(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_7, 0);
x_10 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_11 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_10, x_9);
lean::cnstr_set(x_7, 0, x_11);
return x_7;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_12 = lean::cnstr_get(x_7, 0);
x_13 = lean::cnstr_get(x_7, 1);
lean::inc(x_13);
lean::inc(x_12);
lean::dec(x_7);
x_14 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_12);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_13);
return x_16;
}
}
}
obj* l___private_init_lean_parser_token_4__ident_x27___lambda__1(obj* x_1, uint32 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_4__ident_x27___spec__7(x_6, x_1, x_2, x_3, x_4, x_5);
x_8 = !lean::is_exclusive(x_7);
if (x_8 == 0)
{
obj* x_9; obj* x_10; 
x_9 = lean::cnstr_get(x_7, 0);
x_10 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_9);
lean::cnstr_set(x_7, 0, x_10);
return x_7;
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_7, 0);
x_12 = lean::cnstr_get(x_7, 1);
lean::inc(x_12);
lean::inc(x_11);
lean::dec(x_7);
x_13 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_11);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_13);
lean::cnstr_set(x_14, 1, x_12);
return x_14;
}
}
}
obj* l___private_init_lean_parser_token_4__ident_x27___lambda__2(uint32 x_1, uint32 x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
x_6 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6(x_1, x_3, x_4, x_5);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; uint8 x_12; 
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
lean::dec(x_6);
x_9 = lean::cnstr_get(x_7, 1);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_7, 2);
lean::inc(x_10);
lean::dec(x_7);
x_11 = l_Lean_Parser_idPart___at___private_init_lean_parser_token_4__ident_x27___spec__1(x_3, x_9, x_8);
x_12 = !lean::is_exclusive(x_11);
if (x_12 == 0)
{
obj* x_13; obj* x_14; 
x_13 = lean::cnstr_get(x_11, 0);
x_14 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_10, x_13);
lean::cnstr_set(x_11, 0, x_14);
return x_11;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_11, 0);
x_16 = lean::cnstr_get(x_11, 1);
lean::inc(x_16);
lean::inc(x_15);
lean::dec(x_11);
x_17 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_10, x_15);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
return x_18;
}
}
else
{
uint8 x_19; 
x_19 = !lean::is_exclusive(x_6);
if (x_19 == 0)
{
obj* x_20; uint8 x_21; 
x_20 = lean::cnstr_get(x_6, 0);
lean::dec(x_20);
x_21 = !lean::is_exclusive(x_7);
if (x_21 == 0)
{
return x_6;
}
else
{
obj* x_22; uint8 x_23; obj* x_24; 
x_22 = lean::cnstr_get(x_7, 0);
x_23 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
lean::inc(x_22);
lean::dec(x_7);
x_24 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set_scalar(x_24, sizeof(void*)*1, x_23);
lean::cnstr_set(x_6, 0, x_24);
return x_6;
}
}
else
{
obj* x_25; obj* x_26; uint8 x_27; obj* x_28; obj* x_29; obj* x_30; 
x_25 = lean::cnstr_get(x_6, 1);
lean::inc(x_25);
lean::dec(x_6);
x_26 = lean::cnstr_get(x_7, 0);
lean::inc(x_26);
x_27 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_28 = x_7;
} else {
 lean::dec_ref(x_7);
 x_28 = lean::box(0);
}
if (lean::is_scalar(x_28)) {
 x_29 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_29 = x_28;
}
lean::cnstr_set(x_29, 0, x_26);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_27);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_25);
return x_30;
}
}
}
}
obj* _init_l___private_init_lean_parser_token_4__ident_x27___closed__1() {
_start:
{
obj* x_1; obj* x_2; uint32 x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = 46;
x_4 = lean::box_uint32(x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_token_4__ident_x27___lambda__1___boxed), 5, 2);
lean::closure_set(x_5, 0, x_2);
lean::closure_set(x_5, 1, x_4);
x_6 = lean::box_uint32(x_3);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_token_4__ident_x27___lambda__2___boxed), 5, 1);
lean::closure_set(x_7, 0, x_6);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_8, 0, x_5);
lean::closure_set(x_8, 1, x_7);
return x_8;
}
}
obj* l___private_init_lean_parser_token_4__ident_x27(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
lean::inc(x_2);
x_4 = l_Lean_Parser_idPart___at___private_init_lean_parser_token_4__ident_x27___spec__1(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
lean::dec(x_4);
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_5, 2);
lean::inc(x_9);
lean::dec(x_5);
x_10 = lean::box(0);
x_11 = lean_name_mk_string(x_10, x_7);
x_12 = l___private_init_lean_parser_token_4__ident_x27___closed__1;
x_13 = l_Lean_Parser_MonadParsec_foldl___at___private_init_lean_parser_token_4__ident_x27___spec__8(x_11, x_12, x_1, x_8, x_6);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
if (lean::obj_tag(x_14) == 0)
{
uint8 x_15; 
x_15 = !lean::is_exclusive(x_13);
if (x_15 == 0)
{
obj* x_16; uint8 x_17; 
x_16 = lean::cnstr_get(x_13, 0);
lean::dec(x_16);
x_17 = !lean::is_exclusive(x_14);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_18 = lean::cnstr_get(x_14, 0);
x_19 = lean::cnstr_get(x_14, 1);
x_20 = lean::cnstr_get(x_14, 2);
lean::inc(x_2, 2);
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_2);
lean::cnstr_set(x_21, 1, x_2);
x_22 = lean::cnstr_get(x_2, 1);
lean::inc(x_22);
lean::inc(x_19, 2);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_19);
lean::cnstr_set(x_23, 1, x_19);
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_21);
lean::cnstr_set(x_24, 1, x_22);
lean::cnstr_set(x_24, 2, x_23);
x_25 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::inc(x_19);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_2);
lean::cnstr_set(x_26, 1, x_19);
x_27 = lean::box(0);
x_28 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_28, 0, x_25);
lean::cnstr_set(x_28, 1, x_26);
lean::cnstr_set(x_28, 2, x_18);
lean::cnstr_set(x_28, 3, x_27);
lean::cnstr_set(x_28, 4, x_27);
x_29 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_29, 0, x_28);
x_30 = l_Lean_Parser_finishCommentBlock___closed__2;
lean::cnstr_set(x_14, 2, x_30);
lean::cnstr_set(x_14, 0, x_29);
x_31 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_20, x_14);
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_31);
x_33 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_34 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_33, x_32);
lean::cnstr_set(x_13, 0, x_34);
return x_13;
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; 
x_35 = lean::cnstr_get(x_14, 0);
x_36 = lean::cnstr_get(x_14, 1);
x_37 = lean::cnstr_get(x_14, 2);
lean::inc(x_37);
lean::inc(x_36);
lean::inc(x_35);
lean::dec(x_14);
lean::inc(x_2, 2);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_2);
lean::cnstr_set(x_38, 1, x_2);
x_39 = lean::cnstr_get(x_2, 1);
lean::inc(x_39);
lean::inc(x_36, 2);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_36);
lean::cnstr_set(x_40, 1, x_36);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_38);
lean::cnstr_set(x_41, 1, x_39);
lean::cnstr_set(x_41, 2, x_40);
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::inc(x_36);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_2);
lean::cnstr_set(x_43, 1, x_36);
x_44 = lean::box(0);
x_45 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_45, 0, x_42);
lean::cnstr_set(x_45, 1, x_43);
lean::cnstr_set(x_45, 2, x_35);
lean::cnstr_set(x_45, 3, x_44);
lean::cnstr_set(x_45, 4, x_44);
x_46 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_46, 0, x_45);
x_47 = l_Lean_Parser_finishCommentBlock___closed__2;
x_48 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_48, 0, x_46);
lean::cnstr_set(x_48, 1, x_36);
lean::cnstr_set(x_48, 2, x_47);
x_49 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_37, x_48);
x_50 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_49);
x_51 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_52 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_51, x_50);
lean::cnstr_set(x_13, 0, x_52);
return x_13;
}
}
else
{
obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
x_53 = lean::cnstr_get(x_13, 1);
lean::inc(x_53);
lean::dec(x_13);
x_54 = lean::cnstr_get(x_14, 0);
lean::inc(x_54);
x_55 = lean::cnstr_get(x_14, 1);
lean::inc(x_55);
x_56 = lean::cnstr_get(x_14, 2);
lean::inc(x_56);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 lean::cnstr_release(x_14, 1);
 lean::cnstr_release(x_14, 2);
 x_57 = x_14;
} else {
 lean::dec_ref(x_14);
 x_57 = lean::box(0);
}
lean::inc(x_2, 2);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_2);
lean::cnstr_set(x_58, 1, x_2);
x_59 = lean::cnstr_get(x_2, 1);
lean::inc(x_59);
lean::inc(x_55, 2);
x_60 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_60, 0, x_55);
lean::cnstr_set(x_60, 1, x_55);
x_61 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_61, 0, x_58);
lean::cnstr_set(x_61, 1, x_59);
lean::cnstr_set(x_61, 2, x_60);
x_62 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_62, 0, x_61);
lean::inc(x_55);
x_63 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_63, 0, x_2);
lean::cnstr_set(x_63, 1, x_55);
x_64 = lean::box(0);
x_65 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_65, 0, x_62);
lean::cnstr_set(x_65, 1, x_63);
lean::cnstr_set(x_65, 2, x_54);
lean::cnstr_set(x_65, 3, x_64);
lean::cnstr_set(x_65, 4, x_64);
x_66 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_66, 0, x_65);
x_67 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_57)) {
 x_68 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_68 = x_57;
}
lean::cnstr_set(x_68, 0, x_66);
lean::cnstr_set(x_68, 1, x_55);
lean::cnstr_set(x_68, 2, x_67);
x_69 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_56, x_68);
x_70 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_69);
x_71 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_72 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_71, x_70);
x_73 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_53);
return x_73;
}
}
else
{
uint8 x_74; 
lean::dec(x_2);
x_74 = !lean::is_exclusive(x_13);
if (x_74 == 0)
{
obj* x_75; uint8 x_76; 
x_75 = lean::cnstr_get(x_13, 0);
lean::dec(x_75);
x_76 = !lean::is_exclusive(x_14);
if (x_76 == 0)
{
obj* x_77; obj* x_78; obj* x_79; 
x_77 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_14);
x_78 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_79 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_78, x_77);
lean::cnstr_set(x_13, 0, x_79);
return x_13;
}
else
{
obj* x_80; uint8 x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_80 = lean::cnstr_get(x_14, 0);
x_81 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
lean::inc(x_80);
lean::dec(x_14);
x_82 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_82, 0, x_80);
lean::cnstr_set_scalar(x_82, sizeof(void*)*1, x_81);
x_83 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_82);
x_84 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_85 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_84, x_83);
lean::cnstr_set(x_13, 0, x_85);
return x_13;
}
}
else
{
obj* x_86; obj* x_87; uint8 x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; 
x_86 = lean::cnstr_get(x_13, 1);
lean::inc(x_86);
lean::dec(x_13);
x_87 = lean::cnstr_get(x_14, 0);
lean::inc(x_87);
x_88 = lean::cnstr_get_scalar<uint8>(x_14, sizeof(void*)*1);
if (lean::is_exclusive(x_14)) {
 lean::cnstr_release(x_14, 0);
 x_89 = x_14;
} else {
 lean::dec_ref(x_14);
 x_89 = lean::box(0);
}
if (lean::is_scalar(x_89)) {
 x_90 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_90 = x_89;
}
lean::cnstr_set(x_90, 0, x_87);
lean::cnstr_set_scalar(x_90, sizeof(void*)*1, x_88);
x_91 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_90);
x_92 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_93 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_92, x_91);
x_94 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_94, 0, x_93);
lean::cnstr_set(x_94, 1, x_86);
return x_94;
}
}
}
else
{
uint8 x_95; 
lean::dec(x_2);
lean::dec(x_1);
x_95 = !lean::is_exclusive(x_4);
if (x_95 == 0)
{
obj* x_96; uint8 x_97; 
x_96 = lean::cnstr_get(x_4, 0);
lean::dec(x_96);
x_97 = !lean::is_exclusive(x_5);
if (x_97 == 0)
{
obj* x_98; obj* x_99; 
x_98 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_99 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_98, x_5);
lean::cnstr_set(x_4, 0, x_99);
return x_4;
}
else
{
obj* x_100; uint8 x_101; obj* x_102; obj* x_103; obj* x_104; 
x_100 = lean::cnstr_get(x_5, 0);
x_101 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
lean::inc(x_100);
lean::dec(x_5);
x_102 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_102, 0, x_100);
lean::cnstr_set_scalar(x_102, sizeof(void*)*1, x_101);
x_103 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_104 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_103, x_102);
lean::cnstr_set(x_4, 0, x_104);
return x_4;
}
}
else
{
obj* x_105; obj* x_106; uint8 x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_105 = lean::cnstr_get(x_4, 1);
lean::inc(x_105);
lean::dec(x_4);
x_106 = lean::cnstr_get(x_5, 0);
lean::inc(x_106);
x_107 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_108 = x_5;
} else {
 lean::dec_ref(x_5);
 x_108 = lean::box(0);
}
if (lean::is_scalar(x_108)) {
 x_109 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_109 = x_108;
}
lean::cnstr_set(x_109, 0, x_106);
lean::cnstr_set_scalar(x_109, sizeof(void*)*1, x_107);
x_110 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_111 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_110, x_109);
x_112 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_105);
return x_112;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_curr___at___private_init_lean_parser_token_4__ident_x27___spec__2___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_MonadParsec_curr___at___private_init_lean_parser_token_4__ident_x27___spec__2(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x27___spec__4___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_takeWhileCont___at___private_init_lean_parser_token_4__ident_x27___spec__4(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_idPartDefault___at___private_init_lean_parser_token_4__ident_x27___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_idPartDefault___at___private_init_lean_parser_token_4__ident_x27___spec__3(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_6 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6(x_5, x_2, x_3, x_4);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_idPartEscaped___at___private_init_lean_parser_token_4__ident_x27___spec__5___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_idPartEscaped___at___private_init_lean_parser_token_4__ident_x27___spec__5(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_idPart___at___private_init_lean_parser_token_4__ident_x27___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_idPart___at___private_init_lean_parser_token_4__ident_x27___spec__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_4__ident_x27___spec__7___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
uint32 x_7; obj* x_8; 
x_7 = lean::unbox_uint32(x_3);
lean::dec(x_3);
x_8 = l_Lean_Parser_ParsecT_lookahead___at___private_init_lean_parser_token_4__ident_x27___spec__7(x_1, x_2, x_7, x_4, x_5, x_6);
lean::dec(x_4);
return x_8;
}
}
obj* l_Lean_Parser_MonadParsec_foldlAux___main___at___private_init_lean_parser_token_4__ident_x27___spec__9___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_MonadParsec_foldlAux___main___at___private_init_lean_parser_token_4__ident_x27___spec__9(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
return x_7;
}
}
obj* l___private_init_lean_parser_token_4__ident_x27___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint32 x_6; obj* x_7; 
x_6 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_7 = l___private_init_lean_parser_token_4__ident_x27___lambda__1(x_1, x_6, x_3, x_4, x_5);
lean::dec(x_3);
return x_7;
}
}
obj* l___private_init_lean_parser_token_4__ident_x27___lambda__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint32 x_6; uint32 x_7; obj* x_8; 
x_6 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_7 = lean::unbox_uint32(x_2);
lean::dec(x_2);
x_8 = l___private_init_lean_parser_token_4__ident_x27___lambda__2(x_6, x_7, x_3, x_4, x_5);
lean::dec(x_3);
return x_8;
}
}
obj* l_ReaderT_orelse___at_Lean_Parser_parseBinLit___spec__1___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_4);
lean::inc(x_3);
x_6 = lean::apply_3(x_1, x_3, x_4, x_5);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_8 = !lean::is_exclusive(x_6);
if (x_8 == 0)
{
obj* x_9; 
x_9 = lean::cnstr_get(x_6, 0);
lean::dec(x_9);
return x_6;
}
else
{
obj* x_10; obj* x_11; 
x_10 = lean::cnstr_get(x_6, 1);
lean::inc(x_10);
lean::dec(x_6);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_7);
lean::cnstr_set(x_11, 1, x_10);
return x_11;
}
}
else
{
uint8 x_12; 
x_12 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; uint8 x_16; 
x_13 = lean::cnstr_get(x_6, 1);
lean::inc(x_13);
lean::dec(x_6);
x_14 = lean::cnstr_get(x_7, 0);
lean::inc(x_14);
lean::dec(x_7);
x_15 = lean::apply_3(x_2, x_3, x_4, x_13);
x_16 = !lean::is_exclusive(x_15);
if (x_16 == 0)
{
obj* x_17; obj* x_18; 
x_17 = lean::cnstr_get(x_15, 0);
x_18 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_14, x_17);
lean::cnstr_set(x_15, 0, x_18);
return x_15;
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_19 = lean::cnstr_get(x_15, 0);
x_20 = lean::cnstr_get(x_15, 1);
lean::inc(x_20);
lean::inc(x_19);
lean::dec(x_15);
x_21 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_14, x_19);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_20);
return x_22;
}
}
else
{
uint8 x_23; 
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
x_23 = !lean::is_exclusive(x_6);
if (x_23 == 0)
{
obj* x_24; 
x_24 = lean::cnstr_get(x_6, 0);
lean::dec(x_24);
return x_6;
}
else
{
obj* x_25; obj* x_26; 
x_25 = lean::cnstr_get(x_6, 1);
lean::inc(x_25);
lean::dec(x_6);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_7);
lean::cnstr_set(x_26, 1, x_25);
return x_26;
}
}
}
}
}
obj* l_ReaderT_orelse___at_Lean_Parser_parseBinLit___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_orelse___at_Lean_Parser_parseBinLit___spec__1___rarg), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux_x27___main___at_Lean_Parser_parseBinLit___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_2, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_2, x_8);
lean::inc(x_1);
lean::inc(x_3);
x_10 = lean::apply_3(x_1, x_3, x_4, x_5);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; uint8 x_13; 
x_12 = lean::cnstr_get(x_10, 1);
lean::inc(x_12);
lean::dec(x_10);
x_13 = !lean::is_exclusive(x_11);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_14 = lean::cnstr_get(x_11, 1);
x_15 = lean::cnstr_get(x_11, 2);
x_16 = lean::cnstr_get(x_11, 0);
lean::dec(x_16);
lean::inc(x_14);
x_17 = l_Lean_Parser_MonadParsec_many1Aux_x27___main___at_Lean_Parser_parseBinLit___spec__2(x_1, x_9, x_3, x_14, x_12);
lean::dec(x_9);
x_18 = lean::cnstr_get(x_17, 0);
lean::inc(x_18);
if (lean::obj_tag(x_18) == 0)
{
uint8 x_19; 
lean::free_heap_obj(x_11);
lean::dec(x_14);
x_19 = !lean::is_exclusive(x_17);
if (x_19 == 0)
{
obj* x_20; obj* x_21; 
x_20 = lean::cnstr_get(x_17, 0);
lean::dec(x_20);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_18);
lean::cnstr_set(x_17, 0, x_21);
return x_17;
}
else
{
obj* x_22; obj* x_23; obj* x_24; 
x_22 = lean::cnstr_get(x_17, 1);
lean::inc(x_22);
lean::dec(x_17);
x_23 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_18);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8 x_25; 
x_25 = lean::cnstr_get_scalar<uint8>(x_18, sizeof(void*)*1);
if (x_25 == 0)
{
uint8 x_26; 
x_26 = !lean::is_exclusive(x_17);
if (x_26 == 0)
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_27 = lean::cnstr_get(x_17, 0);
lean::dec(x_27);
x_28 = lean::cnstr_get(x_18, 0);
lean::inc(x_28);
lean::dec(x_18);
x_29 = lean::cnstr_get(x_28, 2);
lean::inc(x_29);
lean::dec(x_28);
x_30 = l_mjoin___rarg___closed__1;
x_31 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_31, 0, x_29);
lean::closure_set(x_31, 1, x_30);
x_32 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_32, 0, x_31);
x_33 = lean::box(0);
lean::cnstr_set(x_11, 2, x_32);
lean::cnstr_set(x_11, 0, x_33);
x_34 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_11);
lean::cnstr_set(x_17, 0, x_34);
return x_17;
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_35 = lean::cnstr_get(x_17, 1);
lean::inc(x_35);
lean::dec(x_17);
x_36 = lean::cnstr_get(x_18, 0);
lean::inc(x_36);
lean::dec(x_18);
x_37 = lean::cnstr_get(x_36, 2);
lean::inc(x_37);
lean::dec(x_36);
x_38 = l_mjoin___rarg___closed__1;
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_39, 0, x_37);
lean::closure_set(x_39, 1, x_38);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_39);
x_41 = lean::box(0);
lean::cnstr_set(x_11, 2, x_40);
lean::cnstr_set(x_11, 0, x_41);
x_42 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_11);
x_43 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_35);
return x_43;
}
}
else
{
uint8 x_44; 
lean::free_heap_obj(x_11);
lean::dec(x_14);
x_44 = !lean::is_exclusive(x_17);
if (x_44 == 0)
{
obj* x_45; obj* x_46; 
x_45 = lean::cnstr_get(x_17, 0);
lean::dec(x_45);
x_46 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_18);
lean::cnstr_set(x_17, 0, x_46);
return x_17;
}
else
{
obj* x_47; obj* x_48; obj* x_49; 
x_47 = lean::cnstr_get(x_17, 1);
lean::inc(x_47);
lean::dec(x_17);
x_48 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_18);
x_49 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_49, 0, x_48);
lean::cnstr_set(x_49, 1, x_47);
return x_49;
}
}
}
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_50 = lean::cnstr_get(x_11, 1);
x_51 = lean::cnstr_get(x_11, 2);
lean::inc(x_51);
lean::inc(x_50);
lean::dec(x_11);
lean::inc(x_50);
x_52 = l_Lean_Parser_MonadParsec_many1Aux_x27___main___at_Lean_Parser_parseBinLit___spec__2(x_1, x_9, x_3, x_50, x_12);
lean::dec(x_9);
x_53 = lean::cnstr_get(x_52, 0);
lean::inc(x_53);
if (lean::obj_tag(x_53) == 0)
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_50);
x_54 = lean::cnstr_get(x_52, 1);
lean::inc(x_54);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 lean::cnstr_release(x_52, 1);
 x_55 = x_52;
} else {
 lean::dec_ref(x_52);
 x_55 = lean::box(0);
}
x_56 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_51, x_53);
if (lean::is_scalar(x_55)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_55;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_54);
return x_57;
}
else
{
uint8 x_58; 
x_58 = lean::cnstr_get_scalar<uint8>(x_53, sizeof(void*)*1);
if (x_58 == 0)
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_59 = lean::cnstr_get(x_52, 1);
lean::inc(x_59);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 lean::cnstr_release(x_52, 1);
 x_60 = x_52;
} else {
 lean::dec_ref(x_52);
 x_60 = lean::box(0);
}
x_61 = lean::cnstr_get(x_53, 0);
lean::inc(x_61);
lean::dec(x_53);
x_62 = lean::cnstr_get(x_61, 2);
lean::inc(x_62);
lean::dec(x_61);
x_63 = l_mjoin___rarg___closed__1;
x_64 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_64, 0, x_62);
lean::closure_set(x_64, 1, x_63);
x_65 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_65, 0, x_64);
x_66 = lean::box(0);
x_67 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_50);
lean::cnstr_set(x_67, 2, x_65);
x_68 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_51, x_67);
if (lean::is_scalar(x_60)) {
 x_69 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_69 = x_60;
}
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_59);
return x_69;
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; 
lean::dec(x_50);
x_70 = lean::cnstr_get(x_52, 1);
lean::inc(x_70);
if (lean::is_exclusive(x_52)) {
 lean::cnstr_release(x_52, 0);
 lean::cnstr_release(x_52, 1);
 x_71 = x_52;
} else {
 lean::dec_ref(x_52);
 x_71 = lean::box(0);
}
x_72 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_51, x_53);
if (lean::is_scalar(x_71)) {
 x_73 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_73 = x_71;
}
lean::cnstr_set(x_73, 0, x_72);
lean::cnstr_set(x_73, 1, x_70);
return x_73;
}
}
}
}
else
{
uint8 x_74; 
lean::dec(x_9);
lean::dec(x_3);
lean::dec(x_1);
x_74 = !lean::is_exclusive(x_10);
if (x_74 == 0)
{
obj* x_75; uint8 x_76; 
x_75 = lean::cnstr_get(x_10, 0);
lean::dec(x_75);
x_76 = !lean::is_exclusive(x_11);
if (x_76 == 0)
{
return x_10;
}
else
{
obj* x_77; uint8 x_78; obj* x_79; 
x_77 = lean::cnstr_get(x_11, 0);
x_78 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
lean::inc(x_77);
lean::dec(x_11);
x_79 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_79, 0, x_77);
lean::cnstr_set_scalar(x_79, sizeof(void*)*1, x_78);
lean::cnstr_set(x_10, 0, x_79);
return x_10;
}
}
else
{
obj* x_80; obj* x_81; uint8 x_82; obj* x_83; obj* x_84; obj* x_85; 
x_80 = lean::cnstr_get(x_10, 1);
lean::inc(x_80);
lean::dec(x_10);
x_81 = lean::cnstr_get(x_11, 0);
lean::inc(x_81);
x_82 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_83 = x_11;
} else {
 lean::dec_ref(x_11);
 x_83 = lean::box(0);
}
if (lean::is_scalar(x_83)) {
 x_84 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_84 = x_83;
}
lean::cnstr_set(x_84, 0, x_81);
lean::cnstr_set_scalar(x_84, sizeof(void*)*1, x_82);
x_85 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_80);
return x_85;
}
}
}
else
{
obj* x_86; obj* x_87; 
x_86 = lean::apply_3(x_1, x_3, x_4, x_5);
x_87 = lean::cnstr_get(x_86, 0);
lean::inc(x_87);
if (lean::obj_tag(x_87) == 0)
{
uint8 x_88; 
x_88 = !lean::is_exclusive(x_86);
if (x_88 == 0)
{
obj* x_89; uint8 x_90; 
x_89 = lean::cnstr_get(x_86, 0);
lean::dec(x_89);
x_90 = !lean::is_exclusive(x_87);
if (x_90 == 0)
{
obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_91 = lean::cnstr_get(x_87, 2);
x_92 = lean::cnstr_get(x_87, 0);
lean::dec(x_92);
x_93 = lean::box(0);
x_94 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_87, 2, x_94);
lean::cnstr_set(x_87, 0, x_93);
x_95 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_91, x_87);
lean::cnstr_set(x_86, 0, x_95);
return x_86;
}
else
{
obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_96 = lean::cnstr_get(x_87, 1);
x_97 = lean::cnstr_get(x_87, 2);
lean::inc(x_97);
lean::inc(x_96);
lean::dec(x_87);
x_98 = lean::box(0);
x_99 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_100 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_100, 0, x_98);
lean::cnstr_set(x_100, 1, x_96);
lean::cnstr_set(x_100, 2, x_99);
x_101 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_97, x_100);
lean::cnstr_set(x_86, 0, x_101);
return x_86;
}
}
else
{
obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; 
x_102 = lean::cnstr_get(x_86, 1);
lean::inc(x_102);
lean::dec(x_86);
x_103 = lean::cnstr_get(x_87, 1);
lean::inc(x_103);
x_104 = lean::cnstr_get(x_87, 2);
lean::inc(x_104);
if (lean::is_exclusive(x_87)) {
 lean::cnstr_release(x_87, 0);
 lean::cnstr_release(x_87, 1);
 lean::cnstr_release(x_87, 2);
 x_105 = x_87;
} else {
 lean::dec_ref(x_87);
 x_105 = lean::box(0);
}
x_106 = lean::box(0);
x_107 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_105)) {
 x_108 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_108 = x_105;
}
lean::cnstr_set(x_108, 0, x_106);
lean::cnstr_set(x_108, 1, x_103);
lean::cnstr_set(x_108, 2, x_107);
x_109 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_104, x_108);
x_110 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_110, 0, x_109);
lean::cnstr_set(x_110, 1, x_102);
return x_110;
}
}
else
{
uint8 x_111; 
x_111 = !lean::is_exclusive(x_86);
if (x_111 == 0)
{
obj* x_112; uint8 x_113; 
x_112 = lean::cnstr_get(x_86, 0);
lean::dec(x_112);
x_113 = !lean::is_exclusive(x_87);
if (x_113 == 0)
{
return x_86;
}
else
{
obj* x_114; uint8 x_115; obj* x_116; 
x_114 = lean::cnstr_get(x_87, 0);
x_115 = lean::cnstr_get_scalar<uint8>(x_87, sizeof(void*)*1);
lean::inc(x_114);
lean::dec(x_87);
x_116 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_116, 0, x_114);
lean::cnstr_set_scalar(x_116, sizeof(void*)*1, x_115);
lean::cnstr_set(x_86, 0, x_116);
return x_86;
}
}
else
{
obj* x_117; obj* x_118; uint8 x_119; obj* x_120; obj* x_121; obj* x_122; 
x_117 = lean::cnstr_get(x_86, 1);
lean::inc(x_117);
lean::dec(x_86);
x_118 = lean::cnstr_get(x_87, 0);
lean::inc(x_118);
x_119 = lean::cnstr_get_scalar<uint8>(x_87, sizeof(void*)*1);
if (lean::is_exclusive(x_87)) {
 lean::cnstr_release(x_87, 0);
 x_120 = x_87;
} else {
 lean::dec_ref(x_87);
 x_120 = lean::box(0);
}
if (lean::is_scalar(x_120)) {
 x_121 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_121 = x_120;
}
lean::cnstr_set(x_121, 0, x_118);
lean::cnstr_set_scalar(x_121, sizeof(void*)*1, x_119);
x_122 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_122, 0, x_121);
lean::cnstr_set(x_122, 1, x_117);
return x_122;
}
}
}
}
}
obj* _init_l_Lean_Parser_parseBinLit___closed__1() {
_start:
{
uint32 x_1; obj* x_2; obj* x_3; uint32 x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = 48;
x_2 = lean::box_uint32(x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6___boxed), 4, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = 49;
x_5 = lean::box_uint32(x_4);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6___boxed), 4, 1);
lean::closure_set(x_6, 0, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_orelse___at_Lean_Parser_parseBinLit___spec__1___rarg), 5, 2);
lean::closure_set(x_7, 0, x_3);
lean::closure_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_Lean_Parser_parseBinLit(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; uint32 x_5; uint32 x_6; obj* x_7; obj* x_8; 
x_4 = 48;
x_5 = 98;
x_6 = 66;
x_7 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6(x_4, x_1, x_2, x_3);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_42; obj* x_43; 
x_9 = lean::cnstr_get(x_7, 1);
lean::inc(x_9);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 x_10 = x_7;
} else {
 lean::dec_ref(x_7);
 x_10 = lean::box(0);
}
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
x_12 = lean::cnstr_get(x_8, 2);
lean::inc(x_12);
lean::dec(x_8);
lean::inc(x_11);
x_42 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6(x_5, x_1, x_11, x_9);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
if (lean::obj_tag(x_43) == 0)
{
obj* x_44; 
lean::dec(x_11);
x_44 = lean::cnstr_get(x_42, 1);
lean::inc(x_44);
lean::dec(x_42);
x_13 = x_43;
x_14 = x_44;
goto block_41;
}
else
{
uint8 x_45; 
x_45 = lean::cnstr_get_scalar<uint8>(x_43, sizeof(void*)*1);
if (x_45 == 0)
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_46 = lean::cnstr_get(x_42, 1);
lean::inc(x_46);
lean::dec(x_42);
x_47 = lean::cnstr_get(x_43, 0);
lean::inc(x_47);
lean::dec(x_43);
x_48 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6(x_6, x_1, x_11, x_46);
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_50 = lean::cnstr_get(x_48, 1);
lean::inc(x_50);
lean::dec(x_48);
x_51 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_47, x_49);
x_13 = x_51;
x_14 = x_50;
goto block_41;
}
else
{
obj* x_52; 
lean::dec(x_11);
x_52 = lean::cnstr_get(x_42, 1);
lean::inc(x_52);
lean::dec(x_42);
x_13 = x_43;
x_14 = x_52;
goto block_41;
}
}
block_41:
{
if (lean::obj_tag(x_13) == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; 
lean::dec(x_10);
x_15 = lean::cnstr_get(x_13, 1);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_13, 2);
lean::inc(x_16);
lean::dec(x_13);
x_17 = l_String_OldIterator_remaining___main(x_15);
x_18 = l_Lean_Parser_parseBinLit___closed__1;
x_19 = l_Lean_Parser_MonadParsec_many1Aux_x27___main___at_Lean_Parser_parseBinLit___spec__2(x_18, x_17, x_1, x_15, x_14);
lean::dec(x_17);
x_20 = !lean::is_exclusive(x_19);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_21 = lean::cnstr_get(x_19, 0);
x_22 = l_Lean_Parser_finishCommentBlock___closed__2;
x_23 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_21);
x_24 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_23);
x_25 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_24);
lean::cnstr_set(x_19, 0, x_25);
return x_19;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_26 = lean::cnstr_get(x_19, 0);
x_27 = lean::cnstr_get(x_19, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_19);
x_28 = l_Lean_Parser_finishCommentBlock___closed__2;
x_29 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_28, x_26);
x_30 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_29);
x_31 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_30);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_27);
return x_32;
}
}
else
{
uint8 x_33; 
lean::dec(x_1);
x_33 = !lean::is_exclusive(x_13);
if (x_33 == 0)
{
obj* x_34; obj* x_35; 
x_34 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_13);
if (lean::is_scalar(x_10)) {
 x_35 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_35 = x_10;
}
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_14);
return x_35;
}
else
{
obj* x_36; uint8 x_37; obj* x_38; obj* x_39; obj* x_40; 
x_36 = lean::cnstr_get(x_13, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
lean::inc(x_36);
lean::dec(x_13);
x_38 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set_scalar(x_38, sizeof(void*)*1, x_37);
x_39 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_38);
if (lean::is_scalar(x_10)) {
 x_40 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_40 = x_10;
}
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_14);
return x_40;
}
}
}
}
else
{
uint8 x_53; 
lean::dec(x_1);
x_53 = !lean::is_exclusive(x_7);
if (x_53 == 0)
{
obj* x_54; uint8 x_55; 
x_54 = lean::cnstr_get(x_7, 0);
lean::dec(x_54);
x_55 = !lean::is_exclusive(x_8);
if (x_55 == 0)
{
return x_7;
}
else
{
obj* x_56; uint8 x_57; obj* x_58; 
x_56 = lean::cnstr_get(x_8, 0);
x_57 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
lean::inc(x_56);
lean::dec(x_8);
x_58 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set_scalar(x_58, sizeof(void*)*1, x_57);
lean::cnstr_set(x_7, 0, x_58);
return x_7;
}
}
else
{
obj* x_59; obj* x_60; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; 
x_59 = lean::cnstr_get(x_7, 1);
lean::inc(x_59);
lean::dec(x_7);
x_60 = lean::cnstr_get(x_8, 0);
lean::inc(x_60);
x_61 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_62 = x_8;
} else {
 lean::dec_ref(x_8);
 x_62 = lean::box(0);
}
if (lean::is_scalar(x_62)) {
 x_63 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_63 = x_62;
}
lean::cnstr_set(x_63, 0, x_60);
lean::cnstr_set_scalar(x_63, sizeof(void*)*1, x_61);
x_64 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_59);
return x_64;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_many1Aux_x27___main___at_Lean_Parser_parseBinLit___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_many1Aux_x27___main___at_Lean_Parser_parseBinLit___spec__2(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_parseOctLit___spec__3(uint32 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_2, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_2, x_7);
lean::dec(x_2);
x_9 = l_String_OldIterator_hasNext___main(x_4);
if (x_9 == 0)
{
obj* x_10; 
lean::dec(x_8);
x_10 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_3, x_4);
return x_10;
}
else
{
uint32 x_11; uint8 x_12; 
x_11 = l_String_OldIterator_curr___main(x_4);
x_12 = x_1 <= x_11;
if (x_12 == 0)
{
obj* x_13; 
lean::dec(x_8);
x_13 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_3, x_4);
return x_13;
}
else
{
uint32 x_14; uint8 x_15; 
x_14 = 56;
x_15 = x_11 < x_14;
if (x_15 == 0)
{
obj* x_16; 
lean::dec(x_8);
x_16 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_3, x_4);
return x_16;
}
else
{
obj* x_17; obj* x_18; obj* x_19; 
x_17 = lean::string_push(x_3, x_11);
x_18 = l_String_OldIterator_next___main(x_4);
x_2 = x_8;
x_3 = x_17;
x_4 = x_18;
goto _start;
}
}
}
}
else
{
obj* x_20; 
lean::dec(x_2);
x_20 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_3, x_4);
return x_20;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseOctLit___spec__2(uint32 x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = l_String_OldIterator_remaining___main(x_4);
x_7 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_parseOctLit___spec__3(x_1, x_6, x_2, x_4);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_5);
return x_8;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseOctLit___spec__1(uint32 x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; uint8 x_28; 
x_28 = l_String_OldIterator_hasNext___main(x_3);
if (x_28 == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_29 = lean::box(0);
x_30 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_31 = l_mjoin___rarg___closed__1;
x_32 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_30, x_31, x_29, x_29, x_2, x_3, x_4);
x_33 = lean::cnstr_get(x_32, 0);
lean::inc(x_33);
x_34 = lean::cnstr_get(x_32, 1);
lean::inc(x_34);
lean::dec(x_32);
x_35 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_36 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_35, x_33);
x_5 = x_36;
x_6 = x_34;
goto block_27;
}
else
{
uint32 x_37; uint8 x_38; 
x_37 = l_String_OldIterator_curr___main(x_3);
x_38 = x_1 <= x_37;
if (x_38 == 0)
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_39 = l_Char_quoteCore(x_37);
x_40 = l_Char_HasRepr___closed__1;
x_41 = lean::string_append(x_40, x_39);
lean::dec(x_39);
x_42 = lean::string_append(x_41, x_40);
x_43 = lean::box(0);
x_44 = l_mjoin___rarg___closed__1;
x_45 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_42, x_44, x_43, x_43, x_2, x_3, x_4);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_47 = lean::cnstr_get(x_45, 1);
lean::inc(x_47);
lean::dec(x_45);
x_48 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_49 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_48, x_46);
x_5 = x_49;
x_6 = x_47;
goto block_27;
}
else
{
uint32 x_50; uint8 x_51; 
x_50 = 56;
x_51 = x_37 < x_50;
if (x_51 == 0)
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; 
x_52 = l_Char_quoteCore(x_37);
x_53 = l_Char_HasRepr___closed__1;
x_54 = lean::string_append(x_53, x_52);
lean::dec(x_52);
x_55 = lean::string_append(x_54, x_53);
x_56 = lean::box(0);
x_57 = l_mjoin___rarg___closed__1;
x_58 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_55, x_57, x_56, x_56, x_2, x_3, x_4);
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_60 = lean::cnstr_get(x_58, 1);
lean::inc(x_60);
lean::dec(x_58);
x_61 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_62 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_61, x_59);
x_5 = x_62;
x_6 = x_60;
goto block_27;
}
else
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_63 = l_String_OldIterator_next___main(x_3);
x_64 = lean::box(0);
x_65 = lean::box_uint32(x_37);
x_66 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_66, 0, x_65);
lean::cnstr_set(x_66, 1, x_63);
lean::cnstr_set(x_66, 2, x_64);
x_5 = x_66;
x_6 = x_4;
goto block_27;
}
}
}
block_27:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; uint32 x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_7 = lean::cnstr_get(x_5, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_5, 1);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_5, 2);
lean::inc(x_9);
lean::dec(x_5);
x_10 = l_String_splitAux___main___closed__1;
x_11 = lean::unbox_uint32(x_7);
lean::dec(x_7);
x_12 = lean::string_push(x_10, x_11);
x_13 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseOctLit___spec__2(x_1, x_12, x_2, x_8, x_6);
x_14 = !lean::is_exclusive(x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_13, 0);
x_16 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_15);
lean::cnstr_set(x_13, 0, x_16);
return x_13;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_17 = lean::cnstr_get(x_13, 0);
x_18 = lean::cnstr_get(x_13, 1);
lean::inc(x_18);
lean::inc(x_17);
lean::dec(x_13);
x_19 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_17);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8 x_21; 
x_21 = !lean::is_exclusive(x_5);
if (x_21 == 0)
{
obj* x_22; 
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_5);
lean::cnstr_set(x_22, 1, x_6);
return x_22;
}
else
{
obj* x_23; uint8 x_24; obj* x_25; obj* x_26; 
x_23 = lean::cnstr_get(x_5, 0);
x_24 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
lean::inc(x_23);
lean::dec(x_5);
x_25 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set_scalar(x_25, sizeof(void*)*1, x_24);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_6);
return x_26;
}
}
}
}
}
obj* l_Lean_Parser_parseOctLit(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; uint32 x_5; uint32 x_6; obj* x_7; obj* x_8; 
x_4 = 48;
x_5 = 111;
x_6 = 79;
x_7 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6(x_4, x_1, x_2, x_3);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_7, 1);
lean::inc(x_9);
lean::dec(x_7);
x_10 = lean::cnstr_get(x_8, 1);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_8, 2);
lean::inc(x_11);
lean::dec(x_8);
lean::inc(x_10);
x_12 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6(x_5, x_1, x_10, x_9);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; 
lean::dec(x_10);
x_14 = lean::cnstr_get(x_12, 1);
lean::inc(x_14);
lean::dec(x_12);
x_15 = lean::cnstr_get(x_13, 1);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_13, 2);
lean::inc(x_16);
lean::dec(x_13);
x_17 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseOctLit___spec__1(x_4, x_1, x_15, x_14);
x_18 = !lean::is_exclusive(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_17, 0);
x_20 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_19);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_20);
lean::cnstr_set(x_17, 0, x_21);
return x_17;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_22 = lean::cnstr_get(x_17, 0);
x_23 = lean::cnstr_get(x_17, 1);
lean::inc(x_23);
lean::inc(x_22);
lean::dec(x_17);
x_24 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_22);
x_25 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_24);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_23);
return x_26;
}
}
else
{
uint8 x_27; 
x_27 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; uint8 x_31; 
x_28 = lean::cnstr_get(x_12, 1);
lean::inc(x_28);
lean::dec(x_12);
x_29 = lean::cnstr_get(x_13, 0);
lean::inc(x_29);
lean::dec(x_13);
x_30 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6(x_6, x_1, x_10, x_28);
x_31 = !lean::is_exclusive(x_30);
if (x_31 == 0)
{
obj* x_32; obj* x_33; obj* x_34; 
x_32 = lean::cnstr_get(x_30, 0);
x_33 = lean::cnstr_get(x_30, 1);
x_34 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_32);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_36; obj* x_37; uint8 x_38; 
lean::free_heap_obj(x_30);
x_35 = lean::cnstr_get(x_34, 1);
lean::inc(x_35);
x_36 = lean::cnstr_get(x_34, 2);
lean::inc(x_36);
lean::dec(x_34);
x_37 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseOctLit___spec__1(x_4, x_1, x_35, x_33);
x_38 = !lean::is_exclusive(x_37);
if (x_38 == 0)
{
obj* x_39; obj* x_40; obj* x_41; 
x_39 = lean::cnstr_get(x_37, 0);
x_40 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_36, x_39);
x_41 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_40);
lean::cnstr_set(x_37, 0, x_41);
return x_37;
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_42 = lean::cnstr_get(x_37, 0);
x_43 = lean::cnstr_get(x_37, 1);
lean::inc(x_43);
lean::inc(x_42);
lean::dec(x_37);
x_44 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_36, x_42);
x_45 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_44);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_43);
return x_46;
}
}
else
{
uint8 x_47; 
x_47 = !lean::is_exclusive(x_34);
if (x_47 == 0)
{
obj* x_48; 
x_48 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_34);
lean::cnstr_set(x_30, 0, x_48);
return x_30;
}
else
{
obj* x_49; uint8 x_50; obj* x_51; obj* x_52; 
x_49 = lean::cnstr_get(x_34, 0);
x_50 = lean::cnstr_get_scalar<uint8>(x_34, sizeof(void*)*1);
lean::inc(x_49);
lean::dec(x_34);
x_51 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set_scalar(x_51, sizeof(void*)*1, x_50);
x_52 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_51);
lean::cnstr_set(x_30, 0, x_52);
return x_30;
}
}
}
else
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = lean::cnstr_get(x_30, 0);
x_54 = lean::cnstr_get(x_30, 1);
lean::inc(x_54);
lean::inc(x_53);
lean::dec(x_30);
x_55 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_53);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_56 = lean::cnstr_get(x_55, 1);
lean::inc(x_56);
x_57 = lean::cnstr_get(x_55, 2);
lean::inc(x_57);
lean::dec(x_55);
x_58 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseOctLit___spec__1(x_4, x_1, x_56, x_54);
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_60 = lean::cnstr_get(x_58, 1);
lean::inc(x_60);
if (lean::is_exclusive(x_58)) {
 lean::cnstr_release(x_58, 0);
 lean::cnstr_release(x_58, 1);
 x_61 = x_58;
} else {
 lean::dec_ref(x_58);
 x_61 = lean::box(0);
}
x_62 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_57, x_59);
x_63 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_62);
if (lean::is_scalar(x_61)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_61;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_60);
return x_64;
}
else
{
obj* x_65; uint8 x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_65 = lean::cnstr_get(x_55, 0);
lean::inc(x_65);
x_66 = lean::cnstr_get_scalar<uint8>(x_55, sizeof(void*)*1);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 x_67 = x_55;
} else {
 lean::dec_ref(x_55);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_65);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_66);
x_69 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_68);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_54);
return x_70;
}
}
}
else
{
uint8 x_71; 
lean::dec(x_10);
x_71 = !lean::is_exclusive(x_12);
if (x_71 == 0)
{
obj* x_72; uint8 x_73; 
x_72 = lean::cnstr_get(x_12, 0);
lean::dec(x_72);
x_73 = !lean::is_exclusive(x_13);
if (x_73 == 0)
{
obj* x_74; 
x_74 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_13);
lean::cnstr_set(x_12, 0, x_74);
return x_12;
}
else
{
obj* x_75; obj* x_76; obj* x_77; 
x_75 = lean::cnstr_get(x_13, 0);
lean::inc(x_75);
lean::dec(x_13);
x_76 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set_scalar(x_76, sizeof(void*)*1, x_27);
x_77 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_76);
lean::cnstr_set(x_12, 0, x_77);
return x_12;
}
}
else
{
obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_78 = lean::cnstr_get(x_12, 1);
lean::inc(x_78);
lean::dec(x_12);
x_79 = lean::cnstr_get(x_13, 0);
lean::inc(x_79);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_80 = x_13;
} else {
 lean::dec_ref(x_13);
 x_80 = lean::box(0);
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_79);
lean::cnstr_set_scalar(x_81, sizeof(void*)*1, x_27);
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_81);
x_83 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_78);
return x_83;
}
}
}
}
else
{
uint8 x_84; 
x_84 = !lean::is_exclusive(x_7);
if (x_84 == 0)
{
obj* x_85; uint8 x_86; 
x_85 = lean::cnstr_get(x_7, 0);
lean::dec(x_85);
x_86 = !lean::is_exclusive(x_8);
if (x_86 == 0)
{
return x_7;
}
else
{
obj* x_87; uint8 x_88; obj* x_89; 
x_87 = lean::cnstr_get(x_8, 0);
x_88 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
lean::inc(x_87);
lean::dec(x_8);
x_89 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_89, 0, x_87);
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_88);
lean::cnstr_set(x_7, 0, x_89);
return x_7;
}
}
else
{
obj* x_90; obj* x_91; uint8 x_92; obj* x_93; obj* x_94; obj* x_95; 
x_90 = lean::cnstr_get(x_7, 1);
lean::inc(x_90);
lean::dec(x_7);
x_91 = lean::cnstr_get(x_8, 0);
lean::inc(x_91);
x_92 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_93 = x_8;
} else {
 lean::dec_ref(x_8);
 x_93 = lean::box(0);
}
if (lean::is_scalar(x_93)) {
 x_94 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_94 = x_93;
}
lean::cnstr_set(x_94, 0, x_91);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_92);
x_95 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_90);
return x_95;
}
}
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_parseOctLit___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_6 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_parseOctLit___spec__3(x_5, x_2, x_3, x_4);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseOctLit___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
uint32 x_6; obj* x_7; 
x_6 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_7 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseOctLit___spec__2(x_6, x_2, x_3, x_4, x_5);
lean::dec(x_3);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseOctLit___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
uint32 x_5; obj* x_6; 
x_5 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_6 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseOctLit___spec__1(x_5, x_2, x_3, x_4);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_parseOctLit___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_parseOctLit(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_parseHexLit___spec__3(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_1);
x_8 = l_String_OldIterator_hasNext___main(x_3);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_7);
x_9 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_9;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = l_String_OldIterator_curr___main(x_3);
x_11 = l_Char_isDigit(x_10);
if (x_11 == 0)
{
uint8 x_12; 
x_12 = l_Char_isAlpha(x_10);
if (x_12 == 0)
{
obj* x_13; 
lean::dec(x_7);
x_13 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_13;
}
else
{
obj* x_14; obj* x_15; obj* x_16; 
x_14 = lean::string_push(x_2, x_10);
x_15 = l_String_OldIterator_next___main(x_3);
x_1 = x_7;
x_2 = x_14;
x_3 = x_15;
goto _start;
}
}
else
{
obj* x_17; obj* x_18; obj* x_19; 
x_17 = lean::string_push(x_2, x_10);
x_18 = l_String_OldIterator_next___main(x_3);
x_1 = x_7;
x_2 = x_17;
x_3 = x_18;
goto _start;
}
}
}
else
{
obj* x_20; 
lean::dec(x_1);
x_20 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_20;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseHexLit___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_String_OldIterator_remaining___main(x_3);
x_6 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_parseHexLit___spec__3(x_5, x_1, x_3);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_4);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseHexLit___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; uint8 x_27; 
x_27 = l_String_OldIterator_hasNext___main(x_2);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_28 = lean::box(0);
x_29 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_30 = l_mjoin___rarg___closed__1;
x_31 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_29, x_30, x_28, x_28, x_1, x_2, x_3);
x_32 = lean::cnstr_get(x_31, 0);
lean::inc(x_32);
x_33 = lean::cnstr_get(x_31, 1);
lean::inc(x_33);
lean::dec(x_31);
x_34 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_34, x_32);
x_4 = x_35;
x_5 = x_33;
goto block_26;
}
else
{
uint32 x_36; uint8 x_37; 
x_36 = l_String_OldIterator_curr___main(x_2);
x_37 = l_Char_isDigit(x_36);
if (x_37 == 0)
{
uint8 x_38; 
x_38 = l_Char_isAlpha(x_36);
if (x_38 == 0)
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; 
x_39 = l_Char_quoteCore(x_36);
x_40 = l_Char_HasRepr___closed__1;
x_41 = lean::string_append(x_40, x_39);
lean::dec(x_39);
x_42 = lean::string_append(x_41, x_40);
x_43 = lean::box(0);
x_44 = l_mjoin___rarg___closed__1;
x_45 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_42, x_44, x_43, x_43, x_1, x_2, x_3);
x_46 = lean::cnstr_get(x_45, 0);
lean::inc(x_46);
x_47 = lean::cnstr_get(x_45, 1);
lean::inc(x_47);
lean::dec(x_45);
x_48 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_49 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_48, x_46);
x_4 = x_49;
x_5 = x_47;
goto block_26;
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_50 = l_String_OldIterator_next___main(x_2);
x_51 = lean::box(0);
x_52 = lean::box_uint32(x_36);
x_53 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_50);
lean::cnstr_set(x_53, 2, x_51);
x_4 = x_53;
x_5 = x_3;
goto block_26;
}
}
else
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_54 = l_String_OldIterator_next___main(x_2);
x_55 = lean::box(0);
x_56 = lean::box_uint32(x_36);
x_57 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_54);
lean::cnstr_set(x_57, 2, x_55);
x_4 = x_57;
x_5 = x_3;
goto block_26;
}
}
block_26:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; uint32 x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_6 = lean::cnstr_get(x_4, 0);
lean::inc(x_6);
x_7 = lean::cnstr_get(x_4, 1);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_4, 2);
lean::inc(x_8);
lean::dec(x_4);
x_9 = l_String_splitAux___main___closed__1;
x_10 = lean::unbox_uint32(x_6);
lean::dec(x_6);
x_11 = lean::string_push(x_9, x_10);
x_12 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseHexLit___spec__2(x_11, x_1, x_7, x_5);
x_13 = !lean::is_exclusive(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; 
x_14 = lean::cnstr_get(x_12, 0);
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_8, x_14);
lean::cnstr_set(x_12, 0, x_15);
return x_12;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_16 = lean::cnstr_get(x_12, 0);
x_17 = lean::cnstr_get(x_12, 1);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_12);
x_18 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_8, x_16);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_18);
lean::cnstr_set(x_19, 1, x_17);
return x_19;
}
}
else
{
uint8 x_20; 
x_20 = !lean::is_exclusive(x_4);
if (x_20 == 0)
{
obj* x_21; 
x_21 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_21, 0, x_4);
lean::cnstr_set(x_21, 1, x_5);
return x_21;
}
else
{
obj* x_22; uint8 x_23; obj* x_24; obj* x_25; 
x_22 = lean::cnstr_get(x_4, 0);
x_23 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
lean::inc(x_22);
lean::dec(x_4);
x_24 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set_scalar(x_24, sizeof(void*)*1, x_23);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_5);
return x_25;
}
}
}
}
}
obj* l_Lean_Parser_parseHexLit(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; uint32 x_5; uint32 x_6; obj* x_7; obj* x_8; 
x_4 = 48;
x_5 = 120;
x_6 = 88;
x_7 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6(x_4, x_1, x_2, x_3);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_9 = lean::cnstr_get(x_7, 1);
lean::inc(x_9);
lean::dec(x_7);
x_10 = lean::cnstr_get(x_8, 1);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_8, 2);
lean::inc(x_11);
lean::dec(x_8);
lean::inc(x_10);
x_12 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6(x_5, x_1, x_10, x_9);
x_13 = lean::cnstr_get(x_12, 0);
lean::inc(x_13);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; 
lean::dec(x_10);
x_14 = lean::cnstr_get(x_12, 1);
lean::inc(x_14);
lean::dec(x_12);
x_15 = lean::cnstr_get(x_13, 1);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_13, 2);
lean::inc(x_16);
lean::dec(x_13);
x_17 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseHexLit___spec__1(x_1, x_15, x_14);
x_18 = !lean::is_exclusive(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; 
x_19 = lean::cnstr_get(x_17, 0);
x_20 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_19);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_20);
lean::cnstr_set(x_17, 0, x_21);
return x_17;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_22 = lean::cnstr_get(x_17, 0);
x_23 = lean::cnstr_get(x_17, 1);
lean::inc(x_23);
lean::inc(x_22);
lean::dec(x_17);
x_24 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_22);
x_25 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_24);
x_26 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_26, 0, x_25);
lean::cnstr_set(x_26, 1, x_23);
return x_26;
}
}
else
{
uint8 x_27; 
x_27 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; uint8 x_31; 
x_28 = lean::cnstr_get(x_12, 1);
lean::inc(x_28);
lean::dec(x_12);
x_29 = lean::cnstr_get(x_13, 0);
lean::inc(x_29);
lean::dec(x_13);
x_30 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6(x_6, x_1, x_10, x_28);
x_31 = !lean::is_exclusive(x_30);
if (x_31 == 0)
{
obj* x_32; obj* x_33; obj* x_34; 
x_32 = lean::cnstr_get(x_30, 0);
x_33 = lean::cnstr_get(x_30, 1);
x_34 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_32);
if (lean::obj_tag(x_34) == 0)
{
obj* x_35; obj* x_36; obj* x_37; uint8 x_38; 
lean::free_heap_obj(x_30);
x_35 = lean::cnstr_get(x_34, 1);
lean::inc(x_35);
x_36 = lean::cnstr_get(x_34, 2);
lean::inc(x_36);
lean::dec(x_34);
x_37 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseHexLit___spec__1(x_1, x_35, x_33);
x_38 = !lean::is_exclusive(x_37);
if (x_38 == 0)
{
obj* x_39; obj* x_40; obj* x_41; 
x_39 = lean::cnstr_get(x_37, 0);
x_40 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_36, x_39);
x_41 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_40);
lean::cnstr_set(x_37, 0, x_41);
return x_37;
}
else
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_42 = lean::cnstr_get(x_37, 0);
x_43 = lean::cnstr_get(x_37, 1);
lean::inc(x_43);
lean::inc(x_42);
lean::dec(x_37);
x_44 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_36, x_42);
x_45 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_44);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_43);
return x_46;
}
}
else
{
uint8 x_47; 
x_47 = !lean::is_exclusive(x_34);
if (x_47 == 0)
{
obj* x_48; 
x_48 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_34);
lean::cnstr_set(x_30, 0, x_48);
return x_30;
}
else
{
obj* x_49; uint8 x_50; obj* x_51; obj* x_52; 
x_49 = lean::cnstr_get(x_34, 0);
x_50 = lean::cnstr_get_scalar<uint8>(x_34, sizeof(void*)*1);
lean::inc(x_49);
lean::dec(x_34);
x_51 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set_scalar(x_51, sizeof(void*)*1, x_50);
x_52 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_51);
lean::cnstr_set(x_30, 0, x_52);
return x_30;
}
}
}
else
{
obj* x_53; obj* x_54; obj* x_55; 
x_53 = lean::cnstr_get(x_30, 0);
x_54 = lean::cnstr_get(x_30, 1);
lean::inc(x_54);
lean::inc(x_53);
lean::dec(x_30);
x_55 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_29, x_53);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_56 = lean::cnstr_get(x_55, 1);
lean::inc(x_56);
x_57 = lean::cnstr_get(x_55, 2);
lean::inc(x_57);
lean::dec(x_55);
x_58 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseHexLit___spec__1(x_1, x_56, x_54);
x_59 = lean::cnstr_get(x_58, 0);
lean::inc(x_59);
x_60 = lean::cnstr_get(x_58, 1);
lean::inc(x_60);
if (lean::is_exclusive(x_58)) {
 lean::cnstr_release(x_58, 0);
 lean::cnstr_release(x_58, 1);
 x_61 = x_58;
} else {
 lean::dec_ref(x_58);
 x_61 = lean::box(0);
}
x_62 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_57, x_59);
x_63 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_62);
if (lean::is_scalar(x_61)) {
 x_64 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_64 = x_61;
}
lean::cnstr_set(x_64, 0, x_63);
lean::cnstr_set(x_64, 1, x_60);
return x_64;
}
else
{
obj* x_65; uint8 x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; 
x_65 = lean::cnstr_get(x_55, 0);
lean::inc(x_65);
x_66 = lean::cnstr_get_scalar<uint8>(x_55, sizeof(void*)*1);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 x_67 = x_55;
} else {
 lean::dec_ref(x_55);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_65);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_66);
x_69 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_68);
x_70 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_70, 0, x_69);
lean::cnstr_set(x_70, 1, x_54);
return x_70;
}
}
}
else
{
uint8 x_71; 
lean::dec(x_10);
x_71 = !lean::is_exclusive(x_12);
if (x_71 == 0)
{
obj* x_72; uint8 x_73; 
x_72 = lean::cnstr_get(x_12, 0);
lean::dec(x_72);
x_73 = !lean::is_exclusive(x_13);
if (x_73 == 0)
{
obj* x_74; 
x_74 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_13);
lean::cnstr_set(x_12, 0, x_74);
return x_12;
}
else
{
obj* x_75; obj* x_76; obj* x_77; 
x_75 = lean::cnstr_get(x_13, 0);
lean::inc(x_75);
lean::dec(x_13);
x_76 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set_scalar(x_76, sizeof(void*)*1, x_27);
x_77 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_76);
lean::cnstr_set(x_12, 0, x_77);
return x_12;
}
}
else
{
obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_78 = lean::cnstr_get(x_12, 1);
lean::inc(x_78);
lean::dec(x_12);
x_79 = lean::cnstr_get(x_13, 0);
lean::inc(x_79);
if (lean::is_exclusive(x_13)) {
 lean::cnstr_release(x_13, 0);
 x_80 = x_13;
} else {
 lean::dec_ref(x_13);
 x_80 = lean::box(0);
}
if (lean::is_scalar(x_80)) {
 x_81 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_81 = x_80;
}
lean::cnstr_set(x_81, 0, x_79);
lean::cnstr_set_scalar(x_81, sizeof(void*)*1, x_27);
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_81);
x_83 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_83, 0, x_82);
lean::cnstr_set(x_83, 1, x_78);
return x_83;
}
}
}
}
else
{
uint8 x_84; 
x_84 = !lean::is_exclusive(x_7);
if (x_84 == 0)
{
obj* x_85; uint8 x_86; 
x_85 = lean::cnstr_get(x_7, 0);
lean::dec(x_85);
x_86 = !lean::is_exclusive(x_8);
if (x_86 == 0)
{
return x_7;
}
else
{
obj* x_87; uint8 x_88; obj* x_89; 
x_87 = lean::cnstr_get(x_8, 0);
x_88 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
lean::inc(x_87);
lean::dec(x_8);
x_89 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_89, 0, x_87);
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_88);
lean::cnstr_set(x_7, 0, x_89);
return x_7;
}
}
else
{
obj* x_90; obj* x_91; uint8 x_92; obj* x_93; obj* x_94; obj* x_95; 
x_90 = lean::cnstr_get(x_7, 1);
lean::inc(x_90);
lean::dec(x_7);
x_91 = lean::cnstr_get(x_8, 0);
lean::inc(x_91);
x_92 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_93 = x_8;
} else {
 lean::dec_ref(x_8);
 x_93 = lean::box(0);
}
if (lean::is_scalar(x_93)) {
 x_94 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_94 = x_93;
}
lean::cnstr_set(x_94, 0, x_91);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_92);
x_95 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_95, 0, x_94);
lean::cnstr_set(x_95, 1, x_90);
return x_95;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseHexLit___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_parseHexLit___spec__2(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseHexLit___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_parseHexLit___spec__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_parseHexLit___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_parseHexLit(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* _init_l_Lean_Parser_number() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("number");
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
obj* _init_l_Lean_Parser_number_HasView_x27___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_nat_obj(0u);
x_4 = lean_name_mk_numeral(x_2, x_3);
x_5 = lean::box(3);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
x_7 = l_Lean_Parser_Syntax_mkNode(x_4, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_number;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_number_HasView_x27___elambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_nat_obj(1u);
x_4 = lean_name_mk_numeral(x_2, x_3);
x_5 = lean::box(3);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
x_7 = l_Lean_Parser_Syntax_mkNode(x_4, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_number;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_number_HasView_x27___elambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_nat_obj(2u);
x_4 = lean_name_mk_numeral(x_2, x_3);
x_5 = lean::box(3);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
x_7 = l_Lean_Parser_Syntax_mkNode(x_4, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_number;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_number_HasView_x27___elambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(2u);
x_3 = lean_name_mk_numeral(x_1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_number_HasView_x27___elambda__1___closed__5() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_1 = lean::box(0);
x_2 = lean::box(0);
x_3 = lean::mk_nat_obj(3u);
x_4 = lean_name_mk_numeral(x_2, x_3);
x_5 = lean::box(3);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
x_7 = l_Lean_Parser_Syntax_mkNode(x_4, x_6);
x_8 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_1);
x_9 = l_Lean_Parser_number;
x_10 = l_Lean_Parser_Syntax_mkNode(x_9, x_8);
return x_10;
}
}
obj* _init_l_Lean_Parser_number_HasView_x27___elambda__1___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_nat_obj(3u);
x_3 = lean_name_mk_numeral(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_number_HasView_x27___elambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::box(0);
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_3; 
x_3 = lean::cnstr_get(x_1, 0);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; 
x_4 = l_Lean_Parser_number_HasView_x27___elambda__1___closed__1;
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_5 = lean::cnstr_get(x_3, 0);
lean::inc(x_5);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_2);
x_8 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__1;
x_9 = l_Lean_Parser_Syntax_mkNode(x_8, x_7);
x_10 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_2);
x_11 = l_Lean_Parser_number;
x_12 = l_Lean_Parser_Syntax_mkNode(x_11, x_10);
return x_12;
}
}
case 1:
{
obj* x_13; 
x_13 = lean::cnstr_get(x_1, 0);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
x_14 = l_Lean_Parser_number_HasView_x27___elambda__1___closed__2;
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
x_16 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_2);
x_18 = l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__3;
x_19 = l_Lean_Parser_Syntax_mkNode(x_18, x_17);
x_20 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_2);
x_21 = l_Lean_Parser_number;
x_22 = l_Lean_Parser_Syntax_mkNode(x_21, x_20);
return x_22;
}
}
case 2:
{
obj* x_23; 
x_23 = lean::cnstr_get(x_1, 0);
if (lean::obj_tag(x_23) == 0)
{
obj* x_24; 
x_24 = l_Lean_Parser_number_HasView_x27___elambda__1___closed__3;
return x_24;
}
else
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_25 = lean::cnstr_get(x_23, 0);
lean::inc(x_25);
x_26 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_26, 0, x_25);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_2);
x_28 = l_Lean_Parser_number_HasView_x27___elambda__1___closed__4;
x_29 = l_Lean_Parser_Syntax_mkNode(x_28, x_27);
x_30 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_2);
x_31 = l_Lean_Parser_number;
x_32 = l_Lean_Parser_Syntax_mkNode(x_31, x_30);
return x_32;
}
}
default: 
{
obj* x_33; 
x_33 = lean::cnstr_get(x_1, 0);
if (lean::obj_tag(x_33) == 0)
{
obj* x_34; 
x_34 = l_Lean_Parser_number_HasView_x27___elambda__1___closed__5;
return x_34;
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
x_35 = lean::cnstr_get(x_33, 0);
lean::inc(x_35);
x_36 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_36, 0, x_35);
x_37 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_2);
x_38 = l_Lean_Parser_number_HasView_x27___elambda__1___closed__6;
x_39 = l_Lean_Parser_Syntax_mkNode(x_38, x_37);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_2);
x_41 = l_Lean_Parser_number;
x_42 = l_Lean_Parser_Syntax_mkNode(x_41, x_40);
return x_42;
}
}
}
}
}
obj* _init_l_Lean_Parser_number_HasView_x27___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_number_HasView_x27___lambda__1___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_number_HasView_x27___lambda__1___closed__3() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_number_HasView_x27___lambda__1___closed__4() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::box(0);
x_2 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_number_HasView_x27___lambda__1___closed__5() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__4;
return x_1;
}
}
obj* _init_l_Lean_Parser_number_HasView_x27___lambda__1___closed__6() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("number");
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
obj* l_Lean_Parser_number_HasView_x27___lambda__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_2);
x_3 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__5;
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_4, 1);
lean::inc(x_6);
lean::dec(x_4);
x_7 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__6;
x_8 = lean_name_dec_eq(x_5, x_7);
lean::dec(x_5);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_6);
x_9 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__5;
return x_9;
}
else
{
if (lean::obj_tag(x_6) == 0)
{
obj* x_10; 
lean::dec(x_6);
x_10 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__5;
return x_10;
}
else
{
obj* x_11; 
x_11 = lean::cnstr_get(x_6, 1);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
obj* x_12; obj* x_13; 
lean::dec(x_11);
x_12 = lean::cnstr_get(x_6, 0);
lean::inc(x_12);
lean::dec(x_6);
x_13 = l_Lean_Parser_Syntax_asNode___main(x_12);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
lean::dec(x_13);
x_14 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__5;
return x_14;
}
else
{
uint8 x_15; 
x_15 = !lean::is_exclusive(x_13);
if (x_15 == 0)
{
obj* x_16; obj* x_17; 
x_16 = lean::cnstr_get(x_13, 0);
x_17 = lean::cnstr_get(x_16, 0);
lean::inc(x_17);
switch (lean::obj_tag(x_17)) {
case 0:
{
obj* x_18; 
lean::dec(x_17);
lean::free_heap_obj(x_13);
lean::dec(x_16);
x_18 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__5;
return x_18;
}
case 1:
{
obj* x_19; 
lean::dec(x_17);
lean::free_heap_obj(x_13);
lean::dec(x_16);
x_19 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__5;
return x_19;
}
default: 
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; uint8 x_24; 
x_20 = lean::cnstr_get(x_16, 1);
lean::inc(x_20);
lean::dec(x_16);
x_21 = lean::cnstr_get(x_17, 0);
lean::inc(x_21);
x_22 = lean::cnstr_get(x_17, 1);
lean::inc(x_22);
lean::dec(x_17);
x_23 = lean::box(0);
x_24 = lean_name_dec_eq(x_21, x_23);
lean::dec(x_21);
if (x_24 == 0)
{
obj* x_25; 
lean::dec(x_22);
lean::dec(x_20);
lean::free_heap_obj(x_13);
x_25 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__5;
return x_25;
}
else
{
if (lean::obj_tag(x_20) == 0)
{
obj* x_26; 
lean::dec(x_22);
lean::dec(x_20);
lean::free_heap_obj(x_13);
x_26 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__5;
return x_26;
}
else
{
obj* x_27; 
x_27 = lean::cnstr_get(x_20, 1);
lean::inc(x_27);
if (lean::obj_tag(x_27) == 0)
{
obj* x_28; obj* x_29; uint8 x_30; 
lean::dec(x_27);
x_28 = lean::cnstr_get(x_20, 0);
lean::inc(x_28);
lean::dec(x_20);
x_29 = lean::mk_nat_obj(0u);
x_30 = lean::nat_dec_eq(x_22, x_29);
if (x_30 == 0)
{
obj* x_31; uint8 x_32; 
x_31 = lean::mk_nat_obj(1u);
x_32 = lean::nat_dec_eq(x_22, x_31);
if (x_32 == 0)
{
obj* x_33; uint8 x_34; 
x_33 = lean::mk_nat_obj(2u);
x_34 = lean::nat_dec_eq(x_22, x_33);
lean::dec(x_22);
if (x_34 == 0)
{
if (lean::obj_tag(x_28) == 0)
{
obj* x_35; obj* x_36; 
x_35 = lean::cnstr_get(x_28, 0);
lean::inc(x_35);
lean::dec(x_28);
lean::cnstr_set(x_13, 0, x_35);
x_36 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_36, 0, x_13);
return x_36;
}
else
{
obj* x_37; 
lean::dec(x_28);
lean::free_heap_obj(x_13);
x_37 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__1;
return x_37;
}
}
else
{
if (lean::obj_tag(x_28) == 0)
{
obj* x_38; obj* x_39; 
x_38 = lean::cnstr_get(x_28, 0);
lean::inc(x_38);
lean::dec(x_28);
lean::cnstr_set(x_13, 0, x_38);
x_39 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_39, 0, x_13);
return x_39;
}
else
{
obj* x_40; 
lean::dec(x_28);
lean::free_heap_obj(x_13);
x_40 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__2;
return x_40;
}
}
}
else
{
lean::dec(x_22);
if (lean::obj_tag(x_28) == 0)
{
obj* x_41; obj* x_42; 
x_41 = lean::cnstr_get(x_28, 0);
lean::inc(x_41);
lean::dec(x_28);
lean::cnstr_set(x_13, 0, x_41);
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_13);
return x_42;
}
else
{
obj* x_43; 
lean::dec(x_28);
lean::free_heap_obj(x_13);
x_43 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__3;
return x_43;
}
}
}
else
{
lean::dec(x_22);
if (lean::obj_tag(x_28) == 0)
{
obj* x_44; obj* x_45; 
x_44 = lean::cnstr_get(x_28, 0);
lean::inc(x_44);
lean::dec(x_28);
lean::cnstr_set(x_13, 0, x_44);
x_45 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_45, 0, x_13);
return x_45;
}
else
{
obj* x_46; 
lean::dec(x_28);
lean::free_heap_obj(x_13);
x_46 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__4;
return x_46;
}
}
}
else
{
obj* x_47; 
lean::dec(x_27);
lean::dec(x_22);
lean::dec(x_20);
lean::free_heap_obj(x_13);
x_47 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__5;
return x_47;
}
}
}
}
}
}
else
{
obj* x_48; obj* x_49; 
x_48 = lean::cnstr_get(x_13, 0);
lean::inc(x_48);
lean::dec(x_13);
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
switch (lean::obj_tag(x_49)) {
case 0:
{
obj* x_50; 
lean::dec(x_49);
lean::dec(x_48);
x_50 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__5;
return x_50;
}
case 1:
{
obj* x_51; 
lean::dec(x_49);
lean::dec(x_48);
x_51 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__5;
return x_51;
}
default: 
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; uint8 x_56; 
x_52 = lean::cnstr_get(x_48, 1);
lean::inc(x_52);
lean::dec(x_48);
x_53 = lean::cnstr_get(x_49, 0);
lean::inc(x_53);
x_54 = lean::cnstr_get(x_49, 1);
lean::inc(x_54);
lean::dec(x_49);
x_55 = lean::box(0);
x_56 = lean_name_dec_eq(x_53, x_55);
lean::dec(x_53);
if (x_56 == 0)
{
obj* x_57; 
lean::dec(x_54);
lean::dec(x_52);
x_57 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__5;
return x_57;
}
else
{
if (lean::obj_tag(x_52) == 0)
{
obj* x_58; 
lean::dec(x_54);
lean::dec(x_52);
x_58 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__5;
return x_58;
}
else
{
obj* x_59; 
x_59 = lean::cnstr_get(x_52, 1);
lean::inc(x_59);
if (lean::obj_tag(x_59) == 0)
{
obj* x_60; obj* x_61; uint8 x_62; 
lean::dec(x_59);
x_60 = lean::cnstr_get(x_52, 0);
lean::inc(x_60);
lean::dec(x_52);
x_61 = lean::mk_nat_obj(0u);
x_62 = lean::nat_dec_eq(x_54, x_61);
if (x_62 == 0)
{
obj* x_63; uint8 x_64; 
x_63 = lean::mk_nat_obj(1u);
x_64 = lean::nat_dec_eq(x_54, x_63);
if (x_64 == 0)
{
obj* x_65; uint8 x_66; 
x_65 = lean::mk_nat_obj(2u);
x_66 = lean::nat_dec_eq(x_54, x_65);
lean::dec(x_54);
if (x_66 == 0)
{
if (lean::obj_tag(x_60) == 0)
{
obj* x_67; obj* x_68; obj* x_69; 
x_67 = lean::cnstr_get(x_60, 0);
lean::inc(x_67);
lean::dec(x_60);
x_68 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_68, 0, x_67);
x_69 = lean::alloc_cnstr(3, 1, 0);
lean::cnstr_set(x_69, 0, x_68);
return x_69;
}
else
{
obj* x_70; 
lean::dec(x_60);
x_70 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__1;
return x_70;
}
}
else
{
if (lean::obj_tag(x_60) == 0)
{
obj* x_71; obj* x_72; obj* x_73; 
x_71 = lean::cnstr_get(x_60, 0);
lean::inc(x_71);
lean::dec(x_60);
x_72 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_72, 0, x_71);
x_73 = lean::alloc_cnstr(2, 1, 0);
lean::cnstr_set(x_73, 0, x_72);
return x_73;
}
else
{
obj* x_74; 
lean::dec(x_60);
x_74 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__2;
return x_74;
}
}
}
else
{
lean::dec(x_54);
if (lean::obj_tag(x_60) == 0)
{
obj* x_75; obj* x_76; obj* x_77; 
x_75 = lean::cnstr_get(x_60, 0);
lean::inc(x_75);
lean::dec(x_60);
x_76 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_76, 0, x_75);
x_77 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_77, 0, x_76);
return x_77;
}
else
{
obj* x_78; 
lean::dec(x_60);
x_78 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__3;
return x_78;
}
}
}
else
{
lean::dec(x_54);
if (lean::obj_tag(x_60) == 0)
{
obj* x_79; obj* x_80; obj* x_81; 
x_79 = lean::cnstr_get(x_60, 0);
lean::inc(x_79);
lean::dec(x_60);
x_80 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_80, 0, x_79);
x_81 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_81, 0, x_80);
return x_81;
}
else
{
obj* x_82; 
lean::dec(x_60);
x_82 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__4;
return x_82;
}
}
}
else
{
obj* x_83; 
lean::dec(x_59);
lean::dec(x_54);
lean::dec(x_52);
x_83 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__5;
return x_83;
}
}
}
}
}
}
}
}
else
{
obj* x_84; 
lean::dec(x_11);
lean::dec(x_6);
x_84 = l_Lean_Parser_number_HasView_x27___lambda__1___closed__5;
return x_84;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_number_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_HasView_x27___lambda__1), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_HasView_x27___elambda__1___boxed), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_number_HasView_x27___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_number_HasView_x27___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_number_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_number_HasView_x27;
return x_1;
}
}
obj* l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_number_x27___spec__3(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; uint8 x_8; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
lean::dec(x_1);
x_8 = l_String_OldIterator_hasNext___main(x_3);
if (x_8 == 0)
{
obj* x_9; 
lean::dec(x_7);
x_9 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_9;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = l_String_OldIterator_curr___main(x_3);
x_11 = l_Char_isDigit(x_10);
if (x_11 == 0)
{
obj* x_12; 
lean::dec(x_7);
x_12 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; 
x_13 = lean::string_push(x_2, x_10);
x_14 = l_String_OldIterator_next___main(x_3);
x_1 = x_7;
x_2 = x_13;
x_3 = x_14;
goto _start;
}
}
}
else
{
obj* x_16; 
lean::dec(x_1);
x_16 = l___private_init_lean_parser_parsec_4__mkStringResult___rarg(x_2, x_3);
return x_16;
}
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x27___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
x_5 = l_String_OldIterator_remaining___main(x_3);
x_6 = l___private_init_lean_parser_parsec_5__takeWhileAux___main___at_Lean_Parser_number_x27___spec__3(x_5, x_1, x_3);
x_7 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_7, 0, x_6);
lean::cnstr_set(x_7, 1, x_4);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_number_x27___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_String_OldIterator_hasNext___main(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_5 = lean::box(0);
x_6 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_7 = l_mjoin___rarg___closed__1;
x_8 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_6, x_7, x_5, x_5, x_1, x_2, x_3);
x_9 = !lean::is_exclusive(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_10 = lean::cnstr_get(x_8, 0);
x_11 = lean::cnstr_get(x_8, 1);
x_12 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_13 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_10);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint32 x_18; obj* x_19; obj* x_20; uint8 x_21; 
lean::free_heap_obj(x_8);
x_14 = lean::cnstr_get(x_13, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_13, 1);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_13, 2);
lean::inc(x_16);
lean::dec(x_13);
x_17 = l_String_splitAux___main___closed__1;
x_18 = lean::unbox_uint32(x_14);
lean::dec(x_14);
x_19 = lean::string_push(x_17, x_18);
x_20 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x27___spec__2(x_19, x_1, x_15, x_11);
x_21 = !lean::is_exclusive(x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_23; 
x_22 = lean::cnstr_get(x_20, 0);
x_23 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_22);
lean::cnstr_set(x_20, 0, x_23);
return x_20;
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_24 = lean::cnstr_get(x_20, 0);
x_25 = lean::cnstr_get(x_20, 1);
lean::inc(x_25);
lean::inc(x_24);
lean::dec(x_20);
x_26 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_24);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8 x_28; 
x_28 = !lean::is_exclusive(x_13);
if (x_28 == 0)
{
lean::cnstr_set(x_8, 0, x_13);
return x_8;
}
else
{
obj* x_29; uint8 x_30; obj* x_31; 
x_29 = lean::cnstr_get(x_13, 0);
x_30 = lean::cnstr_get_scalar<uint8>(x_13, sizeof(void*)*1);
lean::inc(x_29);
lean::dec(x_13);
x_31 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_31, 0, x_29);
lean::cnstr_set_scalar(x_31, sizeof(void*)*1, x_30);
lean::cnstr_set(x_8, 0, x_31);
return x_8;
}
}
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_32 = lean::cnstr_get(x_8, 0);
x_33 = lean::cnstr_get(x_8, 1);
lean::inc(x_33);
lean::inc(x_32);
lean::dec(x_8);
x_34 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_34, x_32);
if (lean::obj_tag(x_35) == 0)
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; uint32 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_36 = lean::cnstr_get(x_35, 0);
lean::inc(x_36);
x_37 = lean::cnstr_get(x_35, 1);
lean::inc(x_37);
x_38 = lean::cnstr_get(x_35, 2);
lean::inc(x_38);
lean::dec(x_35);
x_39 = l_String_splitAux___main___closed__1;
x_40 = lean::unbox_uint32(x_36);
lean::dec(x_36);
x_41 = lean::string_push(x_39, x_40);
x_42 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x27___spec__2(x_41, x_1, x_37, x_33);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_42, 1);
lean::inc(x_44);
if (lean::is_exclusive(x_42)) {
 lean::cnstr_release(x_42, 0);
 lean::cnstr_release(x_42, 1);
 x_45 = x_42;
} else {
 lean::dec_ref(x_42);
 x_45 = lean::box(0);
}
x_46 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_38, x_43);
if (lean::is_scalar(x_45)) {
 x_47 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_47 = x_45;
}
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_44);
return x_47;
}
else
{
obj* x_48; uint8 x_49; obj* x_50; obj* x_51; obj* x_52; 
x_48 = lean::cnstr_get(x_35, 0);
lean::inc(x_48);
x_49 = lean::cnstr_get_scalar<uint8>(x_35, sizeof(void*)*1);
if (lean::is_exclusive(x_35)) {
 lean::cnstr_release(x_35, 0);
 x_50 = x_35;
} else {
 lean::dec_ref(x_35);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_48);
lean::cnstr_set_scalar(x_51, sizeof(void*)*1, x_49);
x_52 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_33);
return x_52;
}
}
}
else
{
uint32 x_53; uint8 x_54; 
x_53 = l_String_OldIterator_curr___main(x_2);
x_54 = l_Char_isDigit(x_53);
if (x_54 == 0)
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; uint8 x_62; 
x_55 = l_Char_quoteCore(x_53);
x_56 = l_Char_HasRepr___closed__1;
x_57 = lean::string_append(x_56, x_55);
lean::dec(x_55);
x_58 = lean::string_append(x_57, x_56);
x_59 = lean::box(0);
x_60 = l_mjoin___rarg___closed__1;
x_61 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_58, x_60, x_59, x_59, x_1, x_2, x_3);
x_62 = !lean::is_exclusive(x_61);
if (x_62 == 0)
{
obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_63 = lean::cnstr_get(x_61, 0);
x_64 = lean::cnstr_get(x_61, 1);
x_65 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_66 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_65, x_63);
if (lean::obj_tag(x_66) == 0)
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; uint32 x_71; obj* x_72; obj* x_73; uint8 x_74; 
lean::free_heap_obj(x_61);
x_67 = lean::cnstr_get(x_66, 0);
lean::inc(x_67);
x_68 = lean::cnstr_get(x_66, 1);
lean::inc(x_68);
x_69 = lean::cnstr_get(x_66, 2);
lean::inc(x_69);
lean::dec(x_66);
x_70 = l_String_splitAux___main___closed__1;
x_71 = lean::unbox_uint32(x_67);
lean::dec(x_67);
x_72 = lean::string_push(x_70, x_71);
x_73 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x27___spec__2(x_72, x_1, x_68, x_64);
x_74 = !lean::is_exclusive(x_73);
if (x_74 == 0)
{
obj* x_75; obj* x_76; 
x_75 = lean::cnstr_get(x_73, 0);
x_76 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_69, x_75);
lean::cnstr_set(x_73, 0, x_76);
return x_73;
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_77 = lean::cnstr_get(x_73, 0);
x_78 = lean::cnstr_get(x_73, 1);
lean::inc(x_78);
lean::inc(x_77);
lean::dec(x_73);
x_79 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_69, x_77);
x_80 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_78);
return x_80;
}
}
else
{
uint8 x_81; 
x_81 = !lean::is_exclusive(x_66);
if (x_81 == 0)
{
lean::cnstr_set(x_61, 0, x_66);
return x_61;
}
else
{
obj* x_82; uint8 x_83; obj* x_84; 
x_82 = lean::cnstr_get(x_66, 0);
x_83 = lean::cnstr_get_scalar<uint8>(x_66, sizeof(void*)*1);
lean::inc(x_82);
lean::dec(x_66);
x_84 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_84, 0, x_82);
lean::cnstr_set_scalar(x_84, sizeof(void*)*1, x_83);
lean::cnstr_set(x_61, 0, x_84);
return x_61;
}
}
}
else
{
obj* x_85; obj* x_86; obj* x_87; obj* x_88; 
x_85 = lean::cnstr_get(x_61, 0);
x_86 = lean::cnstr_get(x_61, 1);
lean::inc(x_86);
lean::inc(x_85);
lean::dec(x_61);
x_87 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_88 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_87, x_85);
if (lean::obj_tag(x_88) == 0)
{
obj* x_89; obj* x_90; obj* x_91; obj* x_92; uint32 x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_89 = lean::cnstr_get(x_88, 0);
lean::inc(x_89);
x_90 = lean::cnstr_get(x_88, 1);
lean::inc(x_90);
x_91 = lean::cnstr_get(x_88, 2);
lean::inc(x_91);
lean::dec(x_88);
x_92 = l_String_splitAux___main___closed__1;
x_93 = lean::unbox_uint32(x_89);
lean::dec(x_89);
x_94 = lean::string_push(x_92, x_93);
x_95 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x27___spec__2(x_94, x_1, x_90, x_86);
x_96 = lean::cnstr_get(x_95, 0);
lean::inc(x_96);
x_97 = lean::cnstr_get(x_95, 1);
lean::inc(x_97);
if (lean::is_exclusive(x_95)) {
 lean::cnstr_release(x_95, 0);
 lean::cnstr_release(x_95, 1);
 x_98 = x_95;
} else {
 lean::dec_ref(x_95);
 x_98 = lean::box(0);
}
x_99 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_91, x_96);
if (lean::is_scalar(x_98)) {
 x_100 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_100 = x_98;
}
lean::cnstr_set(x_100, 0, x_99);
lean::cnstr_set(x_100, 1, x_97);
return x_100;
}
else
{
obj* x_101; uint8 x_102; obj* x_103; obj* x_104; obj* x_105; 
x_101 = lean::cnstr_get(x_88, 0);
lean::inc(x_101);
x_102 = lean::cnstr_get_scalar<uint8>(x_88, sizeof(void*)*1);
if (lean::is_exclusive(x_88)) {
 lean::cnstr_release(x_88, 0);
 x_103 = x_88;
} else {
 lean::dec_ref(x_88);
 x_103 = lean::box(0);
}
if (lean::is_scalar(x_103)) {
 x_104 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_104 = x_103;
}
lean::cnstr_set(x_104, 0, x_101);
lean::cnstr_set_scalar(x_104, sizeof(void*)*1, x_102);
x_105 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_86);
return x_105;
}
}
}
else
{
obj* x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; uint8 x_111; 
x_106 = l_String_OldIterator_next___main(x_2);
x_107 = lean::box(0);
x_108 = l_String_splitAux___main___closed__1;
x_109 = lean::string_push(x_108, x_53);
x_110 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x27___spec__2(x_109, x_1, x_106, x_3);
x_111 = !lean::is_exclusive(x_110);
if (x_111 == 0)
{
obj* x_112; obj* x_113; 
x_112 = lean::cnstr_get(x_110, 0);
x_113 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_107, x_112);
lean::cnstr_set(x_110, 0, x_113);
return x_110;
}
else
{
obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
x_114 = lean::cnstr_get(x_110, 0);
x_115 = lean::cnstr_get(x_110, 1);
lean::inc(x_115);
lean::inc(x_114);
lean::dec(x_110);
x_116 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_107, x_114);
x_117 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_117, 0, x_116);
lean::cnstr_set(x_117, 1, x_115);
return x_117;
}
}
}
}
}
obj* l_List_map___main___at_Lean_Parser_number_x27___spec__5___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = lean::cnstr_get(x_1, 0);
lean::inc(x_5);
x_6 = lean::cnstr_get(x_1, 1);
lean::inc(x_6);
lean::dec(x_1);
x_7 = lean::apply_3(x_6, x_2, x_3, x_4);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_7);
if (x_9 == 0)
{
obj* x_10; uint8 x_11; 
x_10 = lean::cnstr_get(x_7, 0);
lean::dec(x_10);
x_11 = !lean::is_exclusive(x_8);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_12 = lean::cnstr_get(x_8, 0);
x_13 = lean::cnstr_get(x_8, 2);
x_14 = lean::box(0);
x_15 = lean_name_mk_numeral(x_14, x_5);
x_16 = lean::box(0);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_12);
lean::cnstr_set(x_17, 1, x_16);
x_18 = l_Lean_Parser_Syntax_mkNode(x_15, x_17);
x_19 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_8, 2, x_19);
lean::cnstr_set(x_8, 0, x_18);
x_20 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_8);
lean::cnstr_set(x_7, 0, x_20);
return x_7;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_21 = lean::cnstr_get(x_8, 0);
x_22 = lean::cnstr_get(x_8, 1);
x_23 = lean::cnstr_get(x_8, 2);
lean::inc(x_23);
lean::inc(x_22);
lean::inc(x_21);
lean::dec(x_8);
x_24 = lean::box(0);
x_25 = lean_name_mk_numeral(x_24, x_5);
x_26 = lean::box(0);
x_27 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_27, 0, x_21);
lean::cnstr_set(x_27, 1, x_26);
x_28 = l_Lean_Parser_Syntax_mkNode(x_25, x_27);
x_29 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_30 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set(x_30, 1, x_22);
lean::cnstr_set(x_30, 2, x_29);
x_31 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_23, x_30);
lean::cnstr_set(x_7, 0, x_31);
return x_7;
}
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_32 = lean::cnstr_get(x_7, 1);
lean::inc(x_32);
lean::dec(x_7);
x_33 = lean::cnstr_get(x_8, 0);
lean::inc(x_33);
x_34 = lean::cnstr_get(x_8, 1);
lean::inc(x_34);
x_35 = lean::cnstr_get(x_8, 2);
lean::inc(x_35);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 x_36 = x_8;
} else {
 lean::dec_ref(x_8);
 x_36 = lean::box(0);
}
x_37 = lean::box(0);
x_38 = lean_name_mk_numeral(x_37, x_5);
x_39 = lean::box(0);
x_40 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_40, 0, x_33);
lean::cnstr_set(x_40, 1, x_39);
x_41 = l_Lean_Parser_Syntax_mkNode(x_38, x_40);
x_42 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_36)) {
 x_43 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_43 = x_36;
}
lean::cnstr_set(x_43, 0, x_41);
lean::cnstr_set(x_43, 1, x_34);
lean::cnstr_set(x_43, 2, x_42);
x_44 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_35, x_43);
x_45 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_45, 0, x_44);
lean::cnstr_set(x_45, 1, x_32);
return x_45;
}
}
else
{
uint8 x_46; 
lean::dec(x_5);
x_46 = !lean::is_exclusive(x_7);
if (x_46 == 0)
{
obj* x_47; uint8 x_48; 
x_47 = lean::cnstr_get(x_7, 0);
lean::dec(x_47);
x_48 = !lean::is_exclusive(x_8);
if (x_48 == 0)
{
return x_7;
}
else
{
obj* x_49; uint8 x_50; obj* x_51; 
x_49 = lean::cnstr_get(x_8, 0);
x_50 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
lean::inc(x_49);
lean::dec(x_8);
x_51 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set_scalar(x_51, sizeof(void*)*1, x_50);
lean::cnstr_set(x_7, 0, x_51);
return x_7;
}
}
else
{
obj* x_52; obj* x_53; uint8 x_54; obj* x_55; obj* x_56; obj* x_57; 
x_52 = lean::cnstr_get(x_7, 1);
lean::inc(x_52);
lean::dec(x_7);
x_53 = lean::cnstr_get(x_8, 0);
lean::inc(x_53);
x_54 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_55 = x_8;
} else {
 lean::dec_ref(x_8);
 x_55 = lean::box(0);
}
if (lean::is_scalar(x_55)) {
 x_56 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_56 = x_55;
}
lean::cnstr_set(x_56, 0, x_53);
lean::cnstr_set_scalar(x_56, sizeof(void*)*1, x_54);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_52);
return x_57;
}
}
}
}
obj* l_List_map___main___at_Lean_Parser_number_x27___spec__5(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
lean::dec(x_1);
x_2 = lean::box(0);
return x_2;
}
else
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_Lean_Parser_number_x27___spec__5___lambda__1), 4, 1);
lean::closure_set(x_6, 0, x_4);
x_7 = l_List_map___main___at_Lean_Parser_number_x27___spec__5(x_5);
lean::cnstr_set(x_1, 1, x_7);
lean::cnstr_set(x_1, 0, x_6);
return x_1;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_8 = lean::cnstr_get(x_1, 0);
x_9 = lean::cnstr_get(x_1, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_1);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_List_map___main___at_Lean_Parser_number_x27___spec__5___lambda__1), 4, 1);
lean::closure_set(x_10, 0, x_8);
x_11 = l_List_map___main___at_Lean_Parser_number_x27___spec__5(x_9);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
return x_12;
}
}
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_number_x27___spec__7___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7) {
_start:
{
obj* x_8; obj* x_9; obj* x_21; obj* x_22; obj* x_27; obj* x_28; 
lean::inc(x_6);
x_27 = lean::apply_3(x_3, x_5, x_6, x_7);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
if (lean::obj_tag(x_28) == 0)
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_29 = lean::cnstr_get(x_27, 1);
lean::inc(x_29);
lean::dec(x_27);
x_30 = lean::cnstr_get(x_28, 0);
lean::inc(x_30);
x_31 = lean::cnstr_get(x_28, 1);
lean::inc(x_31);
x_32 = lean::cnstr_get(x_28, 2);
lean::inc(x_32);
if (lean::is_exclusive(x_28)) {
 lean::cnstr_release(x_28, 0);
 lean::cnstr_release(x_28, 1);
 lean::cnstr_release(x_28, 2);
 x_33 = x_28;
} else {
 lean::dec_ref(x_28);
 x_33 = lean::box(0);
}
if (lean::obj_tag(x_4) == 0)
{
obj* x_44; 
x_44 = lean::cnstr_get(x_4, 2);
lean::inc(x_44);
if (lean::obj_tag(x_44) == 0)
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; uint8 x_49; 
lean::dec(x_33);
x_45 = lean::cnstr_get(x_4, 0);
lean::inc(x_45);
x_46 = lean::cnstr_get(x_4, 1);
lean::inc(x_46);
x_47 = lean::cnstr_get(x_31, 1);
lean::inc(x_47);
x_48 = lean::cnstr_get(x_46, 1);
lean::inc(x_48);
lean::dec(x_46);
x_49 = lean::nat_dec_lt(x_47, x_48);
if (x_49 == 0)
{
uint8 x_50; 
x_50 = lean::nat_dec_lt(x_48, x_47);
lean::dec(x_47);
lean::dec(x_48);
if (x_50 == 0)
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; 
x_51 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_51, 0, x_30);
lean::cnstr_set(x_51, 1, x_45);
lean::inc(x_31);
x_52 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_52, 0, x_51);
lean::cnstr_set(x_52, 1, x_31);
lean::cnstr_set(x_52, 2, x_44);
lean::inc(x_1);
x_53 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_53, 0, x_1);
lean::closure_set(x_53, 1, x_1);
x_54 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_54, 0, x_53);
x_55 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_55, 0, x_52);
lean::cnstr_set(x_55, 1, x_31);
lean::cnstr_set(x_55, 2, x_54);
x_56 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_32, x_55);
x_21 = x_56;
x_22 = x_29;
goto block_26;
}
else
{
obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
lean::dec(x_45);
x_57 = lean::box(0);
x_58 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_58, 0, x_30);
lean::cnstr_set(x_58, 1, x_57);
lean::inc(x_31);
x_59 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_31);
lean::cnstr_set(x_59, 2, x_44);
lean::inc(x_1);
x_60 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_60, 0, x_1);
lean::closure_set(x_60, 1, x_1);
x_61 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_61, 0, x_60);
x_62 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_62, 0, x_59);
lean::cnstr_set(x_62, 1, x_31);
lean::cnstr_set(x_62, 2, x_61);
x_63 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_32, x_62);
x_21 = x_63;
x_22 = x_29;
goto block_26;
}
}
else
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
lean::dec(x_48);
lean::dec(x_47);
lean::dec(x_45);
lean::dec(x_30);
lean::inc(x_1);
x_64 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_64, 0, x_1);
lean::closure_set(x_64, 1, x_1);
x_65 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_65, 0, x_64);
lean::inc(x_4);
x_66 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_66, 0, x_4);
lean::cnstr_set(x_66, 1, x_31);
lean::cnstr_set(x_66, 2, x_65);
x_67 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_32, x_66);
x_21 = x_67;
x_22 = x_29;
goto block_26;
}
}
else
{
obj* x_68; 
lean::dec(x_44);
x_68 = lean::box(0);
x_34 = x_68;
goto block_43;
}
}
else
{
obj* x_69; 
x_69 = lean::box(0);
x_34 = x_69;
goto block_43;
}
block_43:
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_34);
x_35 = lean::box(0);
x_36 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_36, 0, x_30);
lean::cnstr_set(x_36, 1, x_35);
x_37 = lean::box(0);
lean::inc(x_31);
if (lean::is_scalar(x_33)) {
 x_38 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_38 = x_33;
}
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set(x_38, 1, x_31);
lean::cnstr_set(x_38, 2, x_37);
lean::inc(x_1);
x_39 = lean::alloc_closure(reinterpret_cast<void*>(l_Function_comp___rarg), 3, 2);
lean::closure_set(x_39, 0, x_1);
lean::closure_set(x_39, 1, x_1);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_39);
x_41 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_41, 0, x_38);
lean::cnstr_set(x_41, 1, x_31);
lean::cnstr_set(x_41, 2, x_40);
x_42 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_32, x_41);
x_21 = x_42;
x_22 = x_29;
goto block_26;
}
}
else
{
obj* x_70; uint8 x_71; 
lean::dec(x_1);
x_70 = lean::cnstr_get(x_27, 1);
lean::inc(x_70);
lean::dec(x_27);
x_71 = !lean::is_exclusive(x_28);
if (x_71 == 0)
{
x_21 = x_28;
x_22 = x_70;
goto block_26;
}
else
{
obj* x_72; uint8 x_73; obj* x_74; 
x_72 = lean::cnstr_get(x_28, 0);
x_73 = lean::cnstr_get_scalar<uint8>(x_28, sizeof(void*)*1);
lean::inc(x_72);
lean::dec(x_28);
x_74 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_74, 0, x_72);
lean::cnstr_set_scalar(x_74, sizeof(void*)*1, x_73);
x_21 = x_74;
x_22 = x_70;
goto block_26;
}
}
block_20:
{
if (lean::obj_tag(x_8) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_8);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_8, 2);
lean::dec(x_11);
x_12 = lean::cnstr_get(x_8, 1);
lean::dec(x_12);
x_13 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_8, 2, x_13);
lean::cnstr_set(x_8, 1, x_6);
x_14 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_14, 0, x_8);
lean::cnstr_set(x_14, 1, x_9);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_8, 0);
lean::inc(x_15);
lean::dec(x_8);
x_16 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_17 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_17, 0, x_15);
lean::cnstr_set(x_17, 1, x_6);
lean::cnstr_set(x_17, 2, x_16);
x_18 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_9);
return x_18;
}
}
else
{
obj* x_19; 
lean::dec(x_6);
x_19 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_19, 0, x_8);
lean::cnstr_set(x_19, 1, x_9);
return x_19;
}
}
block_26:
{
if (lean::obj_tag(x_21) == 0)
{
lean::dec(x_4);
lean::dec(x_2);
x_8 = x_21;
x_9 = x_22;
goto block_20;
}
else
{
obj* x_23; obj* x_24; obj* x_25; 
x_23 = lean::cnstr_get(x_21, 0);
lean::inc(x_23);
lean::dec(x_21);
x_24 = lean::cnstr_get(x_23, 0);
lean::inc(x_24);
lean::dec(x_23);
x_25 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_25, 0, x_4);
lean::cnstr_set(x_25, 1, x_24);
lean::cnstr_set(x_25, 2, x_2);
x_8 = x_25;
x_9 = x_22;
goto block_20;
}
}
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_number_x27___spec__7(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_number_x27___spec__7___rarg), 7, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_number_x27___spec__8___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; uint8 x_7; obj* x_8; 
x_6 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_4);
x_7 = 0;
x_8 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set_scalar(x_8, sizeof(void*)*1, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_10; uint8 x_11; obj* x_12; 
lean::dec(x_5);
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
x_10 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_1);
lean::cnstr_set(x_10, 2, x_2);
lean::cnstr_set(x_10, 3, x_4);
x_11 = 0;
x_12 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set_scalar(x_12, sizeof(void*)*1, x_11);
return x_12;
}
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_number_x27___spec__8(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___at_Lean_Parser_number_x27___spec__8___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_List_mfoldr___main___at_Lean_Parser_number_x27___spec__9(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
if (lean::obj_tag(x_5) == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
lean::dec(x_6);
lean::dec(x_5);
lean::dec(x_3);
lean::dec(x_2);
x_9 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_10 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_10, 0, x_4);
lean::cnstr_set(x_10, 1, x_7);
lean::cnstr_set(x_10, 2, x_9);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_8);
return x_11;
}
else
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_12 = lean::cnstr_get(x_5, 0);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_5, 1);
lean::inc(x_13);
lean::dec(x_5);
lean::inc(x_6);
lean::inc(x_3);
lean::inc(x_2);
x_14 = l_List_mfoldr___main___at_Lean_Parser_number_x27___spec__9(x_1, x_2, x_3, x_4, x_13, x_6, x_7, x_8);
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; 
x_16 = lean::cnstr_get(x_14, 1);
lean::inc(x_16);
lean::dec(x_14);
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
x_18 = lean::cnstr_get(x_15, 1);
lean::inc(x_18);
x_19 = lean::cnstr_get(x_15, 2);
lean::inc(x_19);
lean::dec(x_15);
x_20 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_number_x27___spec__7___rarg(x_2, x_3, x_12, x_17, x_6, x_18, x_16);
x_21 = !lean::is_exclusive(x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_23; 
x_22 = lean::cnstr_get(x_20, 0);
x_23 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_19, x_22);
lean::cnstr_set(x_20, 0, x_23);
return x_20;
}
else
{
obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_24 = lean::cnstr_get(x_20, 0);
x_25 = lean::cnstr_get(x_20, 1);
lean::inc(x_25);
lean::inc(x_24);
lean::dec(x_20);
x_26 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_19, x_24);
x_27 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_25);
return x_27;
}
}
else
{
uint8 x_28; 
lean::dec(x_12);
lean::dec(x_6);
lean::dec(x_3);
lean::dec(x_2);
x_28 = !lean::is_exclusive(x_14);
if (x_28 == 0)
{
obj* x_29; uint8 x_30; 
x_29 = lean::cnstr_get(x_14, 0);
lean::dec(x_29);
x_30 = !lean::is_exclusive(x_15);
if (x_30 == 0)
{
return x_14;
}
else
{
obj* x_31; uint8 x_32; obj* x_33; 
x_31 = lean::cnstr_get(x_15, 0);
x_32 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
lean::inc(x_31);
lean::dec(x_15);
x_33 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_33, 0, x_31);
lean::cnstr_set_scalar(x_33, sizeof(void*)*1, x_32);
lean::cnstr_set(x_14, 0, x_33);
return x_14;
}
}
else
{
obj* x_34; obj* x_35; uint8 x_36; obj* x_37; obj* x_38; obj* x_39; 
x_34 = lean::cnstr_get(x_14, 1);
lean::inc(x_34);
lean::dec(x_14);
x_35 = lean::cnstr_get(x_15, 0);
lean::inc(x_35);
x_36 = lean::cnstr_get_scalar<uint8>(x_15, sizeof(void*)*1);
if (lean::is_exclusive(x_15)) {
 lean::cnstr_release(x_15, 0);
 x_37 = x_15;
} else {
 lean::dec_ref(x_15);
 x_37 = lean::box(0);
}
if (lean::is_scalar(x_37)) {
 x_38 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_38 = x_37;
}
lean::cnstr_set(x_38, 0, x_35);
lean::cnstr_set_scalar(x_38, sizeof(void*)*1, x_36);
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_34);
return x_39;
}
}
}
}
}
obj* l_Lean_Parser_MonadParsec_longestMatch___at_Lean_Parser_number_x27___spec__6(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_5 = lean::box(0);
x_6 = l_Lean_Parser_MonadParsec_longestMatch___rarg___lambda__2___closed__1;
x_7 = l_mjoin___rarg___closed__1;
lean::inc(x_3);
x_8 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_number_x27___spec__8___rarg(x_6, x_7, x_5, x_5, x_3);
x_9 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::inc(x_3);
x_10 = l_List_mfoldr___main___at_Lean_Parser_number_x27___spec__9(x_3, x_7, x_9, x_8, x_1, x_2, x_3, x_4);
lean::dec(x_3);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_10);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_13 = lean::cnstr_get(x_10, 0);
lean::dec(x_13);
x_14 = lean::cnstr_get(x_11, 0);
lean::inc(x_14);
x_15 = lean::cnstr_get(x_11, 2);
lean::inc(x_15);
lean::dec(x_11);
x_16 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_14);
x_17 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_16);
lean::cnstr_set(x_10, 0, x_17);
return x_10;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_18 = lean::cnstr_get(x_10, 1);
lean::inc(x_18);
lean::dec(x_10);
x_19 = lean::cnstr_get(x_11, 0);
lean::inc(x_19);
x_20 = lean::cnstr_get(x_11, 2);
lean::inc(x_20);
lean::dec(x_11);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_20, x_19);
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_18);
return x_23;
}
}
else
{
uint8 x_24; 
x_24 = !lean::is_exclusive(x_10);
if (x_24 == 0)
{
obj* x_25; uint8 x_26; 
x_25 = lean::cnstr_get(x_10, 0);
lean::dec(x_25);
x_26 = !lean::is_exclusive(x_11);
if (x_26 == 0)
{
obj* x_27; 
x_27 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_11);
lean::cnstr_set(x_10, 0, x_27);
return x_10;
}
else
{
obj* x_28; uint8 x_29; obj* x_30; obj* x_31; 
x_28 = lean::cnstr_get(x_11, 0);
x_29 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
lean::inc(x_28);
lean::dec(x_11);
x_30 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_30, 0, x_28);
lean::cnstr_set_scalar(x_30, sizeof(void*)*1, x_29);
x_31 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_30);
lean::cnstr_set(x_10, 0, x_31);
return x_10;
}
}
else
{
obj* x_32; obj* x_33; uint8 x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_32 = lean::cnstr_get(x_10, 1);
lean::inc(x_32);
lean::dec(x_10);
x_33 = lean::cnstr_get(x_11, 0);
lean::inc(x_33);
x_34 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_35 = x_11;
} else {
 lean::dec_ref(x_11);
 x_35 = lean::box(0);
}
if (lean::is_scalar(x_35)) {
 x_36 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_36 = x_35;
}
lean::cnstr_set(x_36, 0, x_33);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_34);
x_37 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_36);
x_38 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_38, 0, x_37);
lean::cnstr_set(x_38, 1, x_32);
return x_38;
}
}
}
}
obj* l_Lean_Parser_Combinators_longestChoice___at_Lean_Parser_number_x27___spec__4(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_5 = lean::mk_nat_obj(0u);
x_6 = l_List_enumFrom___main___rarg(x_5, x_1);
x_7 = l_List_map___main___at_Lean_Parser_number_x27___spec__5(x_6);
lean::inc(x_2);
x_8 = l_Lean_Parser_MonadParsec_longestMatch___at_Lean_Parser_number_x27___spec__6(x_7, x_2, x_3, x_4);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
obj* x_10; 
x_10 = lean::cnstr_get(x_9, 0);
lean::inc(x_10);
if (lean::obj_tag(x_10) == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; uint8 x_18; 
lean::dec(x_10);
x_11 = lean::cnstr_get(x_8, 1);
lean::inc(x_11);
lean::dec(x_8);
x_12 = lean::cnstr_get(x_9, 1);
lean::inc(x_12);
x_13 = lean::cnstr_get(x_9, 2);
lean::inc(x_13);
lean::dec(x_9);
x_14 = lean::box(0);
x_15 = l___private_init_lean_parser_combinators_1__many1Aux___main___rarg___closed__1;
x_16 = l_mjoin___rarg___closed__1;
x_17 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_15, x_16, x_14, x_14, x_2, x_12, x_11);
lean::dec(x_2);
x_18 = !lean::is_exclusive(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; 
x_19 = lean::cnstr_get(x_17, 0);
x_20 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_19);
lean::cnstr_set(x_17, 0, x_20);
return x_17;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_21 = lean::cnstr_get(x_17, 0);
x_22 = lean::cnstr_get(x_17, 1);
lean::inc(x_22);
lean::inc(x_21);
lean::dec(x_17);
x_23 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_21);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_22);
return x_24;
}
}
else
{
uint8 x_25; 
lean::dec(x_2);
x_25 = !lean::is_exclusive(x_8);
if (x_25 == 0)
{
obj* x_26; uint8 x_27; 
x_26 = lean::cnstr_get(x_8, 0);
lean::dec(x_26);
x_27 = !lean::is_exclusive(x_9);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_28 = lean::cnstr_get(x_9, 2);
x_29 = lean::cnstr_get(x_9, 0);
lean::dec(x_29);
x_30 = lean::cnstr_get(x_10, 0);
lean::inc(x_30);
lean::dec(x_10);
x_31 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_9, 2, x_31);
lean::cnstr_set(x_9, 0, x_30);
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_28, x_9);
lean::cnstr_set(x_8, 0, x_32);
return x_8;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_33 = lean::cnstr_get(x_9, 1);
x_34 = lean::cnstr_get(x_9, 2);
lean::inc(x_34);
lean::inc(x_33);
lean::dec(x_9);
x_35 = lean::cnstr_get(x_10, 0);
lean::inc(x_35);
lean::dec(x_10);
x_36 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_37 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set(x_37, 1, x_33);
lean::cnstr_set(x_37, 2, x_36);
x_38 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_34, x_37);
lean::cnstr_set(x_8, 0, x_38);
return x_8;
}
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_39 = lean::cnstr_get(x_8, 1);
lean::inc(x_39);
lean::dec(x_8);
x_40 = lean::cnstr_get(x_9, 1);
lean::inc(x_40);
x_41 = lean::cnstr_get(x_9, 2);
lean::inc(x_41);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 x_42 = x_9;
} else {
 lean::dec_ref(x_9);
 x_42 = lean::box(0);
}
x_43 = lean::cnstr_get(x_10, 0);
lean::inc(x_43);
lean::dec(x_10);
x_44 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_42)) {
 x_45 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_45 = x_42;
}
lean::cnstr_set(x_45, 0, x_43);
lean::cnstr_set(x_45, 1, x_40);
lean::cnstr_set(x_45, 2, x_44);
x_46 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_41, x_45);
x_47 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_47, 0, x_46);
lean::cnstr_set(x_47, 1, x_39);
return x_47;
}
}
}
else
{
uint8 x_48; 
lean::dec(x_2);
x_48 = !lean::is_exclusive(x_8);
if (x_48 == 0)
{
obj* x_49; uint8 x_50; 
x_49 = lean::cnstr_get(x_8, 0);
lean::dec(x_49);
x_50 = !lean::is_exclusive(x_9);
if (x_50 == 0)
{
return x_8;
}
else
{
obj* x_51; uint8 x_52; obj* x_53; 
x_51 = lean::cnstr_get(x_9, 0);
x_52 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
lean::inc(x_51);
lean::dec(x_9);
x_53 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_53, 0, x_51);
lean::cnstr_set_scalar(x_53, sizeof(void*)*1, x_52);
lean::cnstr_set(x_8, 0, x_53);
return x_8;
}
}
else
{
obj* x_54; obj* x_55; uint8 x_56; obj* x_57; obj* x_58; obj* x_59; 
x_54 = lean::cnstr_get(x_8, 1);
lean::inc(x_54);
lean::dec(x_8);
x_55 = lean::cnstr_get(x_9, 0);
lean::inc(x_55);
x_56 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_57 = x_9;
} else {
 lean::dec_ref(x_9);
 x_57 = lean::box(0);
}
if (lean::is_scalar(x_57)) {
 x_58 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_58 = x_57;
}
lean::cnstr_set(x_58, 0, x_55);
lean::cnstr_set_scalar(x_58, sizeof(void*)*1, x_56);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_54);
return x_59;
}
}
}
}
obj* l_Lean_Parser_number_x27___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_number_x27___spec__1(x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_5);
if (x_7 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::cnstr_get(x_5, 0);
lean::dec(x_8);
x_9 = !lean::is_exclusive(x_6);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_6, 1);
x_11 = lean::cnstr_get(x_6, 2);
x_12 = lean::cnstr_get(x_6, 0);
lean::dec(x_12);
lean::inc(x_10);
x_13 = l_Lean_Parser_mkRawRes(x_1, x_10);
x_14 = l_Lean_Parser_finishCommentBlock___closed__2;
lean::cnstr_set(x_6, 2, x_14);
lean::cnstr_set(x_6, 0, x_13);
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_6);
lean::cnstr_set(x_5, 0, x_15);
return x_5;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_16 = lean::cnstr_get(x_6, 1);
x_17 = lean::cnstr_get(x_6, 2);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_6);
lean::inc(x_16);
x_18 = l_Lean_Parser_mkRawRes(x_1, x_16);
x_19 = l_Lean_Parser_finishCommentBlock___closed__2;
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_16);
lean::cnstr_set(x_20, 2, x_19);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_20);
lean::cnstr_set(x_5, 0, x_21);
return x_5;
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_5, 1);
lean::inc(x_22);
lean::dec(x_5);
x_23 = lean::cnstr_get(x_6, 1);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_6, 2);
lean::inc(x_24);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_25 = x_6;
} else {
 lean::dec_ref(x_6);
 x_25 = lean::box(0);
}
lean::inc(x_23);
x_26 = l_Lean_Parser_mkRawRes(x_1, x_23);
x_27 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_25)) {
 x_28 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_28 = x_25;
}
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_23);
lean::cnstr_set(x_28, 2, x_27);
x_29 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_22);
return x_30;
}
}
else
{
uint8 x_31; 
lean::dec(x_1);
x_31 = !lean::is_exclusive(x_5);
if (x_31 == 0)
{
obj* x_32; uint8 x_33; 
x_32 = lean::cnstr_get(x_5, 0);
lean::dec(x_32);
x_33 = !lean::is_exclusive(x_6);
if (x_33 == 0)
{
return x_5;
}
else
{
obj* x_34; uint8 x_35; obj* x_36; 
x_34 = lean::cnstr_get(x_6, 0);
x_35 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
lean::inc(x_34);
lean::dec(x_6);
x_36 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_35);
lean::cnstr_set(x_5, 0, x_36);
return x_5;
}
}
else
{
obj* x_37; obj* x_38; uint8 x_39; obj* x_40; obj* x_41; obj* x_42; 
x_37 = lean::cnstr_get(x_5, 1);
lean::inc(x_37);
lean::dec(x_5);
x_38 = lean::cnstr_get(x_6, 0);
lean::inc(x_38);
x_39 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_40 = x_6;
} else {
 lean::dec_ref(x_6);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_38);
lean::cnstr_set_scalar(x_41, sizeof(void*)*1, x_39);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_37);
return x_42;
}
}
}
}
obj* l_Lean_Parser_number_x27___lambda__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_Parser_parseBinLit(x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_5);
if (x_7 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::cnstr_get(x_5, 0);
lean::dec(x_8);
x_9 = !lean::is_exclusive(x_6);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_6, 1);
x_11 = lean::cnstr_get(x_6, 2);
x_12 = lean::cnstr_get(x_6, 0);
lean::dec(x_12);
lean::inc(x_10);
x_13 = l_Lean_Parser_mkRawRes(x_1, x_10);
x_14 = l_Lean_Parser_finishCommentBlock___closed__2;
lean::cnstr_set(x_6, 2, x_14);
lean::cnstr_set(x_6, 0, x_13);
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_6);
lean::cnstr_set(x_5, 0, x_15);
return x_5;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_16 = lean::cnstr_get(x_6, 1);
x_17 = lean::cnstr_get(x_6, 2);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_6);
lean::inc(x_16);
x_18 = l_Lean_Parser_mkRawRes(x_1, x_16);
x_19 = l_Lean_Parser_finishCommentBlock___closed__2;
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_16);
lean::cnstr_set(x_20, 2, x_19);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_20);
lean::cnstr_set(x_5, 0, x_21);
return x_5;
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_5, 1);
lean::inc(x_22);
lean::dec(x_5);
x_23 = lean::cnstr_get(x_6, 1);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_6, 2);
lean::inc(x_24);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_25 = x_6;
} else {
 lean::dec_ref(x_6);
 x_25 = lean::box(0);
}
lean::inc(x_23);
x_26 = l_Lean_Parser_mkRawRes(x_1, x_23);
x_27 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_25)) {
 x_28 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_28 = x_25;
}
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_23);
lean::cnstr_set(x_28, 2, x_27);
x_29 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_22);
return x_30;
}
}
else
{
uint8 x_31; 
lean::dec(x_1);
x_31 = !lean::is_exclusive(x_5);
if (x_31 == 0)
{
obj* x_32; uint8 x_33; 
x_32 = lean::cnstr_get(x_5, 0);
lean::dec(x_32);
x_33 = !lean::is_exclusive(x_6);
if (x_33 == 0)
{
return x_5;
}
else
{
obj* x_34; uint8 x_35; obj* x_36; 
x_34 = lean::cnstr_get(x_6, 0);
x_35 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
lean::inc(x_34);
lean::dec(x_6);
x_36 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_35);
lean::cnstr_set(x_5, 0, x_36);
return x_5;
}
}
else
{
obj* x_37; obj* x_38; uint8 x_39; obj* x_40; obj* x_41; obj* x_42; 
x_37 = lean::cnstr_get(x_5, 1);
lean::inc(x_37);
lean::dec(x_5);
x_38 = lean::cnstr_get(x_6, 0);
lean::inc(x_38);
x_39 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_40 = x_6;
} else {
 lean::dec_ref(x_6);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_38);
lean::cnstr_set_scalar(x_41, sizeof(void*)*1, x_39);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_37);
return x_42;
}
}
}
}
obj* l_Lean_Parser_number_x27___lambda__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_Parser_parseOctLit(x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_5);
if (x_7 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::cnstr_get(x_5, 0);
lean::dec(x_8);
x_9 = !lean::is_exclusive(x_6);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_6, 1);
x_11 = lean::cnstr_get(x_6, 2);
x_12 = lean::cnstr_get(x_6, 0);
lean::dec(x_12);
lean::inc(x_10);
x_13 = l_Lean_Parser_mkRawRes(x_1, x_10);
x_14 = l_Lean_Parser_finishCommentBlock___closed__2;
lean::cnstr_set(x_6, 2, x_14);
lean::cnstr_set(x_6, 0, x_13);
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_6);
lean::cnstr_set(x_5, 0, x_15);
return x_5;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_16 = lean::cnstr_get(x_6, 1);
x_17 = lean::cnstr_get(x_6, 2);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_6);
lean::inc(x_16);
x_18 = l_Lean_Parser_mkRawRes(x_1, x_16);
x_19 = l_Lean_Parser_finishCommentBlock___closed__2;
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_16);
lean::cnstr_set(x_20, 2, x_19);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_20);
lean::cnstr_set(x_5, 0, x_21);
return x_5;
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_5, 1);
lean::inc(x_22);
lean::dec(x_5);
x_23 = lean::cnstr_get(x_6, 1);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_6, 2);
lean::inc(x_24);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_25 = x_6;
} else {
 lean::dec_ref(x_6);
 x_25 = lean::box(0);
}
lean::inc(x_23);
x_26 = l_Lean_Parser_mkRawRes(x_1, x_23);
x_27 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_25)) {
 x_28 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_28 = x_25;
}
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_23);
lean::cnstr_set(x_28, 2, x_27);
x_29 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_22);
return x_30;
}
}
else
{
uint8 x_31; 
lean::dec(x_1);
x_31 = !lean::is_exclusive(x_5);
if (x_31 == 0)
{
obj* x_32; uint8 x_33; 
x_32 = lean::cnstr_get(x_5, 0);
lean::dec(x_32);
x_33 = !lean::is_exclusive(x_6);
if (x_33 == 0)
{
return x_5;
}
else
{
obj* x_34; uint8 x_35; obj* x_36; 
x_34 = lean::cnstr_get(x_6, 0);
x_35 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
lean::inc(x_34);
lean::dec(x_6);
x_36 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_35);
lean::cnstr_set(x_5, 0, x_36);
return x_5;
}
}
else
{
obj* x_37; obj* x_38; uint8 x_39; obj* x_40; obj* x_41; obj* x_42; 
x_37 = lean::cnstr_get(x_5, 1);
lean::inc(x_37);
lean::dec(x_5);
x_38 = lean::cnstr_get(x_6, 0);
lean::inc(x_38);
x_39 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_40 = x_6;
} else {
 lean::dec_ref(x_6);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_38);
lean::cnstr_set_scalar(x_41, sizeof(void*)*1, x_39);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_37);
return x_42;
}
}
}
}
obj* l_Lean_Parser_number_x27___lambda__4(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_Parser_parseHexLit(x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_5);
if (x_7 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::cnstr_get(x_5, 0);
lean::dec(x_8);
x_9 = !lean::is_exclusive(x_6);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_6, 1);
x_11 = lean::cnstr_get(x_6, 2);
x_12 = lean::cnstr_get(x_6, 0);
lean::dec(x_12);
lean::inc(x_10);
x_13 = l_Lean_Parser_mkRawRes(x_1, x_10);
x_14 = l_Lean_Parser_finishCommentBlock___closed__2;
lean::cnstr_set(x_6, 2, x_14);
lean::cnstr_set(x_6, 0, x_13);
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_6);
lean::cnstr_set(x_5, 0, x_15);
return x_5;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_16 = lean::cnstr_get(x_6, 1);
x_17 = lean::cnstr_get(x_6, 2);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_6);
lean::inc(x_16);
x_18 = l_Lean_Parser_mkRawRes(x_1, x_16);
x_19 = l_Lean_Parser_finishCommentBlock___closed__2;
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_16);
lean::cnstr_set(x_20, 2, x_19);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_20);
lean::cnstr_set(x_5, 0, x_21);
return x_5;
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_5, 1);
lean::inc(x_22);
lean::dec(x_5);
x_23 = lean::cnstr_get(x_6, 1);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_6, 2);
lean::inc(x_24);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_25 = x_6;
} else {
 lean::dec_ref(x_6);
 x_25 = lean::box(0);
}
lean::inc(x_23);
x_26 = l_Lean_Parser_mkRawRes(x_1, x_23);
x_27 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_25)) {
 x_28 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_28 = x_25;
}
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_23);
lean::cnstr_set(x_28, 2, x_27);
x_29 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_22);
return x_30;
}
}
else
{
uint8 x_31; 
lean::dec(x_1);
x_31 = !lean::is_exclusive(x_5);
if (x_31 == 0)
{
obj* x_32; uint8 x_33; 
x_32 = lean::cnstr_get(x_5, 0);
lean::dec(x_32);
x_33 = !lean::is_exclusive(x_6);
if (x_33 == 0)
{
return x_5;
}
else
{
obj* x_34; uint8 x_35; obj* x_36; 
x_34 = lean::cnstr_get(x_6, 0);
x_35 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
lean::inc(x_34);
lean::dec(x_6);
x_36 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_35);
lean::cnstr_set(x_5, 0, x_36);
return x_5;
}
}
else
{
obj* x_37; obj* x_38; uint8 x_39; obj* x_40; obj* x_41; obj* x_42; 
x_37 = lean::cnstr_get(x_5, 1);
lean::inc(x_37);
lean::dec(x_5);
x_38 = lean::cnstr_get(x_6, 0);
lean::inc(x_38);
x_39 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_40 = x_6;
} else {
 lean::dec_ref(x_6);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_38);
lean::cnstr_set_scalar(x_41, sizeof(void*)*1, x_39);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_37);
return x_42;
}
}
}
}
obj* _init_l_Lean_Parser_number_x27___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_x27___lambda__1___boxed), 4, 0);
lean::inc(x_2);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_3);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_x27___lambda__2), 4, 0);
lean::inc(x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_6, 0, x_2);
lean::closure_set(x_6, 1, x_5);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_x27___lambda__3___boxed), 4, 0);
lean::inc(x_2);
x_8 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_8, 0, x_2);
lean::closure_set(x_8, 1, x_7);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_x27___lambda__4___boxed), 4, 0);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_10, 0, x_2);
lean::closure_set(x_10, 1, x_9);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_8);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_14, 0, x_6);
lean::cnstr_set(x_14, 1, x_13);
x_15 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_15, 0, x_4);
lean::cnstr_set(x_15, 1, x_14);
x_16 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_longestChoice___at_Lean_Parser_number_x27___spec__4), 4, 1);
lean::closure_set(x_16, 0, x_15);
x_17 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_11);
return x_17;
}
}
obj* l_Lean_Parser_number_x27(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_number;
x_5 = l_Lean_Parser_number_x27___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4(x_4, x_5, x_1, x_2, x_3);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x27___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_MonadParsec_takeWhileCont___at_Lean_Parser_number_x27___spec__2(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_number_x27___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_takeWhile1___at_Lean_Parser_number_x27___spec__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_number_x27___spec__7___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_number_x27___spec__7(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_number_x27___spec__8___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_number_x27___spec__8___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
return x_6;
}
}
obj* l_List_mfoldr___main___at_Lean_Parser_number_x27___spec__9___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6, obj* x_7, obj* x_8) {
_start:
{
obj* x_9; 
x_9 = l_List_mfoldr___main___at_Lean_Parser_number_x27___spec__9(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean::dec(x_1);
return x_9;
}
}
obj* l_Lean_Parser_number_x27___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_number_x27___lambda__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_number_x27___lambda__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_number_x27___lambda__3(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_number_x27___lambda__4___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_number_x27___lambda__4(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* _init_l_Lean_Parser_stringLit() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("Lean");
x_3 = lean_name_mk_string(x_1, x_2);
x_4 = lean::mk_string("Parser");
x_5 = lean_name_mk_string(x_3, x_4);
x_6 = lean::mk_string("stringLit");
x_7 = lean_name_mk_string(x_5, x_6);
return x_7;
}
}
obj* _init_l_Lean_Parser_stringLit_HasView_x27___elambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; 
x_1 = lean::box(0);
x_2 = lean::box(3);
x_3 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_3, 0, x_2);
lean::cnstr_set(x_3, 1, x_1);
x_4 = l_Lean_Parser_stringLit;
x_5 = l_Lean_Parser_Syntax_mkNode(x_4, x_3);
return x_5;
}
}
obj* l_Lean_Parser_stringLit_HasView_x27___elambda__1(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
x_2 = l_Lean_Parser_stringLit_HasView_x27___elambda__1___closed__1;
return x_2;
}
else
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::cnstr_get(x_1, 0);
x_4 = lean::box(0);
lean::inc(x_3);
x_5 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_5, 0, x_3);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_4);
x_7 = l_Lean_Parser_stringLit;
x_8 = l_Lean_Parser_Syntax_mkNode(x_7, x_6);
return x_8;
}
}
}
obj* l_Lean_Parser_stringLit_HasView_x27___elambda__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_Syntax_asNode___main(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_2);
x_3 = lean::box(0);
return x_3;
}
else
{
uint8 x_4; 
x_4 = !lean::is_exclusive(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; 
x_5 = lean::cnstr_get(x_2, 0);
x_6 = lean::cnstr_get(x_5, 1);
lean::inc(x_6);
lean::dec(x_5);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; 
lean::dec(x_6);
lean::free_heap_obj(x_2);
x_7 = lean::box(0);
return x_7;
}
else
{
obj* x_8; 
x_8 = lean::cnstr_get(x_6, 0);
lean::inc(x_8);
lean::dec(x_6);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; 
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
lean::dec(x_8);
lean::cnstr_set(x_2, 0, x_9);
return x_2;
}
else
{
obj* x_10; 
lean::dec(x_8);
lean::free_heap_obj(x_2);
x_10 = lean::box(0);
return x_10;
}
}
}
else
{
obj* x_11; obj* x_12; 
x_11 = lean::cnstr_get(x_2, 0);
lean::inc(x_11);
lean::dec(x_2);
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
lean::dec(x_11);
if (lean::obj_tag(x_12) == 0)
{
obj* x_13; 
lean::dec(x_12);
x_13 = lean::box(0);
return x_13;
}
else
{
obj* x_14; 
x_14 = lean::cnstr_get(x_12, 0);
lean::inc(x_14);
lean::dec(x_12);
if (lean::obj_tag(x_14) == 0)
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
lean::dec(x_14);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_15);
return x_16;
}
else
{
obj* x_17; 
lean::dec(x_14);
x_17 = lean::box(0);
return x_17;
}
}
}
}
}
}
obj* _init_l_Lean_Parser_stringLit_HasView_x27() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_stringLit_HasView_x27___elambda__2), 1, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_stringLit_HasView_x27___elambda__1___boxed), 1, 0);
x_3 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_3, 0, x_1);
lean::cnstr_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_stringLit_HasView_x27___elambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_stringLit_HasView_x27___elambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_stringLit_HasView() {
_start:
{
obj* x_1; 
x_1 = l_Lean_Parser_stringLit_HasView_x27;
return x_1;
}
}
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x27___spec__4___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_6, 0, x_2);
x_7 = lean::box(0);
x_8 = l_mjoin___rarg___closed__1;
x_9 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_1, x_8, x_6, x_7, x_3, x_4, x_5);
lean::dec(x_6);
return x_9;
}
}
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x27___spec__4(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x27___spec__4___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_digit___at_Lean_Parser_stringLit_x27___spec__6(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint8 x_4; 
x_4 = l_String_OldIterator_hasNext___main(x_2);
if (x_4 == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; uint8 x_9; 
x_5 = lean::box(0);
x_6 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_7 = l_mjoin___rarg___closed__1;
x_8 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_6, x_7, x_5, x_5, x_1, x_2, x_3);
x_9 = !lean::is_exclusive(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; 
x_10 = lean::cnstr_get(x_8, 0);
x_11 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_12 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_10);
lean::cnstr_set(x_8, 0, x_12);
return x_8;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_13 = lean::cnstr_get(x_8, 0);
x_14 = lean::cnstr_get(x_8, 1);
lean::inc(x_14);
lean::inc(x_13);
lean::dec(x_8);
x_15 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_16 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_13);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_14);
return x_17;
}
}
else
{
uint32 x_18; uint8 x_19; 
x_18 = l_String_OldIterator_curr___main(x_2);
x_19 = l_Char_isDigit(x_18);
if (x_19 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; uint8 x_27; 
x_20 = l_Char_quoteCore(x_18);
x_21 = l_Char_HasRepr___closed__1;
x_22 = lean::string_append(x_21, x_20);
lean::dec(x_20);
x_23 = lean::string_append(x_22, x_21);
x_24 = lean::box(0);
x_25 = l_mjoin___rarg___closed__1;
x_26 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_23, x_25, x_24, x_24, x_1, x_2, x_3);
x_27 = !lean::is_exclusive(x_26);
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; 
x_28 = lean::cnstr_get(x_26, 0);
x_29 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_30 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_29, x_28);
lean::cnstr_set(x_26, 0, x_30);
return x_26;
}
else
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_31 = lean::cnstr_get(x_26, 0);
x_32 = lean::cnstr_get(x_26, 1);
lean::inc(x_32);
lean::inc(x_31);
lean::dec(x_26);
x_33 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_34 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_33, x_31);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_32);
return x_35;
}
}
else
{
obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_36 = l_String_OldIterator_next___main(x_2);
x_37 = lean::box(0);
x_38 = lean::box_uint32(x_18);
x_39 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_36);
lean::cnstr_set(x_39, 2, x_37);
x_40 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_40, 0, x_39);
lean::cnstr_set(x_40, 1, x_3);
return x_40;
}
}
}
}
obj* _init_l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("hexadecimal");
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_188; obj* x_189; 
lean::inc(x_2);
x_188 = l_Lean_Parser_MonadParsec_digit___at_Lean_Parser_stringLit_x27___spec__6(x_1, x_2, x_3);
x_189 = lean::cnstr_get(x_188, 0);
lean::inc(x_189);
if (lean::obj_tag(x_189) == 0)
{
obj* x_190; uint8 x_191; 
x_190 = lean::cnstr_get(x_188, 1);
lean::inc(x_190);
lean::dec(x_188);
x_191 = !lean::is_exclusive(x_189);
if (x_191 == 0)
{
obj* x_192; obj* x_193; uint32 x_194; obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; 
x_192 = lean::cnstr_get(x_189, 0);
x_193 = lean::cnstr_get(x_189, 2);
x_194 = lean::unbox_uint32(x_192);
lean::dec(x_192);
x_195 = lean::uint32_to_nat(x_194);
x_196 = l_String_foldlAux___main___at_String_toNat___spec__1___closed__1;
x_197 = lean::nat_sub(x_195, x_196);
lean::dec(x_195);
x_198 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_189, 2, x_198);
lean::cnstr_set(x_189, 0, x_197);
x_199 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_193, x_189);
x_4 = x_199;
x_5 = x_190;
goto block_187;
}
else
{
obj* x_200; obj* x_201; obj* x_202; uint32 x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; 
x_200 = lean::cnstr_get(x_189, 0);
x_201 = lean::cnstr_get(x_189, 1);
x_202 = lean::cnstr_get(x_189, 2);
lean::inc(x_202);
lean::inc(x_201);
lean::inc(x_200);
lean::dec(x_189);
x_203 = lean::unbox_uint32(x_200);
lean::dec(x_200);
x_204 = lean::uint32_to_nat(x_203);
x_205 = l_String_foldlAux___main___at_String_toNat___spec__1___closed__1;
x_206 = lean::nat_sub(x_204, x_205);
lean::dec(x_204);
x_207 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_208 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_208, 0, x_206);
lean::cnstr_set(x_208, 1, x_201);
lean::cnstr_set(x_208, 2, x_207);
x_209 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_202, x_208);
x_4 = x_209;
x_5 = x_190;
goto block_187;
}
}
else
{
obj* x_210; uint8 x_211; 
x_210 = lean::cnstr_get(x_188, 1);
lean::inc(x_210);
lean::dec(x_188);
x_211 = !lean::is_exclusive(x_189);
if (x_211 == 0)
{
x_4 = x_189;
x_5 = x_210;
goto block_187;
}
else
{
obj* x_212; uint8 x_213; obj* x_214; 
x_212 = lean::cnstr_get(x_189, 0);
x_213 = lean::cnstr_get_scalar<uint8>(x_189, sizeof(void*)*1);
lean::inc(x_212);
lean::dec(x_189);
x_214 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_214, 0, x_212);
lean::cnstr_set_scalar(x_214, sizeof(void*)*1, x_213);
x_4 = x_214;
x_5 = x_210;
goto block_187;
}
}
block_187:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_2);
x_6 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1;
x_7 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_4, x_6);
x_8 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_8, 0, x_7);
lean::cnstr_set(x_8, 1, x_5);
return x_8;
}
else
{
obj* x_9; uint8 x_10; obj* x_11; obj* x_12; obj* x_114; obj* x_115; 
x_9 = lean::cnstr_get(x_4, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
if (x_10 == 0)
{
uint8 x_144; 
lean::dec(x_4);
x_144 = l_String_OldIterator_hasNext___main(x_2);
if (x_144 == 0)
{
obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; 
x_145 = lean::box(0);
x_146 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_147 = l_mjoin___rarg___closed__1;
lean::inc(x_2);
x_148 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_146, x_147, x_145, x_145, x_1, x_2, x_5);
x_149 = lean::cnstr_get(x_148, 0);
lean::inc(x_149);
x_150 = lean::cnstr_get(x_148, 1);
lean::inc(x_150);
lean::dec(x_148);
x_151 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_152 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_151, x_149);
x_114 = x_152;
x_115 = x_150;
goto block_143;
}
else
{
uint32 x_153; uint32 x_154; uint8 x_155; 
x_153 = l_String_OldIterator_curr___main(x_2);
x_154 = 97;
x_155 = x_154 <= x_153;
if (x_155 == 0)
{
obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; 
x_156 = l_Char_quoteCore(x_153);
x_157 = l_Char_HasRepr___closed__1;
x_158 = lean::string_append(x_157, x_156);
lean::dec(x_156);
x_159 = lean::string_append(x_158, x_157);
x_160 = lean::box(0);
x_161 = l_mjoin___rarg___closed__1;
lean::inc(x_2);
x_162 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_159, x_161, x_160, x_160, x_1, x_2, x_5);
x_163 = lean::cnstr_get(x_162, 0);
lean::inc(x_163);
x_164 = lean::cnstr_get(x_162, 1);
lean::inc(x_164);
lean::dec(x_162);
x_165 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_166 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_165, x_163);
x_114 = x_166;
x_115 = x_164;
goto block_143;
}
else
{
uint32 x_167; uint8 x_168; 
x_167 = 102;
x_168 = x_153 <= x_167;
if (x_168 == 0)
{
obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; 
x_169 = l_Char_quoteCore(x_153);
x_170 = l_Char_HasRepr___closed__1;
x_171 = lean::string_append(x_170, x_169);
lean::dec(x_169);
x_172 = lean::string_append(x_171, x_170);
x_173 = lean::box(0);
x_174 = l_mjoin___rarg___closed__1;
lean::inc(x_2);
x_175 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_172, x_174, x_173, x_173, x_1, x_2, x_5);
x_176 = lean::cnstr_get(x_175, 0);
lean::inc(x_176);
x_177 = lean::cnstr_get(x_175, 1);
lean::inc(x_177);
lean::dec(x_175);
x_178 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_179 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_178, x_176);
x_114 = x_179;
x_115 = x_177;
goto block_143;
}
else
{
obj* x_180; obj* x_181; obj* x_182; obj* x_183; 
lean::inc(x_2);
x_180 = l_String_OldIterator_next___main(x_2);
x_181 = lean::box(0);
x_182 = lean::box_uint32(x_153);
x_183 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_183, 0, x_182);
lean::cnstr_set(x_183, 1, x_180);
lean::cnstr_set(x_183, 2, x_181);
x_114 = x_183;
x_115 = x_5;
goto block_143;
}
}
}
}
else
{
obj* x_184; obj* x_185; obj* x_186; 
lean::dec(x_9);
lean::dec(x_2);
x_184 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1;
x_185 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_4, x_184);
x_186 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_186, 0, x_185);
lean::cnstr_set(x_186, 1, x_5);
return x_186;
}
block_113:
{
if (lean::obj_tag(x_11) == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
lean::dec(x_2);
x_13 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_9, x_11);
x_14 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1;
x_15 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_13, x_14);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_12);
return x_16;
}
else
{
obj* x_17; uint8 x_18; obj* x_19; obj* x_20; 
x_17 = lean::cnstr_get(x_11, 0);
lean::inc(x_17);
x_18 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (x_18 == 0)
{
uint8 x_69; 
lean::dec(x_11);
x_69 = l_String_OldIterator_hasNext___main(x_2);
if (x_69 == 0)
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
x_70 = lean::box(0);
x_71 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_72 = l_mjoin___rarg___closed__1;
x_73 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_71, x_72, x_70, x_70, x_1, x_2, x_12);
x_74 = lean::cnstr_get(x_73, 0);
lean::inc(x_74);
x_75 = lean::cnstr_get(x_73, 1);
lean::inc(x_75);
lean::dec(x_73);
x_76 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_77 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_76, x_74);
x_19 = x_77;
x_20 = x_75;
goto block_68;
}
else
{
uint32 x_78; uint32 x_79; uint8 x_80; 
x_78 = l_String_OldIterator_curr___main(x_2);
x_79 = 65;
x_80 = x_79 <= x_78;
if (x_80 == 0)
{
obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
x_81 = l_Char_quoteCore(x_78);
x_82 = l_Char_HasRepr___closed__1;
x_83 = lean::string_append(x_82, x_81);
lean::dec(x_81);
x_84 = lean::string_append(x_83, x_82);
x_85 = lean::box(0);
x_86 = l_mjoin___rarg___closed__1;
x_87 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_84, x_86, x_85, x_85, x_1, x_2, x_12);
x_88 = lean::cnstr_get(x_87, 0);
lean::inc(x_88);
x_89 = lean::cnstr_get(x_87, 1);
lean::inc(x_89);
lean::dec(x_87);
x_90 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_91 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_90, x_88);
x_19 = x_91;
x_20 = x_89;
goto block_68;
}
else
{
uint32 x_92; uint8 x_93; 
x_92 = 70;
x_93 = x_78 <= x_92;
if (x_93 == 0)
{
obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_94 = l_Char_quoteCore(x_78);
x_95 = l_Char_HasRepr___closed__1;
x_96 = lean::string_append(x_95, x_94);
lean::dec(x_94);
x_97 = lean::string_append(x_96, x_95);
x_98 = lean::box(0);
x_99 = l_mjoin___rarg___closed__1;
x_100 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_97, x_99, x_98, x_98, x_1, x_2, x_12);
x_101 = lean::cnstr_get(x_100, 0);
lean::inc(x_101);
x_102 = lean::cnstr_get(x_100, 1);
lean::inc(x_102);
lean::dec(x_100);
x_103 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_104 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_103, x_101);
x_19 = x_104;
x_20 = x_102;
goto block_68;
}
else
{
obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
x_105 = l_String_OldIterator_next___main(x_2);
x_106 = lean::box(0);
x_107 = lean::box_uint32(x_78);
x_108 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_108, 0, x_107);
lean::cnstr_set(x_108, 1, x_105);
lean::cnstr_set(x_108, 2, x_106);
x_19 = x_108;
x_20 = x_12;
goto block_68;
}
}
}
}
else
{
obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_17);
lean::dec(x_2);
x_109 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_9, x_11);
x_110 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1;
x_111 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_109, x_110);
x_112 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_12);
return x_112;
}
block_68:
{
if (lean::obj_tag(x_19) == 0)
{
uint8 x_21; 
x_21 = !lean::is_exclusive(x_19);
if (x_21 == 0)
{
obj* x_22; obj* x_23; uint32 x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_22 = lean::cnstr_get(x_19, 0);
x_23 = lean::cnstr_get(x_19, 2);
x_24 = lean::unbox_uint32(x_22);
lean::dec(x_22);
x_25 = lean::uint32_to_nat(x_24);
x_26 = l_Lean_Parser_parseHexDigit___rarg___lambda__5___closed__1;
x_27 = lean::nat_sub(x_25, x_26);
lean::dec(x_25);
x_28 = lean::mk_nat_obj(10u);
x_29 = lean::nat_add(x_28, x_27);
lean::dec(x_27);
x_30 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_19, 2, x_30);
lean::cnstr_set(x_19, 0, x_29);
x_31 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_23, x_19);
x_32 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_17, x_31);
x_33 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_9, x_32);
x_34 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1;
x_35 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_33, x_34);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_20);
return x_36;
}
else
{
obj* x_37; obj* x_38; obj* x_39; uint32 x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_37 = lean::cnstr_get(x_19, 0);
x_38 = lean::cnstr_get(x_19, 1);
x_39 = lean::cnstr_get(x_19, 2);
lean::inc(x_39);
lean::inc(x_38);
lean::inc(x_37);
lean::dec(x_19);
x_40 = lean::unbox_uint32(x_37);
lean::dec(x_37);
x_41 = lean::uint32_to_nat(x_40);
x_42 = l_Lean_Parser_parseHexDigit___rarg___lambda__5___closed__1;
x_43 = lean::nat_sub(x_41, x_42);
lean::dec(x_41);
x_44 = lean::mk_nat_obj(10u);
x_45 = lean::nat_add(x_44, x_43);
lean::dec(x_43);
x_46 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_47 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set(x_47, 1, x_38);
lean::cnstr_set(x_47, 2, x_46);
x_48 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_39, x_47);
x_49 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_17, x_48);
x_50 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_9, x_49);
x_51 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1;
x_52 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_50, x_51);
x_53 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_53, 0, x_52);
lean::cnstr_set(x_53, 1, x_20);
return x_53;
}
}
else
{
uint8 x_54; 
x_54 = !lean::is_exclusive(x_19);
if (x_54 == 0)
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
x_55 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_17, x_19);
x_56 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_9, x_55);
x_57 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1;
x_58 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_56, x_57);
x_59 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_59, 0, x_58);
lean::cnstr_set(x_59, 1, x_20);
return x_59;
}
else
{
obj* x_60; uint8 x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_60 = lean::cnstr_get(x_19, 0);
x_61 = lean::cnstr_get_scalar<uint8>(x_19, sizeof(void*)*1);
lean::inc(x_60);
lean::dec(x_19);
x_62 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_62, 0, x_60);
lean::cnstr_set_scalar(x_62, sizeof(void*)*1, x_61);
x_63 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_17, x_62);
x_64 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_9, x_63);
x_65 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1;
x_66 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_64, x_65);
x_67 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_20);
return x_67;
}
}
}
}
}
block_143:
{
if (lean::obj_tag(x_114) == 0)
{
uint8 x_116; 
x_116 = !lean::is_exclusive(x_114);
if (x_116 == 0)
{
obj* x_117; obj* x_118; uint32 x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; 
x_117 = lean::cnstr_get(x_114, 0);
x_118 = lean::cnstr_get(x_114, 2);
x_119 = lean::unbox_uint32(x_117);
lean::dec(x_117);
x_120 = lean::uint32_to_nat(x_119);
x_121 = l_Lean_Parser_parseHexDigit___rarg___lambda__3___closed__1;
x_122 = lean::nat_sub(x_120, x_121);
lean::dec(x_120);
x_123 = lean::mk_nat_obj(10u);
x_124 = lean::nat_add(x_123, x_122);
lean::dec(x_122);
x_125 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_114, 2, x_125);
lean::cnstr_set(x_114, 0, x_124);
x_126 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_118, x_114);
x_11 = x_126;
x_12 = x_115;
goto block_113;
}
else
{
obj* x_127; obj* x_128; obj* x_129; uint32 x_130; obj* x_131; obj* x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; 
x_127 = lean::cnstr_get(x_114, 0);
x_128 = lean::cnstr_get(x_114, 1);
x_129 = lean::cnstr_get(x_114, 2);
lean::inc(x_129);
lean::inc(x_128);
lean::inc(x_127);
lean::dec(x_114);
x_130 = lean::unbox_uint32(x_127);
lean::dec(x_127);
x_131 = lean::uint32_to_nat(x_130);
x_132 = l_Lean_Parser_parseHexDigit___rarg___lambda__3___closed__1;
x_133 = lean::nat_sub(x_131, x_132);
lean::dec(x_131);
x_134 = lean::mk_nat_obj(10u);
x_135 = lean::nat_add(x_134, x_133);
lean::dec(x_133);
x_136 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_137 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_137, 0, x_135);
lean::cnstr_set(x_137, 1, x_128);
lean::cnstr_set(x_137, 2, x_136);
x_138 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_129, x_137);
x_11 = x_138;
x_12 = x_115;
goto block_113;
}
}
else
{
uint8 x_139; 
x_139 = !lean::is_exclusive(x_114);
if (x_139 == 0)
{
x_11 = x_114;
x_12 = x_115;
goto block_113;
}
else
{
obj* x_140; uint8 x_141; obj* x_142; 
x_140 = lean::cnstr_get(x_114, 0);
x_141 = lean::cnstr_get_scalar<uint8>(x_114, sizeof(void*)*1);
lean::inc(x_140);
lean::dec(x_114);
x_142 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_142, 0, x_140);
lean::cnstr_set_scalar(x_142, sizeof(void*)*1, x_141);
x_11 = x_142;
x_12 = x_115;
goto block_113;
}
}
}
}
}
}
}
obj* l_Lean_Parser_parseQuotedChar___at_Lean_Parser_stringLit_x27___spec__3(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
lean::inc(x_2);
x_4 = l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__2(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_4);
if (x_6 == 0)
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::cnstr_get(x_4, 1);
x_8 = lean::cnstr_get(x_4, 0);
lean::dec(x_8);
x_9 = !lean::is_exclusive(x_5);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; uint32 x_13; uint32 x_14; uint8 x_15; 
x_10 = lean::cnstr_get(x_5, 0);
x_11 = lean::cnstr_get(x_5, 1);
x_12 = lean::cnstr_get(x_5, 2);
x_13 = 92;
x_14 = lean::unbox_uint32(x_10);
x_15 = x_14 == x_13;
if (x_15 == 0)
{
uint32 x_16; uint32 x_17; uint8 x_18; 
x_16 = 34;
x_17 = lean::unbox_uint32(x_10);
x_18 = x_17 == x_16;
if (x_18 == 0)
{
uint32 x_19; uint32 x_20; uint8 x_21; 
x_19 = 39;
x_20 = lean::unbox_uint32(x_10);
x_21 = x_20 == x_19;
if (x_21 == 0)
{
uint32 x_22; uint32 x_23; uint8 x_24; 
x_22 = 110;
x_23 = lean::unbox_uint32(x_10);
x_24 = x_23 == x_22;
if (x_24 == 0)
{
uint32 x_25; uint32 x_26; uint8 x_27; 
x_25 = 116;
x_26 = lean::unbox_uint32(x_10);
x_27 = x_26 == x_25;
if (x_27 == 0)
{
uint32 x_28; uint32 x_29; uint8 x_30; 
lean::free_heap_obj(x_5);
lean::free_heap_obj(x_4);
x_28 = 120;
x_29 = lean::unbox_uint32(x_10);
x_30 = x_29 == x_28;
if (x_30 == 0)
{
uint32 x_31; uint32 x_32; uint8 x_33; 
x_31 = 117;
x_32 = lean::unbox_uint32(x_10);
lean::dec(x_10);
x_33 = x_32 == x_31;
if (x_33 == 0)
{
obj* x_34; obj* x_35; uint8 x_36; 
x_34 = l_Lean_Parser_parseQuotedChar___rarg___lambda__7___closed__1;
x_35 = l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x27___spec__4___rarg(x_34, x_2, x_1, x_11, x_7);
x_36 = !lean::is_exclusive(x_35);
if (x_36 == 0)
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_37 = lean::cnstr_get(x_35, 0);
x_38 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_37);
x_39 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_40 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_39, x_38);
lean::cnstr_set(x_35, 0, x_40);
return x_35;
}
else
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_41 = lean::cnstr_get(x_35, 0);
x_42 = lean::cnstr_get(x_35, 1);
lean::inc(x_42);
lean::inc(x_41);
lean::dec(x_35);
x_43 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_41);
x_44 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_45 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_44, x_43);
x_46 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
return x_46;
}
}
else
{
obj* x_47; obj* x_48; 
lean::dec(x_2);
x_47 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5(x_1, x_11, x_7);
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
if (lean::obj_tag(x_48) == 0)
{
obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_49 = lean::cnstr_get(x_47, 1);
lean::inc(x_49);
lean::dec(x_47);
x_50 = lean::cnstr_get(x_48, 0);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_48, 1);
lean::inc(x_51);
x_52 = lean::cnstr_get(x_48, 2);
lean::inc(x_52);
lean::dec(x_48);
x_53 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5(x_1, x_51, x_49);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
if (lean::obj_tag(x_54) == 0)
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; 
x_55 = lean::cnstr_get(x_53, 1);
lean::inc(x_55);
lean::dec(x_53);
x_56 = lean::cnstr_get(x_54, 0);
lean::inc(x_56);
x_57 = lean::cnstr_get(x_54, 1);
lean::inc(x_57);
x_58 = lean::cnstr_get(x_54, 2);
lean::inc(x_58);
lean::dec(x_54);
x_59 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5(x_1, x_57, x_55);
x_60 = lean::cnstr_get(x_59, 0);
lean::inc(x_60);
if (lean::obj_tag(x_60) == 0)
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; 
x_61 = lean::cnstr_get(x_59, 1);
lean::inc(x_61);
lean::dec(x_59);
x_62 = lean::cnstr_get(x_60, 0);
lean::inc(x_62);
x_63 = lean::cnstr_get(x_60, 1);
lean::inc(x_63);
x_64 = lean::cnstr_get(x_60, 2);
lean::inc(x_64);
lean::dec(x_60);
x_65 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5(x_1, x_63, x_61);
x_66 = lean::cnstr_get(x_65, 0);
lean::inc(x_66);
if (lean::obj_tag(x_66) == 0)
{
uint8 x_67; 
x_67 = !lean::is_exclusive(x_65);
if (x_67 == 0)
{
obj* x_68; uint8 x_69; 
x_68 = lean::cnstr_get(x_65, 0);
lean::dec(x_68);
x_69 = !lean::is_exclusive(x_66);
if (x_69 == 0)
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; uint32 x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; 
x_70 = lean::cnstr_get(x_66, 0);
x_71 = lean::cnstr_get(x_66, 2);
x_72 = lean::mk_nat_obj(16u);
x_73 = lean::nat_mul(x_72, x_50);
lean::dec(x_50);
x_74 = lean::nat_add(x_73, x_56);
lean::dec(x_56);
lean::dec(x_73);
x_75 = lean::nat_mul(x_72, x_74);
lean::dec(x_74);
x_76 = lean::nat_add(x_75, x_62);
lean::dec(x_62);
lean::dec(x_75);
x_77 = lean::nat_mul(x_72, x_76);
lean::dec(x_76);
x_78 = lean::nat_add(x_77, x_70);
lean::dec(x_70);
lean::dec(x_77);
x_79 = l_Char_ofNat(x_78);
lean::dec(x_78);
x_80 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_81 = lean::box_uint32(x_79);
lean::cnstr_set(x_66, 2, x_80);
lean::cnstr_set(x_66, 0, x_81);
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_71, x_66);
x_83 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_64, x_82);
x_84 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_83);
x_85 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_84);
x_86 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_85);
x_87 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_80, x_86);
lean::cnstr_set(x_65, 0, x_87);
return x_65;
}
else
{
obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; uint32 x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
x_88 = lean::cnstr_get(x_66, 0);
x_89 = lean::cnstr_get(x_66, 1);
x_90 = lean::cnstr_get(x_66, 2);
lean::inc(x_90);
lean::inc(x_89);
lean::inc(x_88);
lean::dec(x_66);
x_91 = lean::mk_nat_obj(16u);
x_92 = lean::nat_mul(x_91, x_50);
lean::dec(x_50);
x_93 = lean::nat_add(x_92, x_56);
lean::dec(x_56);
lean::dec(x_92);
x_94 = lean::nat_mul(x_91, x_93);
lean::dec(x_93);
x_95 = lean::nat_add(x_94, x_62);
lean::dec(x_62);
lean::dec(x_94);
x_96 = lean::nat_mul(x_91, x_95);
lean::dec(x_95);
x_97 = lean::nat_add(x_96, x_88);
lean::dec(x_88);
lean::dec(x_96);
x_98 = l_Char_ofNat(x_97);
lean::dec(x_97);
x_99 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_100 = lean::box_uint32(x_98);
x_101 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_101, 0, x_100);
lean::cnstr_set(x_101, 1, x_89);
lean::cnstr_set(x_101, 2, x_99);
x_102 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_90, x_101);
x_103 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_64, x_102);
x_104 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_103);
x_105 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_104);
x_106 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_105);
x_107 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_99, x_106);
lean::cnstr_set(x_65, 0, x_107);
return x_65;
}
}
else
{
obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; uint32 x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
x_108 = lean::cnstr_get(x_65, 1);
lean::inc(x_108);
lean::dec(x_65);
x_109 = lean::cnstr_get(x_66, 0);
lean::inc(x_109);
x_110 = lean::cnstr_get(x_66, 1);
lean::inc(x_110);
x_111 = lean::cnstr_get(x_66, 2);
lean::inc(x_111);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 lean::cnstr_release(x_66, 1);
 lean::cnstr_release(x_66, 2);
 x_112 = x_66;
} else {
 lean::dec_ref(x_66);
 x_112 = lean::box(0);
}
x_113 = lean::mk_nat_obj(16u);
x_114 = lean::nat_mul(x_113, x_50);
lean::dec(x_50);
x_115 = lean::nat_add(x_114, x_56);
lean::dec(x_56);
lean::dec(x_114);
x_116 = lean::nat_mul(x_113, x_115);
lean::dec(x_115);
x_117 = lean::nat_add(x_116, x_62);
lean::dec(x_62);
lean::dec(x_116);
x_118 = lean::nat_mul(x_113, x_117);
lean::dec(x_117);
x_119 = lean::nat_add(x_118, x_109);
lean::dec(x_109);
lean::dec(x_118);
x_120 = l_Char_ofNat(x_119);
lean::dec(x_119);
x_121 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_122 = lean::box_uint32(x_120);
if (lean::is_scalar(x_112)) {
 x_123 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_123 = x_112;
}
lean::cnstr_set(x_123, 0, x_122);
lean::cnstr_set(x_123, 1, x_110);
lean::cnstr_set(x_123, 2, x_121);
x_124 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_111, x_123);
x_125 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_64, x_124);
x_126 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_125);
x_127 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_126);
x_128 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_127);
x_129 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_121, x_128);
x_130 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_130, 0, x_129);
lean::cnstr_set(x_130, 1, x_108);
return x_130;
}
}
else
{
uint8 x_131; 
lean::dec(x_62);
lean::dec(x_56);
lean::dec(x_50);
x_131 = !lean::is_exclusive(x_65);
if (x_131 == 0)
{
obj* x_132; uint8 x_133; 
x_132 = lean::cnstr_get(x_65, 0);
lean::dec(x_132);
x_133 = !lean::is_exclusive(x_66);
if (x_133 == 0)
{
obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; 
x_134 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_64, x_66);
x_135 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_134);
x_136 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_135);
x_137 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_136);
x_138 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_139 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_138, x_137);
lean::cnstr_set(x_65, 0, x_139);
return x_65;
}
else
{
obj* x_140; uint8 x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; 
x_140 = lean::cnstr_get(x_66, 0);
x_141 = lean::cnstr_get_scalar<uint8>(x_66, sizeof(void*)*1);
lean::inc(x_140);
lean::dec(x_66);
x_142 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_142, 0, x_140);
lean::cnstr_set_scalar(x_142, sizeof(void*)*1, x_141);
x_143 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_64, x_142);
x_144 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_143);
x_145 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_144);
x_146 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_145);
x_147 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_148 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_147, x_146);
lean::cnstr_set(x_65, 0, x_148);
return x_65;
}
}
else
{
obj* x_149; obj* x_150; uint8 x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
x_149 = lean::cnstr_get(x_65, 1);
lean::inc(x_149);
lean::dec(x_65);
x_150 = lean::cnstr_get(x_66, 0);
lean::inc(x_150);
x_151 = lean::cnstr_get_scalar<uint8>(x_66, sizeof(void*)*1);
if (lean::is_exclusive(x_66)) {
 lean::cnstr_release(x_66, 0);
 x_152 = x_66;
} else {
 lean::dec_ref(x_66);
 x_152 = lean::box(0);
}
if (lean::is_scalar(x_152)) {
 x_153 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_153 = x_152;
}
lean::cnstr_set(x_153, 0, x_150);
lean::cnstr_set_scalar(x_153, sizeof(void*)*1, x_151);
x_154 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_64, x_153);
x_155 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_154);
x_156 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_155);
x_157 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_156);
x_158 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_159 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_158, x_157);
x_160 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_160, 0, x_159);
lean::cnstr_set(x_160, 1, x_149);
return x_160;
}
}
}
else
{
uint8 x_161; 
lean::dec(x_56);
lean::dec(x_50);
x_161 = !lean::is_exclusive(x_59);
if (x_161 == 0)
{
obj* x_162; uint8 x_163; 
x_162 = lean::cnstr_get(x_59, 0);
lean::dec(x_162);
x_163 = !lean::is_exclusive(x_60);
if (x_163 == 0)
{
obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
x_164 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_60);
x_165 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_164);
x_166 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_165);
x_167 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_168 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_167, x_166);
lean::cnstr_set(x_59, 0, x_168);
return x_59;
}
else
{
obj* x_169; uint8 x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; obj* x_175; obj* x_176; 
x_169 = lean::cnstr_get(x_60, 0);
x_170 = lean::cnstr_get_scalar<uint8>(x_60, sizeof(void*)*1);
lean::inc(x_169);
lean::dec(x_60);
x_171 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_171, 0, x_169);
lean::cnstr_set_scalar(x_171, sizeof(void*)*1, x_170);
x_172 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_171);
x_173 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_172);
x_174 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_173);
x_175 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_176 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_175, x_174);
lean::cnstr_set(x_59, 0, x_176);
return x_59;
}
}
else
{
obj* x_177; obj* x_178; uint8 x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; 
x_177 = lean::cnstr_get(x_59, 1);
lean::inc(x_177);
lean::dec(x_59);
x_178 = lean::cnstr_get(x_60, 0);
lean::inc(x_178);
x_179 = lean::cnstr_get_scalar<uint8>(x_60, sizeof(void*)*1);
if (lean::is_exclusive(x_60)) {
 lean::cnstr_release(x_60, 0);
 x_180 = x_60;
} else {
 lean::dec_ref(x_60);
 x_180 = lean::box(0);
}
if (lean::is_scalar(x_180)) {
 x_181 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_181 = x_180;
}
lean::cnstr_set(x_181, 0, x_178);
lean::cnstr_set_scalar(x_181, sizeof(void*)*1, x_179);
x_182 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_181);
x_183 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_182);
x_184 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_183);
x_185 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_186 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_185, x_184);
x_187 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_187, 0, x_186);
lean::cnstr_set(x_187, 1, x_177);
return x_187;
}
}
}
else
{
uint8 x_188; 
lean::dec(x_50);
x_188 = !lean::is_exclusive(x_53);
if (x_188 == 0)
{
obj* x_189; uint8 x_190; 
x_189 = lean::cnstr_get(x_53, 0);
lean::dec(x_189);
x_190 = !lean::is_exclusive(x_54);
if (x_190 == 0)
{
obj* x_191; obj* x_192; obj* x_193; obj* x_194; 
x_191 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_54);
x_192 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_191);
x_193 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_194 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_193, x_192);
lean::cnstr_set(x_53, 0, x_194);
return x_53;
}
else
{
obj* x_195; uint8 x_196; obj* x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; 
x_195 = lean::cnstr_get(x_54, 0);
x_196 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*1);
lean::inc(x_195);
lean::dec(x_54);
x_197 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_197, 0, x_195);
lean::cnstr_set_scalar(x_197, sizeof(void*)*1, x_196);
x_198 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_197);
x_199 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_198);
x_200 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_201 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_200, x_199);
lean::cnstr_set(x_53, 0, x_201);
return x_53;
}
}
else
{
obj* x_202; obj* x_203; uint8 x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; obj* x_209; obj* x_210; obj* x_211; 
x_202 = lean::cnstr_get(x_53, 1);
lean::inc(x_202);
lean::dec(x_53);
x_203 = lean::cnstr_get(x_54, 0);
lean::inc(x_203);
x_204 = lean::cnstr_get_scalar<uint8>(x_54, sizeof(void*)*1);
if (lean::is_exclusive(x_54)) {
 lean::cnstr_release(x_54, 0);
 x_205 = x_54;
} else {
 lean::dec_ref(x_54);
 x_205 = lean::box(0);
}
if (lean::is_scalar(x_205)) {
 x_206 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_206 = x_205;
}
lean::cnstr_set(x_206, 0, x_203);
lean::cnstr_set_scalar(x_206, sizeof(void*)*1, x_204);
x_207 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_52, x_206);
x_208 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_207);
x_209 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_210 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_209, x_208);
x_211 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_211, 0, x_210);
lean::cnstr_set(x_211, 1, x_202);
return x_211;
}
}
}
else
{
uint8 x_212; 
x_212 = !lean::is_exclusive(x_47);
if (x_212 == 0)
{
obj* x_213; uint8 x_214; 
x_213 = lean::cnstr_get(x_47, 0);
lean::dec(x_213);
x_214 = !lean::is_exclusive(x_48);
if (x_214 == 0)
{
obj* x_215; obj* x_216; obj* x_217; 
x_215 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_48);
x_216 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_217 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_216, x_215);
lean::cnstr_set(x_47, 0, x_217);
return x_47;
}
else
{
obj* x_218; uint8 x_219; obj* x_220; obj* x_221; obj* x_222; obj* x_223; 
x_218 = lean::cnstr_get(x_48, 0);
x_219 = lean::cnstr_get_scalar<uint8>(x_48, sizeof(void*)*1);
lean::inc(x_218);
lean::dec(x_48);
x_220 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_220, 0, x_218);
lean::cnstr_set_scalar(x_220, sizeof(void*)*1, x_219);
x_221 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_220);
x_222 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_223 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_222, x_221);
lean::cnstr_set(x_47, 0, x_223);
return x_47;
}
}
else
{
obj* x_224; obj* x_225; uint8 x_226; obj* x_227; obj* x_228; obj* x_229; obj* x_230; obj* x_231; obj* x_232; 
x_224 = lean::cnstr_get(x_47, 1);
lean::inc(x_224);
lean::dec(x_47);
x_225 = lean::cnstr_get(x_48, 0);
lean::inc(x_225);
x_226 = lean::cnstr_get_scalar<uint8>(x_48, sizeof(void*)*1);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 x_227 = x_48;
} else {
 lean::dec_ref(x_48);
 x_227 = lean::box(0);
}
if (lean::is_scalar(x_227)) {
 x_228 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_228 = x_227;
}
lean::cnstr_set(x_228, 0, x_225);
lean::cnstr_set_scalar(x_228, sizeof(void*)*1, x_226);
x_229 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_228);
x_230 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_231 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_230, x_229);
x_232 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_232, 0, x_231);
lean::cnstr_set(x_232, 1, x_224);
return x_232;
}
}
}
}
else
{
obj* x_233; obj* x_234; 
lean::dec(x_10);
lean::dec(x_2);
x_233 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5(x_1, x_11, x_7);
x_234 = lean::cnstr_get(x_233, 0);
lean::inc(x_234);
if (lean::obj_tag(x_234) == 0)
{
obj* x_235; obj* x_236; obj* x_237; obj* x_238; obj* x_239; obj* x_240; 
x_235 = lean::cnstr_get(x_233, 1);
lean::inc(x_235);
lean::dec(x_233);
x_236 = lean::cnstr_get(x_234, 0);
lean::inc(x_236);
x_237 = lean::cnstr_get(x_234, 1);
lean::inc(x_237);
x_238 = lean::cnstr_get(x_234, 2);
lean::inc(x_238);
lean::dec(x_234);
x_239 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5(x_1, x_237, x_235);
x_240 = lean::cnstr_get(x_239, 0);
lean::inc(x_240);
if (lean::obj_tag(x_240) == 0)
{
uint8 x_241; 
x_241 = !lean::is_exclusive(x_239);
if (x_241 == 0)
{
obj* x_242; uint8 x_243; 
x_242 = lean::cnstr_get(x_239, 0);
lean::dec(x_242);
x_243 = !lean::is_exclusive(x_240);
if (x_243 == 0)
{
obj* x_244; obj* x_245; obj* x_246; obj* x_247; obj* x_248; uint32 x_249; obj* x_250; obj* x_251; obj* x_252; obj* x_253; obj* x_254; obj* x_255; 
x_244 = lean::cnstr_get(x_240, 0);
x_245 = lean::cnstr_get(x_240, 2);
x_246 = lean::mk_nat_obj(16u);
x_247 = lean::nat_mul(x_246, x_236);
lean::dec(x_236);
x_248 = lean::nat_add(x_247, x_244);
lean::dec(x_244);
lean::dec(x_247);
x_249 = l_Char_ofNat(x_248);
lean::dec(x_248);
x_250 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_251 = lean::box_uint32(x_249);
lean::cnstr_set(x_240, 2, x_250);
lean::cnstr_set(x_240, 0, x_251);
x_252 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_245, x_240);
x_253 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_238, x_252);
x_254 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_253);
x_255 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_250, x_254);
lean::cnstr_set(x_239, 0, x_255);
return x_239;
}
else
{
obj* x_256; obj* x_257; obj* x_258; obj* x_259; obj* x_260; obj* x_261; uint32 x_262; obj* x_263; obj* x_264; obj* x_265; obj* x_266; obj* x_267; obj* x_268; obj* x_269; 
x_256 = lean::cnstr_get(x_240, 0);
x_257 = lean::cnstr_get(x_240, 1);
x_258 = lean::cnstr_get(x_240, 2);
lean::inc(x_258);
lean::inc(x_257);
lean::inc(x_256);
lean::dec(x_240);
x_259 = lean::mk_nat_obj(16u);
x_260 = lean::nat_mul(x_259, x_236);
lean::dec(x_236);
x_261 = lean::nat_add(x_260, x_256);
lean::dec(x_256);
lean::dec(x_260);
x_262 = l_Char_ofNat(x_261);
lean::dec(x_261);
x_263 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_264 = lean::box_uint32(x_262);
x_265 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_265, 0, x_264);
lean::cnstr_set(x_265, 1, x_257);
lean::cnstr_set(x_265, 2, x_263);
x_266 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_258, x_265);
x_267 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_238, x_266);
x_268 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_267);
x_269 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_263, x_268);
lean::cnstr_set(x_239, 0, x_269);
return x_239;
}
}
else
{
obj* x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; obj* x_275; obj* x_276; obj* x_277; uint32 x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; obj* x_283; obj* x_284; obj* x_285; obj* x_286; 
x_270 = lean::cnstr_get(x_239, 1);
lean::inc(x_270);
lean::dec(x_239);
x_271 = lean::cnstr_get(x_240, 0);
lean::inc(x_271);
x_272 = lean::cnstr_get(x_240, 1);
lean::inc(x_272);
x_273 = lean::cnstr_get(x_240, 2);
lean::inc(x_273);
if (lean::is_exclusive(x_240)) {
 lean::cnstr_release(x_240, 0);
 lean::cnstr_release(x_240, 1);
 lean::cnstr_release(x_240, 2);
 x_274 = x_240;
} else {
 lean::dec_ref(x_240);
 x_274 = lean::box(0);
}
x_275 = lean::mk_nat_obj(16u);
x_276 = lean::nat_mul(x_275, x_236);
lean::dec(x_236);
x_277 = lean::nat_add(x_276, x_271);
lean::dec(x_271);
lean::dec(x_276);
x_278 = l_Char_ofNat(x_277);
lean::dec(x_277);
x_279 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_280 = lean::box_uint32(x_278);
if (lean::is_scalar(x_274)) {
 x_281 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_281 = x_274;
}
lean::cnstr_set(x_281, 0, x_280);
lean::cnstr_set(x_281, 1, x_272);
lean::cnstr_set(x_281, 2, x_279);
x_282 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_273, x_281);
x_283 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_238, x_282);
x_284 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_283);
x_285 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_279, x_284);
x_286 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_286, 0, x_285);
lean::cnstr_set(x_286, 1, x_270);
return x_286;
}
}
else
{
uint8 x_287; 
lean::dec(x_236);
x_287 = !lean::is_exclusive(x_239);
if (x_287 == 0)
{
obj* x_288; uint8 x_289; 
x_288 = lean::cnstr_get(x_239, 0);
lean::dec(x_288);
x_289 = !lean::is_exclusive(x_240);
if (x_289 == 0)
{
obj* x_290; obj* x_291; obj* x_292; obj* x_293; 
x_290 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_238, x_240);
x_291 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_290);
x_292 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_293 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_292, x_291);
lean::cnstr_set(x_239, 0, x_293);
return x_239;
}
else
{
obj* x_294; uint8 x_295; obj* x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; 
x_294 = lean::cnstr_get(x_240, 0);
x_295 = lean::cnstr_get_scalar<uint8>(x_240, sizeof(void*)*1);
lean::inc(x_294);
lean::dec(x_240);
x_296 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_296, 0, x_294);
lean::cnstr_set_scalar(x_296, sizeof(void*)*1, x_295);
x_297 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_238, x_296);
x_298 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_297);
x_299 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_300 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_299, x_298);
lean::cnstr_set(x_239, 0, x_300);
return x_239;
}
}
else
{
obj* x_301; obj* x_302; uint8 x_303; obj* x_304; obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; obj* x_310; 
x_301 = lean::cnstr_get(x_239, 1);
lean::inc(x_301);
lean::dec(x_239);
x_302 = lean::cnstr_get(x_240, 0);
lean::inc(x_302);
x_303 = lean::cnstr_get_scalar<uint8>(x_240, sizeof(void*)*1);
if (lean::is_exclusive(x_240)) {
 lean::cnstr_release(x_240, 0);
 x_304 = x_240;
} else {
 lean::dec_ref(x_240);
 x_304 = lean::box(0);
}
if (lean::is_scalar(x_304)) {
 x_305 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_305 = x_304;
}
lean::cnstr_set(x_305, 0, x_302);
lean::cnstr_set_scalar(x_305, sizeof(void*)*1, x_303);
x_306 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_238, x_305);
x_307 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_306);
x_308 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_309 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_308, x_307);
x_310 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_310, 0, x_309);
lean::cnstr_set(x_310, 1, x_301);
return x_310;
}
}
}
else
{
uint8 x_311; 
x_311 = !lean::is_exclusive(x_233);
if (x_311 == 0)
{
obj* x_312; uint8 x_313; 
x_312 = lean::cnstr_get(x_233, 0);
lean::dec(x_312);
x_313 = !lean::is_exclusive(x_234);
if (x_313 == 0)
{
obj* x_314; obj* x_315; obj* x_316; 
x_314 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_234);
x_315 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_316 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_315, x_314);
lean::cnstr_set(x_233, 0, x_316);
return x_233;
}
else
{
obj* x_317; uint8 x_318; obj* x_319; obj* x_320; obj* x_321; obj* x_322; 
x_317 = lean::cnstr_get(x_234, 0);
x_318 = lean::cnstr_get_scalar<uint8>(x_234, sizeof(void*)*1);
lean::inc(x_317);
lean::dec(x_234);
x_319 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_319, 0, x_317);
lean::cnstr_set_scalar(x_319, sizeof(void*)*1, x_318);
x_320 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_319);
x_321 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_322 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_321, x_320);
lean::cnstr_set(x_233, 0, x_322);
return x_233;
}
}
else
{
obj* x_323; obj* x_324; uint8 x_325; obj* x_326; obj* x_327; obj* x_328; obj* x_329; obj* x_330; obj* x_331; 
x_323 = lean::cnstr_get(x_233, 1);
lean::inc(x_323);
lean::dec(x_233);
x_324 = lean::cnstr_get(x_234, 0);
lean::inc(x_324);
x_325 = lean::cnstr_get_scalar<uint8>(x_234, sizeof(void*)*1);
if (lean::is_exclusive(x_234)) {
 lean::cnstr_release(x_234, 0);
 x_326 = x_234;
} else {
 lean::dec_ref(x_234);
 x_326 = lean::box(0);
}
if (lean::is_scalar(x_326)) {
 x_327 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_327 = x_326;
}
lean::cnstr_set(x_327, 0, x_324);
lean::cnstr_set_scalar(x_327, sizeof(void*)*1, x_325);
x_328 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_327);
x_329 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_330 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_329, x_328);
x_331 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_331, 0, x_330);
lean::cnstr_set(x_331, 1, x_323);
return x_331;
}
}
}
}
else
{
uint32 x_332; obj* x_333; obj* x_334; obj* x_335; obj* x_336; 
lean::dec(x_10);
lean::dec(x_2);
x_332 = 9;
x_333 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_334 = lean::box_uint32(x_332);
lean::cnstr_set(x_5, 2, x_333);
lean::cnstr_set(x_5, 0, x_334);
x_335 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_5);
x_336 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_333, x_335);
lean::cnstr_set(x_4, 0, x_336);
return x_4;
}
}
else
{
uint32 x_337; obj* x_338; obj* x_339; obj* x_340; obj* x_341; 
lean::dec(x_10);
lean::dec(x_2);
x_337 = 10;
x_338 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_339 = lean::box_uint32(x_337);
lean::cnstr_set(x_5, 2, x_338);
lean::cnstr_set(x_5, 0, x_339);
x_340 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_5);
x_341 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_338, x_340);
lean::cnstr_set(x_4, 0, x_341);
return x_4;
}
}
else
{
obj* x_342; obj* x_343; obj* x_344; obj* x_345; 
lean::dec(x_10);
lean::dec(x_2);
x_342 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_343 = lean::box_uint32(x_19);
lean::cnstr_set(x_5, 2, x_342);
lean::cnstr_set(x_5, 0, x_343);
x_344 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_5);
x_345 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_342, x_344);
lean::cnstr_set(x_4, 0, x_345);
return x_4;
}
}
else
{
obj* x_346; obj* x_347; obj* x_348; obj* x_349; 
lean::dec(x_10);
lean::dec(x_2);
x_346 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_347 = lean::box_uint32(x_16);
lean::cnstr_set(x_5, 2, x_346);
lean::cnstr_set(x_5, 0, x_347);
x_348 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_5);
x_349 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_346, x_348);
lean::cnstr_set(x_4, 0, x_349);
return x_4;
}
}
else
{
obj* x_350; obj* x_351; obj* x_352; obj* x_353; 
lean::dec(x_10);
lean::dec(x_2);
x_350 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_351 = lean::box_uint32(x_13);
lean::cnstr_set(x_5, 2, x_350);
lean::cnstr_set(x_5, 0, x_351);
x_352 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_5);
x_353 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_350, x_352);
lean::cnstr_set(x_4, 0, x_353);
return x_4;
}
}
else
{
obj* x_354; obj* x_355; obj* x_356; uint32 x_357; uint32 x_358; uint8 x_359; 
x_354 = lean::cnstr_get(x_5, 0);
x_355 = lean::cnstr_get(x_5, 1);
x_356 = lean::cnstr_get(x_5, 2);
lean::inc(x_356);
lean::inc(x_355);
lean::inc(x_354);
lean::dec(x_5);
x_357 = 92;
x_358 = lean::unbox_uint32(x_354);
x_359 = x_358 == x_357;
if (x_359 == 0)
{
uint32 x_360; uint32 x_361; uint8 x_362; 
x_360 = 34;
x_361 = lean::unbox_uint32(x_354);
x_362 = x_361 == x_360;
if (x_362 == 0)
{
uint32 x_363; uint32 x_364; uint8 x_365; 
x_363 = 39;
x_364 = lean::unbox_uint32(x_354);
x_365 = x_364 == x_363;
if (x_365 == 0)
{
uint32 x_366; uint32 x_367; uint8 x_368; 
x_366 = 110;
x_367 = lean::unbox_uint32(x_354);
x_368 = x_367 == x_366;
if (x_368 == 0)
{
uint32 x_369; uint32 x_370; uint8 x_371; 
x_369 = 116;
x_370 = lean::unbox_uint32(x_354);
x_371 = x_370 == x_369;
if (x_371 == 0)
{
uint32 x_372; uint32 x_373; uint8 x_374; 
lean::free_heap_obj(x_4);
x_372 = 120;
x_373 = lean::unbox_uint32(x_354);
x_374 = x_373 == x_372;
if (x_374 == 0)
{
uint32 x_375; uint32 x_376; uint8 x_377; 
x_375 = 117;
x_376 = lean::unbox_uint32(x_354);
lean::dec(x_354);
x_377 = x_376 == x_375;
if (x_377 == 0)
{
obj* x_378; obj* x_379; obj* x_380; obj* x_381; obj* x_382; obj* x_383; obj* x_384; obj* x_385; obj* x_386; 
x_378 = l_Lean_Parser_parseQuotedChar___rarg___lambda__7___closed__1;
x_379 = l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x27___spec__4___rarg(x_378, x_2, x_1, x_355, x_7);
x_380 = lean::cnstr_get(x_379, 0);
lean::inc(x_380);
x_381 = lean::cnstr_get(x_379, 1);
lean::inc(x_381);
if (lean::is_exclusive(x_379)) {
 lean::cnstr_release(x_379, 0);
 lean::cnstr_release(x_379, 1);
 x_382 = x_379;
} else {
 lean::dec_ref(x_379);
 x_382 = lean::box(0);
}
x_383 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_356, x_380);
x_384 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_385 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_384, x_383);
if (lean::is_scalar(x_382)) {
 x_386 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_386 = x_382;
}
lean::cnstr_set(x_386, 0, x_385);
lean::cnstr_set(x_386, 1, x_381);
return x_386;
}
else
{
obj* x_387; obj* x_388; 
lean::dec(x_2);
x_387 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5(x_1, x_355, x_7);
x_388 = lean::cnstr_get(x_387, 0);
lean::inc(x_388);
if (lean::obj_tag(x_388) == 0)
{
obj* x_389; obj* x_390; obj* x_391; obj* x_392; obj* x_393; obj* x_394; 
x_389 = lean::cnstr_get(x_387, 1);
lean::inc(x_389);
lean::dec(x_387);
x_390 = lean::cnstr_get(x_388, 0);
lean::inc(x_390);
x_391 = lean::cnstr_get(x_388, 1);
lean::inc(x_391);
x_392 = lean::cnstr_get(x_388, 2);
lean::inc(x_392);
lean::dec(x_388);
x_393 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5(x_1, x_391, x_389);
x_394 = lean::cnstr_get(x_393, 0);
lean::inc(x_394);
if (lean::obj_tag(x_394) == 0)
{
obj* x_395; obj* x_396; obj* x_397; obj* x_398; obj* x_399; obj* x_400; 
x_395 = lean::cnstr_get(x_393, 1);
lean::inc(x_395);
lean::dec(x_393);
x_396 = lean::cnstr_get(x_394, 0);
lean::inc(x_396);
x_397 = lean::cnstr_get(x_394, 1);
lean::inc(x_397);
x_398 = lean::cnstr_get(x_394, 2);
lean::inc(x_398);
lean::dec(x_394);
x_399 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5(x_1, x_397, x_395);
x_400 = lean::cnstr_get(x_399, 0);
lean::inc(x_400);
if (lean::obj_tag(x_400) == 0)
{
obj* x_401; obj* x_402; obj* x_403; obj* x_404; obj* x_405; obj* x_406; 
x_401 = lean::cnstr_get(x_399, 1);
lean::inc(x_401);
lean::dec(x_399);
x_402 = lean::cnstr_get(x_400, 0);
lean::inc(x_402);
x_403 = lean::cnstr_get(x_400, 1);
lean::inc(x_403);
x_404 = lean::cnstr_get(x_400, 2);
lean::inc(x_404);
lean::dec(x_400);
x_405 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5(x_1, x_403, x_401);
x_406 = lean::cnstr_get(x_405, 0);
lean::inc(x_406);
if (lean::obj_tag(x_406) == 0)
{
obj* x_407; obj* x_408; obj* x_409; obj* x_410; obj* x_411; obj* x_412; obj* x_413; obj* x_414; obj* x_415; obj* x_416; obj* x_417; obj* x_418; obj* x_419; uint32 x_420; obj* x_421; obj* x_422; obj* x_423; obj* x_424; obj* x_425; obj* x_426; obj* x_427; obj* x_428; obj* x_429; obj* x_430; 
x_407 = lean::cnstr_get(x_405, 1);
lean::inc(x_407);
if (lean::is_exclusive(x_405)) {
 lean::cnstr_release(x_405, 0);
 lean::cnstr_release(x_405, 1);
 x_408 = x_405;
} else {
 lean::dec_ref(x_405);
 x_408 = lean::box(0);
}
x_409 = lean::cnstr_get(x_406, 0);
lean::inc(x_409);
x_410 = lean::cnstr_get(x_406, 1);
lean::inc(x_410);
x_411 = lean::cnstr_get(x_406, 2);
lean::inc(x_411);
if (lean::is_exclusive(x_406)) {
 lean::cnstr_release(x_406, 0);
 lean::cnstr_release(x_406, 1);
 lean::cnstr_release(x_406, 2);
 x_412 = x_406;
} else {
 lean::dec_ref(x_406);
 x_412 = lean::box(0);
}
x_413 = lean::mk_nat_obj(16u);
x_414 = lean::nat_mul(x_413, x_390);
lean::dec(x_390);
x_415 = lean::nat_add(x_414, x_396);
lean::dec(x_396);
lean::dec(x_414);
x_416 = lean::nat_mul(x_413, x_415);
lean::dec(x_415);
x_417 = lean::nat_add(x_416, x_402);
lean::dec(x_402);
lean::dec(x_416);
x_418 = lean::nat_mul(x_413, x_417);
lean::dec(x_417);
x_419 = lean::nat_add(x_418, x_409);
lean::dec(x_409);
lean::dec(x_418);
x_420 = l_Char_ofNat(x_419);
lean::dec(x_419);
x_421 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_422 = lean::box_uint32(x_420);
if (lean::is_scalar(x_412)) {
 x_423 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_423 = x_412;
}
lean::cnstr_set(x_423, 0, x_422);
lean::cnstr_set(x_423, 1, x_410);
lean::cnstr_set(x_423, 2, x_421);
x_424 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_411, x_423);
x_425 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_404, x_424);
x_426 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_398, x_425);
x_427 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_392, x_426);
x_428 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_356, x_427);
x_429 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_421, x_428);
if (lean::is_scalar(x_408)) {
 x_430 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_430 = x_408;
}
lean::cnstr_set(x_430, 0, x_429);
lean::cnstr_set(x_430, 1, x_407);
return x_430;
}
else
{
obj* x_431; obj* x_432; obj* x_433; uint8 x_434; obj* x_435; obj* x_436; obj* x_437; obj* x_438; obj* x_439; obj* x_440; obj* x_441; obj* x_442; obj* x_443; 
lean::dec(x_402);
lean::dec(x_396);
lean::dec(x_390);
x_431 = lean::cnstr_get(x_405, 1);
lean::inc(x_431);
if (lean::is_exclusive(x_405)) {
 lean::cnstr_release(x_405, 0);
 lean::cnstr_release(x_405, 1);
 x_432 = x_405;
} else {
 lean::dec_ref(x_405);
 x_432 = lean::box(0);
}
x_433 = lean::cnstr_get(x_406, 0);
lean::inc(x_433);
x_434 = lean::cnstr_get_scalar<uint8>(x_406, sizeof(void*)*1);
if (lean::is_exclusive(x_406)) {
 lean::cnstr_release(x_406, 0);
 x_435 = x_406;
} else {
 lean::dec_ref(x_406);
 x_435 = lean::box(0);
}
if (lean::is_scalar(x_435)) {
 x_436 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_436 = x_435;
}
lean::cnstr_set(x_436, 0, x_433);
lean::cnstr_set_scalar(x_436, sizeof(void*)*1, x_434);
x_437 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_404, x_436);
x_438 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_398, x_437);
x_439 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_392, x_438);
x_440 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_356, x_439);
x_441 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_442 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_441, x_440);
if (lean::is_scalar(x_432)) {
 x_443 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_443 = x_432;
}
lean::cnstr_set(x_443, 0, x_442);
lean::cnstr_set(x_443, 1, x_431);
return x_443;
}
}
else
{
obj* x_444; obj* x_445; obj* x_446; uint8 x_447; obj* x_448; obj* x_449; obj* x_450; obj* x_451; obj* x_452; obj* x_453; obj* x_454; obj* x_455; 
lean::dec(x_396);
lean::dec(x_390);
x_444 = lean::cnstr_get(x_399, 1);
lean::inc(x_444);
if (lean::is_exclusive(x_399)) {
 lean::cnstr_release(x_399, 0);
 lean::cnstr_release(x_399, 1);
 x_445 = x_399;
} else {
 lean::dec_ref(x_399);
 x_445 = lean::box(0);
}
x_446 = lean::cnstr_get(x_400, 0);
lean::inc(x_446);
x_447 = lean::cnstr_get_scalar<uint8>(x_400, sizeof(void*)*1);
if (lean::is_exclusive(x_400)) {
 lean::cnstr_release(x_400, 0);
 x_448 = x_400;
} else {
 lean::dec_ref(x_400);
 x_448 = lean::box(0);
}
if (lean::is_scalar(x_448)) {
 x_449 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_449 = x_448;
}
lean::cnstr_set(x_449, 0, x_446);
lean::cnstr_set_scalar(x_449, sizeof(void*)*1, x_447);
x_450 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_398, x_449);
x_451 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_392, x_450);
x_452 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_356, x_451);
x_453 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_454 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_453, x_452);
if (lean::is_scalar(x_445)) {
 x_455 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_455 = x_445;
}
lean::cnstr_set(x_455, 0, x_454);
lean::cnstr_set(x_455, 1, x_444);
return x_455;
}
}
else
{
obj* x_456; obj* x_457; obj* x_458; uint8 x_459; obj* x_460; obj* x_461; obj* x_462; obj* x_463; obj* x_464; obj* x_465; obj* x_466; 
lean::dec(x_390);
x_456 = lean::cnstr_get(x_393, 1);
lean::inc(x_456);
if (lean::is_exclusive(x_393)) {
 lean::cnstr_release(x_393, 0);
 lean::cnstr_release(x_393, 1);
 x_457 = x_393;
} else {
 lean::dec_ref(x_393);
 x_457 = lean::box(0);
}
x_458 = lean::cnstr_get(x_394, 0);
lean::inc(x_458);
x_459 = lean::cnstr_get_scalar<uint8>(x_394, sizeof(void*)*1);
if (lean::is_exclusive(x_394)) {
 lean::cnstr_release(x_394, 0);
 x_460 = x_394;
} else {
 lean::dec_ref(x_394);
 x_460 = lean::box(0);
}
if (lean::is_scalar(x_460)) {
 x_461 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_461 = x_460;
}
lean::cnstr_set(x_461, 0, x_458);
lean::cnstr_set_scalar(x_461, sizeof(void*)*1, x_459);
x_462 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_392, x_461);
x_463 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_356, x_462);
x_464 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_465 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_464, x_463);
if (lean::is_scalar(x_457)) {
 x_466 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_466 = x_457;
}
lean::cnstr_set(x_466, 0, x_465);
lean::cnstr_set(x_466, 1, x_456);
return x_466;
}
}
else
{
obj* x_467; obj* x_468; obj* x_469; uint8 x_470; obj* x_471; obj* x_472; obj* x_473; obj* x_474; obj* x_475; obj* x_476; 
x_467 = lean::cnstr_get(x_387, 1);
lean::inc(x_467);
if (lean::is_exclusive(x_387)) {
 lean::cnstr_release(x_387, 0);
 lean::cnstr_release(x_387, 1);
 x_468 = x_387;
} else {
 lean::dec_ref(x_387);
 x_468 = lean::box(0);
}
x_469 = lean::cnstr_get(x_388, 0);
lean::inc(x_469);
x_470 = lean::cnstr_get_scalar<uint8>(x_388, sizeof(void*)*1);
if (lean::is_exclusive(x_388)) {
 lean::cnstr_release(x_388, 0);
 x_471 = x_388;
} else {
 lean::dec_ref(x_388);
 x_471 = lean::box(0);
}
if (lean::is_scalar(x_471)) {
 x_472 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_472 = x_471;
}
lean::cnstr_set(x_472, 0, x_469);
lean::cnstr_set_scalar(x_472, sizeof(void*)*1, x_470);
x_473 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_356, x_472);
x_474 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_475 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_474, x_473);
if (lean::is_scalar(x_468)) {
 x_476 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_476 = x_468;
}
lean::cnstr_set(x_476, 0, x_475);
lean::cnstr_set(x_476, 1, x_467);
return x_476;
}
}
}
else
{
obj* x_477; obj* x_478; 
lean::dec(x_354);
lean::dec(x_2);
x_477 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5(x_1, x_355, x_7);
x_478 = lean::cnstr_get(x_477, 0);
lean::inc(x_478);
if (lean::obj_tag(x_478) == 0)
{
obj* x_479; obj* x_480; obj* x_481; obj* x_482; obj* x_483; obj* x_484; 
x_479 = lean::cnstr_get(x_477, 1);
lean::inc(x_479);
lean::dec(x_477);
x_480 = lean::cnstr_get(x_478, 0);
lean::inc(x_480);
x_481 = lean::cnstr_get(x_478, 1);
lean::inc(x_481);
x_482 = lean::cnstr_get(x_478, 2);
lean::inc(x_482);
lean::dec(x_478);
x_483 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5(x_1, x_481, x_479);
x_484 = lean::cnstr_get(x_483, 0);
lean::inc(x_484);
if (lean::obj_tag(x_484) == 0)
{
obj* x_485; obj* x_486; obj* x_487; obj* x_488; obj* x_489; obj* x_490; obj* x_491; obj* x_492; obj* x_493; uint32 x_494; obj* x_495; obj* x_496; obj* x_497; obj* x_498; obj* x_499; obj* x_500; obj* x_501; obj* x_502; 
x_485 = lean::cnstr_get(x_483, 1);
lean::inc(x_485);
if (lean::is_exclusive(x_483)) {
 lean::cnstr_release(x_483, 0);
 lean::cnstr_release(x_483, 1);
 x_486 = x_483;
} else {
 lean::dec_ref(x_483);
 x_486 = lean::box(0);
}
x_487 = lean::cnstr_get(x_484, 0);
lean::inc(x_487);
x_488 = lean::cnstr_get(x_484, 1);
lean::inc(x_488);
x_489 = lean::cnstr_get(x_484, 2);
lean::inc(x_489);
if (lean::is_exclusive(x_484)) {
 lean::cnstr_release(x_484, 0);
 lean::cnstr_release(x_484, 1);
 lean::cnstr_release(x_484, 2);
 x_490 = x_484;
} else {
 lean::dec_ref(x_484);
 x_490 = lean::box(0);
}
x_491 = lean::mk_nat_obj(16u);
x_492 = lean::nat_mul(x_491, x_480);
lean::dec(x_480);
x_493 = lean::nat_add(x_492, x_487);
lean::dec(x_487);
lean::dec(x_492);
x_494 = l_Char_ofNat(x_493);
lean::dec(x_493);
x_495 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_496 = lean::box_uint32(x_494);
if (lean::is_scalar(x_490)) {
 x_497 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_497 = x_490;
}
lean::cnstr_set(x_497, 0, x_496);
lean::cnstr_set(x_497, 1, x_488);
lean::cnstr_set(x_497, 2, x_495);
x_498 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_489, x_497);
x_499 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_482, x_498);
x_500 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_356, x_499);
x_501 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_495, x_500);
if (lean::is_scalar(x_486)) {
 x_502 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_502 = x_486;
}
lean::cnstr_set(x_502, 0, x_501);
lean::cnstr_set(x_502, 1, x_485);
return x_502;
}
else
{
obj* x_503; obj* x_504; obj* x_505; uint8 x_506; obj* x_507; obj* x_508; obj* x_509; obj* x_510; obj* x_511; obj* x_512; obj* x_513; 
lean::dec(x_480);
x_503 = lean::cnstr_get(x_483, 1);
lean::inc(x_503);
if (lean::is_exclusive(x_483)) {
 lean::cnstr_release(x_483, 0);
 lean::cnstr_release(x_483, 1);
 x_504 = x_483;
} else {
 lean::dec_ref(x_483);
 x_504 = lean::box(0);
}
x_505 = lean::cnstr_get(x_484, 0);
lean::inc(x_505);
x_506 = lean::cnstr_get_scalar<uint8>(x_484, sizeof(void*)*1);
if (lean::is_exclusive(x_484)) {
 lean::cnstr_release(x_484, 0);
 x_507 = x_484;
} else {
 lean::dec_ref(x_484);
 x_507 = lean::box(0);
}
if (lean::is_scalar(x_507)) {
 x_508 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_508 = x_507;
}
lean::cnstr_set(x_508, 0, x_505);
lean::cnstr_set_scalar(x_508, sizeof(void*)*1, x_506);
x_509 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_482, x_508);
x_510 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_356, x_509);
x_511 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_512 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_511, x_510);
if (lean::is_scalar(x_504)) {
 x_513 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_513 = x_504;
}
lean::cnstr_set(x_513, 0, x_512);
lean::cnstr_set(x_513, 1, x_503);
return x_513;
}
}
else
{
obj* x_514; obj* x_515; obj* x_516; uint8 x_517; obj* x_518; obj* x_519; obj* x_520; obj* x_521; obj* x_522; obj* x_523; 
x_514 = lean::cnstr_get(x_477, 1);
lean::inc(x_514);
if (lean::is_exclusive(x_477)) {
 lean::cnstr_release(x_477, 0);
 lean::cnstr_release(x_477, 1);
 x_515 = x_477;
} else {
 lean::dec_ref(x_477);
 x_515 = lean::box(0);
}
x_516 = lean::cnstr_get(x_478, 0);
lean::inc(x_516);
x_517 = lean::cnstr_get_scalar<uint8>(x_478, sizeof(void*)*1);
if (lean::is_exclusive(x_478)) {
 lean::cnstr_release(x_478, 0);
 x_518 = x_478;
} else {
 lean::dec_ref(x_478);
 x_518 = lean::box(0);
}
if (lean::is_scalar(x_518)) {
 x_519 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_519 = x_518;
}
lean::cnstr_set(x_519, 0, x_516);
lean::cnstr_set_scalar(x_519, sizeof(void*)*1, x_517);
x_520 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_356, x_519);
x_521 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_522 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_521, x_520);
if (lean::is_scalar(x_515)) {
 x_523 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_523 = x_515;
}
lean::cnstr_set(x_523, 0, x_522);
lean::cnstr_set(x_523, 1, x_514);
return x_523;
}
}
}
else
{
uint32 x_524; obj* x_525; obj* x_526; obj* x_527; obj* x_528; obj* x_529; 
lean::dec(x_354);
lean::dec(x_2);
x_524 = 9;
x_525 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_526 = lean::box_uint32(x_524);
x_527 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_527, 0, x_526);
lean::cnstr_set(x_527, 1, x_355);
lean::cnstr_set(x_527, 2, x_525);
x_528 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_356, x_527);
x_529 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_525, x_528);
lean::cnstr_set(x_4, 0, x_529);
return x_4;
}
}
else
{
uint32 x_530; obj* x_531; obj* x_532; obj* x_533; obj* x_534; obj* x_535; 
lean::dec(x_354);
lean::dec(x_2);
x_530 = 10;
x_531 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_532 = lean::box_uint32(x_530);
x_533 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_533, 0, x_532);
lean::cnstr_set(x_533, 1, x_355);
lean::cnstr_set(x_533, 2, x_531);
x_534 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_356, x_533);
x_535 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_531, x_534);
lean::cnstr_set(x_4, 0, x_535);
return x_4;
}
}
else
{
obj* x_536; obj* x_537; obj* x_538; obj* x_539; obj* x_540; 
lean::dec(x_354);
lean::dec(x_2);
x_536 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_537 = lean::box_uint32(x_363);
x_538 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_538, 0, x_537);
lean::cnstr_set(x_538, 1, x_355);
lean::cnstr_set(x_538, 2, x_536);
x_539 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_356, x_538);
x_540 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_536, x_539);
lean::cnstr_set(x_4, 0, x_540);
return x_4;
}
}
else
{
obj* x_541; obj* x_542; obj* x_543; obj* x_544; obj* x_545; 
lean::dec(x_354);
lean::dec(x_2);
x_541 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_542 = lean::box_uint32(x_360);
x_543 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_543, 0, x_542);
lean::cnstr_set(x_543, 1, x_355);
lean::cnstr_set(x_543, 2, x_541);
x_544 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_356, x_543);
x_545 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_541, x_544);
lean::cnstr_set(x_4, 0, x_545);
return x_4;
}
}
else
{
obj* x_546; obj* x_547; obj* x_548; obj* x_549; obj* x_550; 
lean::dec(x_354);
lean::dec(x_2);
x_546 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_547 = lean::box_uint32(x_357);
x_548 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_548, 0, x_547);
lean::cnstr_set(x_548, 1, x_355);
lean::cnstr_set(x_548, 2, x_546);
x_549 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_356, x_548);
x_550 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_546, x_549);
lean::cnstr_set(x_4, 0, x_550);
return x_4;
}
}
}
else
{
obj* x_551; obj* x_552; obj* x_553; obj* x_554; obj* x_555; uint32 x_556; uint32 x_557; uint8 x_558; 
x_551 = lean::cnstr_get(x_4, 1);
lean::inc(x_551);
lean::dec(x_4);
x_552 = lean::cnstr_get(x_5, 0);
lean::inc(x_552);
x_553 = lean::cnstr_get(x_5, 1);
lean::inc(x_553);
x_554 = lean::cnstr_get(x_5, 2);
lean::inc(x_554);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_555 = x_5;
} else {
 lean::dec_ref(x_5);
 x_555 = lean::box(0);
}
x_556 = 92;
x_557 = lean::unbox_uint32(x_552);
x_558 = x_557 == x_556;
if (x_558 == 0)
{
uint32 x_559; uint32 x_560; uint8 x_561; 
x_559 = 34;
x_560 = lean::unbox_uint32(x_552);
x_561 = x_560 == x_559;
if (x_561 == 0)
{
uint32 x_562; uint32 x_563; uint8 x_564; 
x_562 = 39;
x_563 = lean::unbox_uint32(x_552);
x_564 = x_563 == x_562;
if (x_564 == 0)
{
uint32 x_565; uint32 x_566; uint8 x_567; 
x_565 = 110;
x_566 = lean::unbox_uint32(x_552);
x_567 = x_566 == x_565;
if (x_567 == 0)
{
uint32 x_568; uint32 x_569; uint8 x_570; 
x_568 = 116;
x_569 = lean::unbox_uint32(x_552);
x_570 = x_569 == x_568;
if (x_570 == 0)
{
uint32 x_571; uint32 x_572; uint8 x_573; 
lean::dec(x_555);
x_571 = 120;
x_572 = lean::unbox_uint32(x_552);
x_573 = x_572 == x_571;
if (x_573 == 0)
{
uint32 x_574; uint32 x_575; uint8 x_576; 
x_574 = 117;
x_575 = lean::unbox_uint32(x_552);
lean::dec(x_552);
x_576 = x_575 == x_574;
if (x_576 == 0)
{
obj* x_577; obj* x_578; obj* x_579; obj* x_580; obj* x_581; obj* x_582; obj* x_583; obj* x_584; obj* x_585; 
x_577 = l_Lean_Parser_parseQuotedChar___rarg___lambda__7___closed__1;
x_578 = l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x27___spec__4___rarg(x_577, x_2, x_1, x_553, x_551);
x_579 = lean::cnstr_get(x_578, 0);
lean::inc(x_579);
x_580 = lean::cnstr_get(x_578, 1);
lean::inc(x_580);
if (lean::is_exclusive(x_578)) {
 lean::cnstr_release(x_578, 0);
 lean::cnstr_release(x_578, 1);
 x_581 = x_578;
} else {
 lean::dec_ref(x_578);
 x_581 = lean::box(0);
}
x_582 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_554, x_579);
x_583 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_584 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_583, x_582);
if (lean::is_scalar(x_581)) {
 x_585 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_585 = x_581;
}
lean::cnstr_set(x_585, 0, x_584);
lean::cnstr_set(x_585, 1, x_580);
return x_585;
}
else
{
obj* x_586; obj* x_587; 
lean::dec(x_2);
x_586 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5(x_1, x_553, x_551);
x_587 = lean::cnstr_get(x_586, 0);
lean::inc(x_587);
if (lean::obj_tag(x_587) == 0)
{
obj* x_588; obj* x_589; obj* x_590; obj* x_591; obj* x_592; obj* x_593; 
x_588 = lean::cnstr_get(x_586, 1);
lean::inc(x_588);
lean::dec(x_586);
x_589 = lean::cnstr_get(x_587, 0);
lean::inc(x_589);
x_590 = lean::cnstr_get(x_587, 1);
lean::inc(x_590);
x_591 = lean::cnstr_get(x_587, 2);
lean::inc(x_591);
lean::dec(x_587);
x_592 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5(x_1, x_590, x_588);
x_593 = lean::cnstr_get(x_592, 0);
lean::inc(x_593);
if (lean::obj_tag(x_593) == 0)
{
obj* x_594; obj* x_595; obj* x_596; obj* x_597; obj* x_598; obj* x_599; 
x_594 = lean::cnstr_get(x_592, 1);
lean::inc(x_594);
lean::dec(x_592);
x_595 = lean::cnstr_get(x_593, 0);
lean::inc(x_595);
x_596 = lean::cnstr_get(x_593, 1);
lean::inc(x_596);
x_597 = lean::cnstr_get(x_593, 2);
lean::inc(x_597);
lean::dec(x_593);
x_598 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5(x_1, x_596, x_594);
x_599 = lean::cnstr_get(x_598, 0);
lean::inc(x_599);
if (lean::obj_tag(x_599) == 0)
{
obj* x_600; obj* x_601; obj* x_602; obj* x_603; obj* x_604; obj* x_605; 
x_600 = lean::cnstr_get(x_598, 1);
lean::inc(x_600);
lean::dec(x_598);
x_601 = lean::cnstr_get(x_599, 0);
lean::inc(x_601);
x_602 = lean::cnstr_get(x_599, 1);
lean::inc(x_602);
x_603 = lean::cnstr_get(x_599, 2);
lean::inc(x_603);
lean::dec(x_599);
x_604 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5(x_1, x_602, x_600);
x_605 = lean::cnstr_get(x_604, 0);
lean::inc(x_605);
if (lean::obj_tag(x_605) == 0)
{
obj* x_606; obj* x_607; obj* x_608; obj* x_609; obj* x_610; obj* x_611; obj* x_612; obj* x_613; obj* x_614; obj* x_615; obj* x_616; obj* x_617; obj* x_618; uint32 x_619; obj* x_620; obj* x_621; obj* x_622; obj* x_623; obj* x_624; obj* x_625; obj* x_626; obj* x_627; obj* x_628; obj* x_629; 
x_606 = lean::cnstr_get(x_604, 1);
lean::inc(x_606);
if (lean::is_exclusive(x_604)) {
 lean::cnstr_release(x_604, 0);
 lean::cnstr_release(x_604, 1);
 x_607 = x_604;
} else {
 lean::dec_ref(x_604);
 x_607 = lean::box(0);
}
x_608 = lean::cnstr_get(x_605, 0);
lean::inc(x_608);
x_609 = lean::cnstr_get(x_605, 1);
lean::inc(x_609);
x_610 = lean::cnstr_get(x_605, 2);
lean::inc(x_610);
if (lean::is_exclusive(x_605)) {
 lean::cnstr_release(x_605, 0);
 lean::cnstr_release(x_605, 1);
 lean::cnstr_release(x_605, 2);
 x_611 = x_605;
} else {
 lean::dec_ref(x_605);
 x_611 = lean::box(0);
}
x_612 = lean::mk_nat_obj(16u);
x_613 = lean::nat_mul(x_612, x_589);
lean::dec(x_589);
x_614 = lean::nat_add(x_613, x_595);
lean::dec(x_595);
lean::dec(x_613);
x_615 = lean::nat_mul(x_612, x_614);
lean::dec(x_614);
x_616 = lean::nat_add(x_615, x_601);
lean::dec(x_601);
lean::dec(x_615);
x_617 = lean::nat_mul(x_612, x_616);
lean::dec(x_616);
x_618 = lean::nat_add(x_617, x_608);
lean::dec(x_608);
lean::dec(x_617);
x_619 = l_Char_ofNat(x_618);
lean::dec(x_618);
x_620 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_621 = lean::box_uint32(x_619);
if (lean::is_scalar(x_611)) {
 x_622 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_622 = x_611;
}
lean::cnstr_set(x_622, 0, x_621);
lean::cnstr_set(x_622, 1, x_609);
lean::cnstr_set(x_622, 2, x_620);
x_623 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_610, x_622);
x_624 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_603, x_623);
x_625 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_597, x_624);
x_626 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_591, x_625);
x_627 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_554, x_626);
x_628 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_620, x_627);
if (lean::is_scalar(x_607)) {
 x_629 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_629 = x_607;
}
lean::cnstr_set(x_629, 0, x_628);
lean::cnstr_set(x_629, 1, x_606);
return x_629;
}
else
{
obj* x_630; obj* x_631; obj* x_632; uint8 x_633; obj* x_634; obj* x_635; obj* x_636; obj* x_637; obj* x_638; obj* x_639; obj* x_640; obj* x_641; obj* x_642; 
lean::dec(x_601);
lean::dec(x_595);
lean::dec(x_589);
x_630 = lean::cnstr_get(x_604, 1);
lean::inc(x_630);
if (lean::is_exclusive(x_604)) {
 lean::cnstr_release(x_604, 0);
 lean::cnstr_release(x_604, 1);
 x_631 = x_604;
} else {
 lean::dec_ref(x_604);
 x_631 = lean::box(0);
}
x_632 = lean::cnstr_get(x_605, 0);
lean::inc(x_632);
x_633 = lean::cnstr_get_scalar<uint8>(x_605, sizeof(void*)*1);
if (lean::is_exclusive(x_605)) {
 lean::cnstr_release(x_605, 0);
 x_634 = x_605;
} else {
 lean::dec_ref(x_605);
 x_634 = lean::box(0);
}
if (lean::is_scalar(x_634)) {
 x_635 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_635 = x_634;
}
lean::cnstr_set(x_635, 0, x_632);
lean::cnstr_set_scalar(x_635, sizeof(void*)*1, x_633);
x_636 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_603, x_635);
x_637 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_597, x_636);
x_638 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_591, x_637);
x_639 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_554, x_638);
x_640 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_641 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_640, x_639);
if (lean::is_scalar(x_631)) {
 x_642 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_642 = x_631;
}
lean::cnstr_set(x_642, 0, x_641);
lean::cnstr_set(x_642, 1, x_630);
return x_642;
}
}
else
{
obj* x_643; obj* x_644; obj* x_645; uint8 x_646; obj* x_647; obj* x_648; obj* x_649; obj* x_650; obj* x_651; obj* x_652; obj* x_653; obj* x_654; 
lean::dec(x_595);
lean::dec(x_589);
x_643 = lean::cnstr_get(x_598, 1);
lean::inc(x_643);
if (lean::is_exclusive(x_598)) {
 lean::cnstr_release(x_598, 0);
 lean::cnstr_release(x_598, 1);
 x_644 = x_598;
} else {
 lean::dec_ref(x_598);
 x_644 = lean::box(0);
}
x_645 = lean::cnstr_get(x_599, 0);
lean::inc(x_645);
x_646 = lean::cnstr_get_scalar<uint8>(x_599, sizeof(void*)*1);
if (lean::is_exclusive(x_599)) {
 lean::cnstr_release(x_599, 0);
 x_647 = x_599;
} else {
 lean::dec_ref(x_599);
 x_647 = lean::box(0);
}
if (lean::is_scalar(x_647)) {
 x_648 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_648 = x_647;
}
lean::cnstr_set(x_648, 0, x_645);
lean::cnstr_set_scalar(x_648, sizeof(void*)*1, x_646);
x_649 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_597, x_648);
x_650 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_591, x_649);
x_651 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_554, x_650);
x_652 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_653 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_652, x_651);
if (lean::is_scalar(x_644)) {
 x_654 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_654 = x_644;
}
lean::cnstr_set(x_654, 0, x_653);
lean::cnstr_set(x_654, 1, x_643);
return x_654;
}
}
else
{
obj* x_655; obj* x_656; obj* x_657; uint8 x_658; obj* x_659; obj* x_660; obj* x_661; obj* x_662; obj* x_663; obj* x_664; obj* x_665; 
lean::dec(x_589);
x_655 = lean::cnstr_get(x_592, 1);
lean::inc(x_655);
if (lean::is_exclusive(x_592)) {
 lean::cnstr_release(x_592, 0);
 lean::cnstr_release(x_592, 1);
 x_656 = x_592;
} else {
 lean::dec_ref(x_592);
 x_656 = lean::box(0);
}
x_657 = lean::cnstr_get(x_593, 0);
lean::inc(x_657);
x_658 = lean::cnstr_get_scalar<uint8>(x_593, sizeof(void*)*1);
if (lean::is_exclusive(x_593)) {
 lean::cnstr_release(x_593, 0);
 x_659 = x_593;
} else {
 lean::dec_ref(x_593);
 x_659 = lean::box(0);
}
if (lean::is_scalar(x_659)) {
 x_660 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_660 = x_659;
}
lean::cnstr_set(x_660, 0, x_657);
lean::cnstr_set_scalar(x_660, sizeof(void*)*1, x_658);
x_661 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_591, x_660);
x_662 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_554, x_661);
x_663 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_664 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_663, x_662);
if (lean::is_scalar(x_656)) {
 x_665 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_665 = x_656;
}
lean::cnstr_set(x_665, 0, x_664);
lean::cnstr_set(x_665, 1, x_655);
return x_665;
}
}
else
{
obj* x_666; obj* x_667; obj* x_668; uint8 x_669; obj* x_670; obj* x_671; obj* x_672; obj* x_673; obj* x_674; obj* x_675; 
x_666 = lean::cnstr_get(x_586, 1);
lean::inc(x_666);
if (lean::is_exclusive(x_586)) {
 lean::cnstr_release(x_586, 0);
 lean::cnstr_release(x_586, 1);
 x_667 = x_586;
} else {
 lean::dec_ref(x_586);
 x_667 = lean::box(0);
}
x_668 = lean::cnstr_get(x_587, 0);
lean::inc(x_668);
x_669 = lean::cnstr_get_scalar<uint8>(x_587, sizeof(void*)*1);
if (lean::is_exclusive(x_587)) {
 lean::cnstr_release(x_587, 0);
 x_670 = x_587;
} else {
 lean::dec_ref(x_587);
 x_670 = lean::box(0);
}
if (lean::is_scalar(x_670)) {
 x_671 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_671 = x_670;
}
lean::cnstr_set(x_671, 0, x_668);
lean::cnstr_set_scalar(x_671, sizeof(void*)*1, x_669);
x_672 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_554, x_671);
x_673 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_674 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_673, x_672);
if (lean::is_scalar(x_667)) {
 x_675 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_675 = x_667;
}
lean::cnstr_set(x_675, 0, x_674);
lean::cnstr_set(x_675, 1, x_666);
return x_675;
}
}
}
else
{
obj* x_676; obj* x_677; 
lean::dec(x_552);
lean::dec(x_2);
x_676 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5(x_1, x_553, x_551);
x_677 = lean::cnstr_get(x_676, 0);
lean::inc(x_677);
if (lean::obj_tag(x_677) == 0)
{
obj* x_678; obj* x_679; obj* x_680; obj* x_681; obj* x_682; obj* x_683; 
x_678 = lean::cnstr_get(x_676, 1);
lean::inc(x_678);
lean::dec(x_676);
x_679 = lean::cnstr_get(x_677, 0);
lean::inc(x_679);
x_680 = lean::cnstr_get(x_677, 1);
lean::inc(x_680);
x_681 = lean::cnstr_get(x_677, 2);
lean::inc(x_681);
lean::dec(x_677);
x_682 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5(x_1, x_680, x_678);
x_683 = lean::cnstr_get(x_682, 0);
lean::inc(x_683);
if (lean::obj_tag(x_683) == 0)
{
obj* x_684; obj* x_685; obj* x_686; obj* x_687; obj* x_688; obj* x_689; obj* x_690; obj* x_691; obj* x_692; uint32 x_693; obj* x_694; obj* x_695; obj* x_696; obj* x_697; obj* x_698; obj* x_699; obj* x_700; obj* x_701; 
x_684 = lean::cnstr_get(x_682, 1);
lean::inc(x_684);
if (lean::is_exclusive(x_682)) {
 lean::cnstr_release(x_682, 0);
 lean::cnstr_release(x_682, 1);
 x_685 = x_682;
} else {
 lean::dec_ref(x_682);
 x_685 = lean::box(0);
}
x_686 = lean::cnstr_get(x_683, 0);
lean::inc(x_686);
x_687 = lean::cnstr_get(x_683, 1);
lean::inc(x_687);
x_688 = lean::cnstr_get(x_683, 2);
lean::inc(x_688);
if (lean::is_exclusive(x_683)) {
 lean::cnstr_release(x_683, 0);
 lean::cnstr_release(x_683, 1);
 lean::cnstr_release(x_683, 2);
 x_689 = x_683;
} else {
 lean::dec_ref(x_683);
 x_689 = lean::box(0);
}
x_690 = lean::mk_nat_obj(16u);
x_691 = lean::nat_mul(x_690, x_679);
lean::dec(x_679);
x_692 = lean::nat_add(x_691, x_686);
lean::dec(x_686);
lean::dec(x_691);
x_693 = l_Char_ofNat(x_692);
lean::dec(x_692);
x_694 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_695 = lean::box_uint32(x_693);
if (lean::is_scalar(x_689)) {
 x_696 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_696 = x_689;
}
lean::cnstr_set(x_696, 0, x_695);
lean::cnstr_set(x_696, 1, x_687);
lean::cnstr_set(x_696, 2, x_694);
x_697 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_688, x_696);
x_698 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_681, x_697);
x_699 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_554, x_698);
x_700 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_694, x_699);
if (lean::is_scalar(x_685)) {
 x_701 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_701 = x_685;
}
lean::cnstr_set(x_701, 0, x_700);
lean::cnstr_set(x_701, 1, x_684);
return x_701;
}
else
{
obj* x_702; obj* x_703; obj* x_704; uint8 x_705; obj* x_706; obj* x_707; obj* x_708; obj* x_709; obj* x_710; obj* x_711; obj* x_712; 
lean::dec(x_679);
x_702 = lean::cnstr_get(x_682, 1);
lean::inc(x_702);
if (lean::is_exclusive(x_682)) {
 lean::cnstr_release(x_682, 0);
 lean::cnstr_release(x_682, 1);
 x_703 = x_682;
} else {
 lean::dec_ref(x_682);
 x_703 = lean::box(0);
}
x_704 = lean::cnstr_get(x_683, 0);
lean::inc(x_704);
x_705 = lean::cnstr_get_scalar<uint8>(x_683, sizeof(void*)*1);
if (lean::is_exclusive(x_683)) {
 lean::cnstr_release(x_683, 0);
 x_706 = x_683;
} else {
 lean::dec_ref(x_683);
 x_706 = lean::box(0);
}
if (lean::is_scalar(x_706)) {
 x_707 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_707 = x_706;
}
lean::cnstr_set(x_707, 0, x_704);
lean::cnstr_set_scalar(x_707, sizeof(void*)*1, x_705);
x_708 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_681, x_707);
x_709 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_554, x_708);
x_710 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_711 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_710, x_709);
if (lean::is_scalar(x_703)) {
 x_712 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_712 = x_703;
}
lean::cnstr_set(x_712, 0, x_711);
lean::cnstr_set(x_712, 1, x_702);
return x_712;
}
}
else
{
obj* x_713; obj* x_714; obj* x_715; uint8 x_716; obj* x_717; obj* x_718; obj* x_719; obj* x_720; obj* x_721; obj* x_722; 
x_713 = lean::cnstr_get(x_676, 1);
lean::inc(x_713);
if (lean::is_exclusive(x_676)) {
 lean::cnstr_release(x_676, 0);
 lean::cnstr_release(x_676, 1);
 x_714 = x_676;
} else {
 lean::dec_ref(x_676);
 x_714 = lean::box(0);
}
x_715 = lean::cnstr_get(x_677, 0);
lean::inc(x_715);
x_716 = lean::cnstr_get_scalar<uint8>(x_677, sizeof(void*)*1);
if (lean::is_exclusive(x_677)) {
 lean::cnstr_release(x_677, 0);
 x_717 = x_677;
} else {
 lean::dec_ref(x_677);
 x_717 = lean::box(0);
}
if (lean::is_scalar(x_717)) {
 x_718 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_718 = x_717;
}
lean::cnstr_set(x_718, 0, x_715);
lean::cnstr_set_scalar(x_718, sizeof(void*)*1, x_716);
x_719 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_554, x_718);
x_720 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_721 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_720, x_719);
if (lean::is_scalar(x_714)) {
 x_722 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_722 = x_714;
}
lean::cnstr_set(x_722, 0, x_721);
lean::cnstr_set(x_722, 1, x_713);
return x_722;
}
}
}
else
{
uint32 x_723; obj* x_724; obj* x_725; obj* x_726; obj* x_727; obj* x_728; obj* x_729; 
lean::dec(x_552);
lean::dec(x_2);
x_723 = 9;
x_724 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_725 = lean::box_uint32(x_723);
if (lean::is_scalar(x_555)) {
 x_726 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_726 = x_555;
}
lean::cnstr_set(x_726, 0, x_725);
lean::cnstr_set(x_726, 1, x_553);
lean::cnstr_set(x_726, 2, x_724);
x_727 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_554, x_726);
x_728 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_724, x_727);
x_729 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_729, 0, x_728);
lean::cnstr_set(x_729, 1, x_551);
return x_729;
}
}
else
{
uint32 x_730; obj* x_731; obj* x_732; obj* x_733; obj* x_734; obj* x_735; obj* x_736; 
lean::dec(x_552);
lean::dec(x_2);
x_730 = 10;
x_731 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_732 = lean::box_uint32(x_730);
if (lean::is_scalar(x_555)) {
 x_733 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_733 = x_555;
}
lean::cnstr_set(x_733, 0, x_732);
lean::cnstr_set(x_733, 1, x_553);
lean::cnstr_set(x_733, 2, x_731);
x_734 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_554, x_733);
x_735 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_731, x_734);
x_736 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_736, 0, x_735);
lean::cnstr_set(x_736, 1, x_551);
return x_736;
}
}
else
{
obj* x_737; obj* x_738; obj* x_739; obj* x_740; obj* x_741; obj* x_742; 
lean::dec(x_552);
lean::dec(x_2);
x_737 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_738 = lean::box_uint32(x_562);
if (lean::is_scalar(x_555)) {
 x_739 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_739 = x_555;
}
lean::cnstr_set(x_739, 0, x_738);
lean::cnstr_set(x_739, 1, x_553);
lean::cnstr_set(x_739, 2, x_737);
x_740 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_554, x_739);
x_741 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_737, x_740);
x_742 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_742, 0, x_741);
lean::cnstr_set(x_742, 1, x_551);
return x_742;
}
}
else
{
obj* x_743; obj* x_744; obj* x_745; obj* x_746; obj* x_747; obj* x_748; 
lean::dec(x_552);
lean::dec(x_2);
x_743 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_744 = lean::box_uint32(x_559);
if (lean::is_scalar(x_555)) {
 x_745 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_745 = x_555;
}
lean::cnstr_set(x_745, 0, x_744);
lean::cnstr_set(x_745, 1, x_553);
lean::cnstr_set(x_745, 2, x_743);
x_746 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_554, x_745);
x_747 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_743, x_746);
x_748 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_748, 0, x_747);
lean::cnstr_set(x_748, 1, x_551);
return x_748;
}
}
else
{
obj* x_749; obj* x_750; obj* x_751; obj* x_752; obj* x_753; obj* x_754; 
lean::dec(x_552);
lean::dec(x_2);
x_749 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_750 = lean::box_uint32(x_556);
if (lean::is_scalar(x_555)) {
 x_751 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_751 = x_555;
}
lean::cnstr_set(x_751, 0, x_750);
lean::cnstr_set(x_751, 1, x_553);
lean::cnstr_set(x_751, 2, x_749);
x_752 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_554, x_751);
x_753 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_749, x_752);
x_754 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_754, 0, x_753);
lean::cnstr_set(x_754, 1, x_551);
return x_754;
}
}
}
else
{
uint8 x_755; 
lean::dec(x_2);
x_755 = !lean::is_exclusive(x_4);
if (x_755 == 0)
{
obj* x_756; uint8 x_757; 
x_756 = lean::cnstr_get(x_4, 0);
lean::dec(x_756);
x_757 = !lean::is_exclusive(x_5);
if (x_757 == 0)
{
obj* x_758; obj* x_759; 
x_758 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_759 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_758, x_5);
lean::cnstr_set(x_4, 0, x_759);
return x_4;
}
else
{
obj* x_760; uint8 x_761; obj* x_762; obj* x_763; obj* x_764; 
x_760 = lean::cnstr_get(x_5, 0);
x_761 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
lean::inc(x_760);
lean::dec(x_5);
x_762 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_762, 0, x_760);
lean::cnstr_set_scalar(x_762, sizeof(void*)*1, x_761);
x_763 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_764 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_763, x_762);
lean::cnstr_set(x_4, 0, x_764);
return x_4;
}
}
else
{
obj* x_765; obj* x_766; uint8 x_767; obj* x_768; obj* x_769; obj* x_770; obj* x_771; obj* x_772; 
x_765 = lean::cnstr_get(x_4, 1);
lean::inc(x_765);
lean::dec(x_4);
x_766 = lean::cnstr_get(x_5, 0);
lean::inc(x_766);
x_767 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_768 = x_5;
} else {
 lean::dec_ref(x_5);
 x_768 = lean::box(0);
}
if (lean::is_scalar(x_768)) {
 x_769 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_769 = x_768;
}
lean::cnstr_set(x_769, 0, x_766);
lean::cnstr_set_scalar(x_769, sizeof(void*)*1, x_767);
x_770 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_771 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_770, x_769);
x_772 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_772, 0, x_771);
lean::cnstr_set(x_772, 1, x_765);
return x_772;
}
}
}
}
obj* l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_x27___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; uint8 x_7; 
x_6 = lean::mk_nat_obj(0u);
x_7 = lean::nat_dec_eq(x_1, x_6);
if (x_7 == 0)
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::mk_nat_obj(1u);
x_9 = lean::nat_sub(x_1, x_8);
x_10 = l_Lean_Parser_MonadParsec_any___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__2(x_3, x_4, x_5);
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
if (lean::obj_tag(x_11) == 0)
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_10);
if (x_12 == 0)
{
obj* x_13; obj* x_14; uint8 x_15; 
x_13 = lean::cnstr_get(x_10, 1);
x_14 = lean::cnstr_get(x_10, 0);
lean::dec(x_14);
x_15 = !lean::is_exclusive(x_11);
if (x_15 == 0)
{
obj* x_16; obj* x_17; obj* x_18; uint32 x_19; uint32 x_20; uint8 x_21; 
x_16 = lean::cnstr_get(x_11, 0);
x_17 = lean::cnstr_get(x_11, 1);
x_18 = lean::cnstr_get(x_11, 2);
x_19 = 92;
x_20 = lean::unbox_uint32(x_16);
x_21 = x_20 == x_19;
if (x_21 == 0)
{
uint32 x_22; uint32 x_23; uint8 x_24; 
x_22 = 34;
x_23 = lean::unbox_uint32(x_16);
x_24 = x_23 == x_22;
if (x_24 == 0)
{
uint32 x_25; obj* x_26; obj* x_27; uint8 x_28; 
lean::free_heap_obj(x_11);
lean::free_heap_obj(x_10);
x_25 = lean::unbox_uint32(x_16);
lean::dec(x_16);
x_26 = lean::string_push(x_2, x_25);
x_27 = l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_x27___spec__2(x_9, x_26, x_3, x_17, x_13);
lean::dec(x_9);
x_28 = !lean::is_exclusive(x_27);
if (x_28 == 0)
{
obj* x_29; obj* x_30; 
x_29 = lean::cnstr_get(x_27, 0);
x_30 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_29);
lean::cnstr_set(x_27, 0, x_30);
return x_27;
}
else
{
obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_31 = lean::cnstr_get(x_27, 0);
x_32 = lean::cnstr_get(x_27, 1);
lean::inc(x_32);
lean::inc(x_31);
lean::dec(x_27);
x_33 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_31);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_32);
return x_34;
}
}
else
{
obj* x_35; obj* x_36; 
lean::dec(x_16);
lean::dec(x_9);
x_35 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_11, 2, x_35);
lean::cnstr_set(x_11, 0, x_2);
x_36 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_11);
lean::cnstr_set(x_10, 0, x_36);
return x_10;
}
}
else
{
obj* x_37; obj* x_38; 
lean::free_heap_obj(x_11);
lean::dec(x_16);
lean::free_heap_obj(x_10);
x_37 = l_Lean_Parser_parseQuotedChar___at_Lean_Parser_stringLit_x27___spec__3(x_3, x_17, x_13);
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; uint32 x_43; obj* x_44; obj* x_45; uint8 x_46; 
x_39 = lean::cnstr_get(x_37, 1);
lean::inc(x_39);
lean::dec(x_37);
x_40 = lean::cnstr_get(x_38, 0);
lean::inc(x_40);
x_41 = lean::cnstr_get(x_38, 1);
lean::inc(x_41);
x_42 = lean::cnstr_get(x_38, 2);
lean::inc(x_42);
lean::dec(x_38);
x_43 = lean::unbox_uint32(x_40);
lean::dec(x_40);
x_44 = lean::string_push(x_2, x_43);
x_45 = l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_x27___spec__2(x_9, x_44, x_3, x_41, x_39);
lean::dec(x_9);
x_46 = !lean::is_exclusive(x_45);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_49; 
x_47 = lean::cnstr_get(x_45, 0);
x_48 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_42, x_47);
x_49 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_48);
lean::cnstr_set(x_45, 0, x_49);
return x_45;
}
else
{
obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_50 = lean::cnstr_get(x_45, 0);
x_51 = lean::cnstr_get(x_45, 1);
lean::inc(x_51);
lean::inc(x_50);
lean::dec(x_45);
x_52 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_42, x_50);
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_52);
x_54 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_51);
return x_54;
}
}
else
{
uint8 x_55; 
lean::dec(x_9);
lean::dec(x_2);
x_55 = !lean::is_exclusive(x_37);
if (x_55 == 0)
{
obj* x_56; uint8 x_57; 
x_56 = lean::cnstr_get(x_37, 0);
lean::dec(x_56);
x_57 = !lean::is_exclusive(x_38);
if (x_57 == 0)
{
obj* x_58; 
x_58 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_38);
lean::cnstr_set(x_37, 0, x_58);
return x_37;
}
else
{
obj* x_59; uint8 x_60; obj* x_61; obj* x_62; 
x_59 = lean::cnstr_get(x_38, 0);
x_60 = lean::cnstr_get_scalar<uint8>(x_38, sizeof(void*)*1);
lean::inc(x_59);
lean::dec(x_38);
x_61 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_61, 0, x_59);
lean::cnstr_set_scalar(x_61, sizeof(void*)*1, x_60);
x_62 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_61);
lean::cnstr_set(x_37, 0, x_62);
return x_37;
}
}
else
{
obj* x_63; obj* x_64; uint8 x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_63 = lean::cnstr_get(x_37, 1);
lean::inc(x_63);
lean::dec(x_37);
x_64 = lean::cnstr_get(x_38, 0);
lean::inc(x_64);
x_65 = lean::cnstr_get_scalar<uint8>(x_38, sizeof(void*)*1);
if (lean::is_exclusive(x_38)) {
 lean::cnstr_release(x_38, 0);
 x_66 = x_38;
} else {
 lean::dec_ref(x_38);
 x_66 = lean::box(0);
}
if (lean::is_scalar(x_66)) {
 x_67 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_67 = x_66;
}
lean::cnstr_set(x_67, 0, x_64);
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_65);
x_68 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_67);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_63);
return x_69;
}
}
}
}
else
{
obj* x_70; obj* x_71; obj* x_72; uint32 x_73; uint32 x_74; uint8 x_75; 
x_70 = lean::cnstr_get(x_11, 0);
x_71 = lean::cnstr_get(x_11, 1);
x_72 = lean::cnstr_get(x_11, 2);
lean::inc(x_72);
lean::inc(x_71);
lean::inc(x_70);
lean::dec(x_11);
x_73 = 92;
x_74 = lean::unbox_uint32(x_70);
x_75 = x_74 == x_73;
if (x_75 == 0)
{
uint32 x_76; uint32 x_77; uint8 x_78; 
x_76 = 34;
x_77 = lean::unbox_uint32(x_70);
x_78 = x_77 == x_76;
if (x_78 == 0)
{
uint32 x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; 
lean::free_heap_obj(x_10);
x_79 = lean::unbox_uint32(x_70);
lean::dec(x_70);
x_80 = lean::string_push(x_2, x_79);
x_81 = l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_x27___spec__2(x_9, x_80, x_3, x_71, x_13);
lean::dec(x_9);
x_82 = lean::cnstr_get(x_81, 0);
lean::inc(x_82);
x_83 = lean::cnstr_get(x_81, 1);
lean::inc(x_83);
if (lean::is_exclusive(x_81)) {
 lean::cnstr_release(x_81, 0);
 lean::cnstr_release(x_81, 1);
 x_84 = x_81;
} else {
 lean::dec_ref(x_81);
 x_84 = lean::box(0);
}
x_85 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_72, x_82);
if (lean::is_scalar(x_84)) {
 x_86 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_86 = x_84;
}
lean::cnstr_set(x_86, 0, x_85);
lean::cnstr_set(x_86, 1, x_83);
return x_86;
}
else
{
obj* x_87; obj* x_88; obj* x_89; 
lean::dec(x_70);
lean::dec(x_9);
x_87 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_88 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_88, 0, x_2);
lean::cnstr_set(x_88, 1, x_71);
lean::cnstr_set(x_88, 2, x_87);
x_89 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_72, x_88);
lean::cnstr_set(x_10, 0, x_89);
return x_10;
}
}
else
{
obj* x_90; obj* x_91; 
lean::dec(x_70);
lean::free_heap_obj(x_10);
x_90 = l_Lean_Parser_parseQuotedChar___at_Lean_Parser_stringLit_x27___spec__3(x_3, x_71, x_13);
x_91 = lean::cnstr_get(x_90, 0);
lean::inc(x_91);
if (lean::obj_tag(x_91) == 0)
{
obj* x_92; obj* x_93; obj* x_94; obj* x_95; uint32 x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_92 = lean::cnstr_get(x_90, 1);
lean::inc(x_92);
lean::dec(x_90);
x_93 = lean::cnstr_get(x_91, 0);
lean::inc(x_93);
x_94 = lean::cnstr_get(x_91, 1);
lean::inc(x_94);
x_95 = lean::cnstr_get(x_91, 2);
lean::inc(x_95);
lean::dec(x_91);
x_96 = lean::unbox_uint32(x_93);
lean::dec(x_93);
x_97 = lean::string_push(x_2, x_96);
x_98 = l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_x27___spec__2(x_9, x_97, x_3, x_94, x_92);
lean::dec(x_9);
x_99 = lean::cnstr_get(x_98, 0);
lean::inc(x_99);
x_100 = lean::cnstr_get(x_98, 1);
lean::inc(x_100);
if (lean::is_exclusive(x_98)) {
 lean::cnstr_release(x_98, 0);
 lean::cnstr_release(x_98, 1);
 x_101 = x_98;
} else {
 lean::dec_ref(x_98);
 x_101 = lean::box(0);
}
x_102 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_95, x_99);
x_103 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_72, x_102);
if (lean::is_scalar(x_101)) {
 x_104 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_104 = x_101;
}
lean::cnstr_set(x_104, 0, x_103);
lean::cnstr_set(x_104, 1, x_100);
return x_104;
}
else
{
obj* x_105; obj* x_106; obj* x_107; uint8 x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
lean::dec(x_9);
lean::dec(x_2);
x_105 = lean::cnstr_get(x_90, 1);
lean::inc(x_105);
if (lean::is_exclusive(x_90)) {
 lean::cnstr_release(x_90, 0);
 lean::cnstr_release(x_90, 1);
 x_106 = x_90;
} else {
 lean::dec_ref(x_90);
 x_106 = lean::box(0);
}
x_107 = lean::cnstr_get(x_91, 0);
lean::inc(x_107);
x_108 = lean::cnstr_get_scalar<uint8>(x_91, sizeof(void*)*1);
if (lean::is_exclusive(x_91)) {
 lean::cnstr_release(x_91, 0);
 x_109 = x_91;
} else {
 lean::dec_ref(x_91);
 x_109 = lean::box(0);
}
if (lean::is_scalar(x_109)) {
 x_110 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_110 = x_109;
}
lean::cnstr_set(x_110, 0, x_107);
lean::cnstr_set_scalar(x_110, sizeof(void*)*1, x_108);
x_111 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_72, x_110);
if (lean::is_scalar(x_106)) {
 x_112 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_112 = x_106;
}
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_105);
return x_112;
}
}
}
}
else
{
obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; uint32 x_118; uint32 x_119; uint8 x_120; 
x_113 = lean::cnstr_get(x_10, 1);
lean::inc(x_113);
lean::dec(x_10);
x_114 = lean::cnstr_get(x_11, 0);
lean::inc(x_114);
x_115 = lean::cnstr_get(x_11, 1);
lean::inc(x_115);
x_116 = lean::cnstr_get(x_11, 2);
lean::inc(x_116);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 lean::cnstr_release(x_11, 1);
 lean::cnstr_release(x_11, 2);
 x_117 = x_11;
} else {
 lean::dec_ref(x_11);
 x_117 = lean::box(0);
}
x_118 = 92;
x_119 = lean::unbox_uint32(x_114);
x_120 = x_119 == x_118;
if (x_120 == 0)
{
uint32 x_121; uint32 x_122; uint8 x_123; 
x_121 = 34;
x_122 = lean::unbox_uint32(x_114);
x_123 = x_122 == x_121;
if (x_123 == 0)
{
uint32 x_124; obj* x_125; obj* x_126; obj* x_127; obj* x_128; obj* x_129; obj* x_130; obj* x_131; 
lean::dec(x_117);
x_124 = lean::unbox_uint32(x_114);
lean::dec(x_114);
x_125 = lean::string_push(x_2, x_124);
x_126 = l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_x27___spec__2(x_9, x_125, x_3, x_115, x_113);
lean::dec(x_9);
x_127 = lean::cnstr_get(x_126, 0);
lean::inc(x_127);
x_128 = lean::cnstr_get(x_126, 1);
lean::inc(x_128);
if (lean::is_exclusive(x_126)) {
 lean::cnstr_release(x_126, 0);
 lean::cnstr_release(x_126, 1);
 x_129 = x_126;
} else {
 lean::dec_ref(x_126);
 x_129 = lean::box(0);
}
x_130 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_116, x_127);
if (lean::is_scalar(x_129)) {
 x_131 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_131 = x_129;
}
lean::cnstr_set(x_131, 0, x_130);
lean::cnstr_set(x_131, 1, x_128);
return x_131;
}
else
{
obj* x_132; obj* x_133; obj* x_134; obj* x_135; 
lean::dec(x_114);
lean::dec(x_9);
x_132 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_117)) {
 x_133 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_133 = x_117;
}
lean::cnstr_set(x_133, 0, x_2);
lean::cnstr_set(x_133, 1, x_115);
lean::cnstr_set(x_133, 2, x_132);
x_134 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_116, x_133);
x_135 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_135, 0, x_134);
lean::cnstr_set(x_135, 1, x_113);
return x_135;
}
}
else
{
obj* x_136; obj* x_137; 
lean::dec(x_117);
lean::dec(x_114);
x_136 = l_Lean_Parser_parseQuotedChar___at_Lean_Parser_stringLit_x27___spec__3(x_3, x_115, x_113);
x_137 = lean::cnstr_get(x_136, 0);
lean::inc(x_137);
if (lean::obj_tag(x_137) == 0)
{
obj* x_138; obj* x_139; obj* x_140; obj* x_141; uint32 x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; obj* x_150; 
x_138 = lean::cnstr_get(x_136, 1);
lean::inc(x_138);
lean::dec(x_136);
x_139 = lean::cnstr_get(x_137, 0);
lean::inc(x_139);
x_140 = lean::cnstr_get(x_137, 1);
lean::inc(x_140);
x_141 = lean::cnstr_get(x_137, 2);
lean::inc(x_141);
lean::dec(x_137);
x_142 = lean::unbox_uint32(x_139);
lean::dec(x_139);
x_143 = lean::string_push(x_2, x_142);
x_144 = l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_x27___spec__2(x_9, x_143, x_3, x_140, x_138);
lean::dec(x_9);
x_145 = lean::cnstr_get(x_144, 0);
lean::inc(x_145);
x_146 = lean::cnstr_get(x_144, 1);
lean::inc(x_146);
if (lean::is_exclusive(x_144)) {
 lean::cnstr_release(x_144, 0);
 lean::cnstr_release(x_144, 1);
 x_147 = x_144;
} else {
 lean::dec_ref(x_144);
 x_147 = lean::box(0);
}
x_148 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_141, x_145);
x_149 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_116, x_148);
if (lean::is_scalar(x_147)) {
 x_150 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_150 = x_147;
}
lean::cnstr_set(x_150, 0, x_149);
lean::cnstr_set(x_150, 1, x_146);
return x_150;
}
else
{
obj* x_151; obj* x_152; obj* x_153; uint8 x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; 
lean::dec(x_9);
lean::dec(x_2);
x_151 = lean::cnstr_get(x_136, 1);
lean::inc(x_151);
if (lean::is_exclusive(x_136)) {
 lean::cnstr_release(x_136, 0);
 lean::cnstr_release(x_136, 1);
 x_152 = x_136;
} else {
 lean::dec_ref(x_136);
 x_152 = lean::box(0);
}
x_153 = lean::cnstr_get(x_137, 0);
lean::inc(x_153);
x_154 = lean::cnstr_get_scalar<uint8>(x_137, sizeof(void*)*1);
if (lean::is_exclusive(x_137)) {
 lean::cnstr_release(x_137, 0);
 x_155 = x_137;
} else {
 lean::dec_ref(x_137);
 x_155 = lean::box(0);
}
if (lean::is_scalar(x_155)) {
 x_156 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_156 = x_155;
}
lean::cnstr_set(x_156, 0, x_153);
lean::cnstr_set_scalar(x_156, sizeof(void*)*1, x_154);
x_157 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_116, x_156);
if (lean::is_scalar(x_152)) {
 x_158 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_158 = x_152;
}
lean::cnstr_set(x_158, 0, x_157);
lean::cnstr_set(x_158, 1, x_151);
return x_158;
}
}
}
}
else
{
uint8 x_159; 
lean::dec(x_9);
lean::dec(x_2);
x_159 = !lean::is_exclusive(x_10);
if (x_159 == 0)
{
obj* x_160; uint8 x_161; 
x_160 = lean::cnstr_get(x_10, 0);
lean::dec(x_160);
x_161 = !lean::is_exclusive(x_11);
if (x_161 == 0)
{
return x_10;
}
else
{
obj* x_162; uint8 x_163; obj* x_164; 
x_162 = lean::cnstr_get(x_11, 0);
x_163 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
lean::inc(x_162);
lean::dec(x_11);
x_164 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_164, 0, x_162);
lean::cnstr_set_scalar(x_164, sizeof(void*)*1, x_163);
lean::cnstr_set(x_10, 0, x_164);
return x_10;
}
}
else
{
obj* x_165; obj* x_166; uint8 x_167; obj* x_168; obj* x_169; obj* x_170; 
x_165 = lean::cnstr_get(x_10, 1);
lean::inc(x_165);
lean::dec(x_10);
x_166 = lean::cnstr_get(x_11, 0);
lean::inc(x_166);
x_167 = lean::cnstr_get_scalar<uint8>(x_11, sizeof(void*)*1);
if (lean::is_exclusive(x_11)) {
 lean::cnstr_release(x_11, 0);
 x_168 = x_11;
} else {
 lean::dec_ref(x_11);
 x_168 = lean::box(0);
}
if (lean::is_scalar(x_168)) {
 x_169 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_169 = x_168;
}
lean::cnstr_set(x_169, 0, x_166);
lean::cnstr_set_scalar(x_169, sizeof(void*)*1, x_167);
x_170 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_170, 0, x_169);
lean::cnstr_set(x_170, 1, x_165);
return x_170;
}
}
}
else
{
uint32 x_171; obj* x_172; obj* x_173; 
x_171 = 34;
x_172 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6(x_171, x_3, x_4, x_5);
x_173 = lean::cnstr_get(x_172, 0);
lean::inc(x_173);
if (lean::obj_tag(x_173) == 0)
{
uint8 x_174; 
x_174 = !lean::is_exclusive(x_172);
if (x_174 == 0)
{
obj* x_175; uint8 x_176; 
x_175 = lean::cnstr_get(x_172, 0);
lean::dec(x_175);
x_176 = !lean::is_exclusive(x_173);
if (x_176 == 0)
{
obj* x_177; obj* x_178; obj* x_179; obj* x_180; 
x_177 = lean::cnstr_get(x_173, 2);
x_178 = lean::cnstr_get(x_173, 0);
lean::dec(x_178);
x_179 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_173, 2, x_179);
lean::cnstr_set(x_173, 0, x_2);
x_180 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_177, x_173);
lean::cnstr_set(x_172, 0, x_180);
return x_172;
}
else
{
obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; 
x_181 = lean::cnstr_get(x_173, 1);
x_182 = lean::cnstr_get(x_173, 2);
lean::inc(x_182);
lean::inc(x_181);
lean::dec(x_173);
x_183 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_184 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_184, 0, x_2);
lean::cnstr_set(x_184, 1, x_181);
lean::cnstr_set(x_184, 2, x_183);
x_185 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_182, x_184);
lean::cnstr_set(x_172, 0, x_185);
return x_172;
}
}
else
{
obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; obj* x_192; obj* x_193; 
x_186 = lean::cnstr_get(x_172, 1);
lean::inc(x_186);
lean::dec(x_172);
x_187 = lean::cnstr_get(x_173, 1);
lean::inc(x_187);
x_188 = lean::cnstr_get(x_173, 2);
lean::inc(x_188);
if (lean::is_exclusive(x_173)) {
 lean::cnstr_release(x_173, 0);
 lean::cnstr_release(x_173, 1);
 lean::cnstr_release(x_173, 2);
 x_189 = x_173;
} else {
 lean::dec_ref(x_173);
 x_189 = lean::box(0);
}
x_190 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_189)) {
 x_191 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_191 = x_189;
}
lean::cnstr_set(x_191, 0, x_2);
lean::cnstr_set(x_191, 1, x_187);
lean::cnstr_set(x_191, 2, x_190);
x_192 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_188, x_191);
x_193 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_193, 0, x_192);
lean::cnstr_set(x_193, 1, x_186);
return x_193;
}
}
else
{
uint8 x_194; 
lean::dec(x_2);
x_194 = !lean::is_exclusive(x_172);
if (x_194 == 0)
{
obj* x_195; uint8 x_196; 
x_195 = lean::cnstr_get(x_172, 0);
lean::dec(x_195);
x_196 = !lean::is_exclusive(x_173);
if (x_196 == 0)
{
return x_172;
}
else
{
obj* x_197; uint8 x_198; obj* x_199; 
x_197 = lean::cnstr_get(x_173, 0);
x_198 = lean::cnstr_get_scalar<uint8>(x_173, sizeof(void*)*1);
lean::inc(x_197);
lean::dec(x_173);
x_199 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_199, 0, x_197);
lean::cnstr_set_scalar(x_199, sizeof(void*)*1, x_198);
lean::cnstr_set(x_172, 0, x_199);
return x_172;
}
}
else
{
obj* x_200; obj* x_201; uint8 x_202; obj* x_203; obj* x_204; obj* x_205; 
x_200 = lean::cnstr_get(x_172, 1);
lean::inc(x_200);
lean::dec(x_172);
x_201 = lean::cnstr_get(x_173, 0);
lean::inc(x_201);
x_202 = lean::cnstr_get_scalar<uint8>(x_173, sizeof(void*)*1);
if (lean::is_exclusive(x_173)) {
 lean::cnstr_release(x_173, 0);
 x_203 = x_173;
} else {
 lean::dec_ref(x_173);
 x_203 = lean::box(0);
}
if (lean::is_scalar(x_203)) {
 x_204 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_204 = x_203;
}
lean::cnstr_set(x_204, 0, x_201);
lean::cnstr_set_scalar(x_204, sizeof(void*)*1, x_202);
x_205 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_205, 0, x_204);
lean::cnstr_set(x_205, 1, x_200);
return x_205;
}
}
}
}
}
obj* l_Lean_Parser_parseStringLiteral___at_Lean_Parser_stringLit_x27___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
uint32 x_4; obj* x_5; obj* x_6; 
x_4 = 34;
x_5 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6(x_4, x_1, x_2, x_3);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; uint8 x_13; 
x_7 = lean::cnstr_get(x_5, 1);
lean::inc(x_7);
lean::dec(x_5);
x_8 = lean::cnstr_get(x_6, 1);
lean::inc(x_8);
x_9 = lean::cnstr_get(x_6, 2);
lean::inc(x_9);
lean::dec(x_6);
x_10 = l_String_OldIterator_remaining___main(x_8);
x_11 = l_String_splitAux___main___closed__1;
x_12 = l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_x27___spec__2(x_10, x_11, x_1, x_8, x_7);
lean::dec(x_10);
x_13 = !lean::is_exclusive(x_12);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_14 = lean::cnstr_get(x_12, 0);
x_15 = l_Lean_Parser_finishCommentBlock___closed__2;
x_16 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_14);
x_17 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_16);
lean::cnstr_set(x_12, 0, x_17);
return x_12;
}
else
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_18 = lean::cnstr_get(x_12, 0);
x_19 = lean::cnstr_get(x_12, 1);
lean::inc(x_19);
lean::inc(x_18);
lean::dec(x_12);
x_20 = l_Lean_Parser_finishCommentBlock___closed__2;
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_20, x_18);
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_21);
x_23 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_19);
return x_23;
}
}
else
{
uint8 x_24; 
x_24 = !lean::is_exclusive(x_5);
if (x_24 == 0)
{
obj* x_25; uint8 x_26; 
x_25 = lean::cnstr_get(x_5, 0);
lean::dec(x_25);
x_26 = !lean::is_exclusive(x_6);
if (x_26 == 0)
{
return x_5;
}
else
{
obj* x_27; uint8 x_28; obj* x_29; 
x_27 = lean::cnstr_get(x_6, 0);
x_28 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
lean::inc(x_27);
lean::dec(x_6);
x_29 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_29, 0, x_27);
lean::cnstr_set_scalar(x_29, sizeof(void*)*1, x_28);
lean::cnstr_set(x_5, 0, x_29);
return x_5;
}
}
else
{
obj* x_30; obj* x_31; uint8 x_32; obj* x_33; obj* x_34; obj* x_35; 
x_30 = lean::cnstr_get(x_5, 1);
lean::inc(x_30);
lean::dec(x_5);
x_31 = lean::cnstr_get(x_6, 0);
lean::inc(x_31);
x_32 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_33 = x_6;
} else {
 lean::dec_ref(x_6);
 x_33 = lean::box(0);
}
if (lean::is_scalar(x_33)) {
 x_34 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_34 = x_33;
}
lean::cnstr_set(x_34, 0, x_31);
lean::cnstr_set_scalar(x_34, sizeof(void*)*1, x_32);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_30);
return x_35;
}
}
}
}
obj* l_Lean_Parser_stringLit_x27___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = l_Lean_Parser_parseStringLiteral___at_Lean_Parser_stringLit_x27___spec__1(x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_5);
if (x_7 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::cnstr_get(x_5, 0);
lean::dec(x_8);
x_9 = !lean::is_exclusive(x_6);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_10 = lean::cnstr_get(x_6, 1);
x_11 = lean::cnstr_get(x_6, 2);
x_12 = lean::cnstr_get(x_6, 0);
lean::dec(x_12);
lean::inc(x_10);
x_13 = l_Lean_Parser_mkRawRes(x_1, x_10);
x_14 = l_Lean_Parser_finishCommentBlock___closed__2;
lean::cnstr_set(x_6, 2, x_14);
lean::cnstr_set(x_6, 0, x_13);
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_6);
lean::cnstr_set(x_5, 0, x_15);
return x_5;
}
else
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
x_16 = lean::cnstr_get(x_6, 1);
x_17 = lean::cnstr_get(x_6, 2);
lean::inc(x_17);
lean::inc(x_16);
lean::dec(x_6);
lean::inc(x_16);
x_18 = l_Lean_Parser_mkRawRes(x_1, x_16);
x_19 = l_Lean_Parser_finishCommentBlock___closed__2;
x_20 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_20, 0, x_18);
lean::cnstr_set(x_20, 1, x_16);
lean::cnstr_set(x_20, 2, x_19);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_17, x_20);
lean::cnstr_set(x_5, 0, x_21);
return x_5;
}
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; 
x_22 = lean::cnstr_get(x_5, 1);
lean::inc(x_22);
lean::dec(x_5);
x_23 = lean::cnstr_get(x_6, 1);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_6, 2);
lean::inc(x_24);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_25 = x_6;
} else {
 lean::dec_ref(x_6);
 x_25 = lean::box(0);
}
lean::inc(x_23);
x_26 = l_Lean_Parser_mkRawRes(x_1, x_23);
x_27 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_25)) {
 x_28 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_28 = x_25;
}
lean::cnstr_set(x_28, 0, x_26);
lean::cnstr_set(x_28, 1, x_23);
lean::cnstr_set(x_28, 2, x_27);
x_29 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_28);
x_30 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_30, 0, x_29);
lean::cnstr_set(x_30, 1, x_22);
return x_30;
}
}
else
{
uint8 x_31; 
lean::dec(x_1);
x_31 = !lean::is_exclusive(x_5);
if (x_31 == 0)
{
obj* x_32; uint8 x_33; 
x_32 = lean::cnstr_get(x_5, 0);
lean::dec(x_32);
x_33 = !lean::is_exclusive(x_6);
if (x_33 == 0)
{
return x_5;
}
else
{
obj* x_34; uint8 x_35; obj* x_36; 
x_34 = lean::cnstr_get(x_6, 0);
x_35 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
lean::inc(x_34);
lean::dec(x_6);
x_36 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_36, 0, x_34);
lean::cnstr_set_scalar(x_36, sizeof(void*)*1, x_35);
lean::cnstr_set(x_5, 0, x_36);
return x_5;
}
}
else
{
obj* x_37; obj* x_38; uint8 x_39; obj* x_40; obj* x_41; obj* x_42; 
x_37 = lean::cnstr_get(x_5, 1);
lean::inc(x_37);
lean::dec(x_5);
x_38 = lean::cnstr_get(x_6, 0);
lean::inc(x_38);
x_39 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_40 = x_6;
} else {
 lean::dec_ref(x_6);
 x_40 = lean::box(0);
}
if (lean::is_scalar(x_40)) {
 x_41 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_41 = x_40;
}
lean::cnstr_set(x_41, 0, x_38);
lean::cnstr_set_scalar(x_41, sizeof(void*)*1, x_39);
x_42 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_42, 0, x_41);
lean::cnstr_set(x_42, 1, x_37);
return x_42;
}
}
}
}
obj* _init_l_Lean_Parser_stringLit_x27___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___rarg___lambda__1), 2, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_lift___at_Lean_Parser_withTrailing___spec__1___rarg___boxed), 4, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_stringLit_x27___lambda__1___boxed), 4, 0);
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_4, 0, x_2);
lean::closure_set(x_4, 1, x_3);
x_5 = lean::box(0);
x_6 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* l_Lean_Parser_stringLit_x27(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_stringLit;
x_5 = l_Lean_Parser_stringLit_x27___closed__1;
x_6 = l_Lean_Parser_Combinators_node___at_Lean_Parser_detailIdentPart_Parser_Lean_Parser_HasTokens___spec__4(x_4, x_5, x_1, x_2, x_3);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x27___spec__4___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_x27___spec__4___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_digit___at_Lean_Parser_stringLit_x27___spec__6___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_MonadParsec_digit___at_Lean_Parser_stringLit_x27___spec__6(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_parseQuotedChar___at_Lean_Parser_stringLit_x27___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_parseQuotedChar___at_Lean_Parser_stringLit_x27___spec__3(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_x27___spec__2___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_x27___spec__2(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_Parser_parseStringLiteral___at_Lean_Parser_stringLit_x27___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_parseStringLiteral___at_Lean_Parser_stringLit_x27___spec__1(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_stringLit_x27___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_stringLit_x27___lambda__1(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l___private_init_lean_parser_token_5__mkConsumeToken(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = lean::string_length(x_6);
lean::inc(x_2);
x_8 = l_String_OldIterator_nextn___main(x_2, x_7);
lean::inc(x_8);
x_9 = l_Lean_Parser_mkRawRes(x_2, x_8);
x_10 = lean::box(0);
x_11 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_11, 0, x_9);
lean::cnstr_set(x_11, 1, x_8);
lean::cnstr_set(x_11, 2, x_10);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_11);
lean::cnstr_set(x_12, 1, x_5);
return x_12;
}
}
obj* l___private_init_lean_parser_token_5__mkConsumeToken___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l___private_init_lean_parser_token_5__mkConsumeToken(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_Parser_numberOrStringLit(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
lean::inc(x_2);
lean::inc(x_1);
x_4 = l_Lean_Parser_number_x27(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
lean::dec(x_2);
lean::dec(x_1);
x_6 = !lean::is_exclusive(x_4);
if (x_6 == 0)
{
obj* x_7; 
x_7 = lean::cnstr_get(x_4, 0);
lean::dec(x_7);
return x_4;
}
else
{
obj* x_8; obj* x_9; 
x_8 = lean::cnstr_get(x_4, 1);
lean::inc(x_8);
lean::dec(x_4);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_5);
lean::cnstr_set(x_9, 1, x_8);
return x_9;
}
}
else
{
uint8 x_10; 
x_10 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_11 = lean::cnstr_get(x_4, 1);
lean::inc(x_11);
lean::dec(x_4);
x_12 = lean::cnstr_get(x_5, 0);
lean::inc(x_12);
lean::dec(x_5);
x_13 = l_Lean_Parser_stringLit_x27(x_1, x_2, x_11);
x_14 = !lean::is_exclusive(x_13);
if (x_14 == 0)
{
obj* x_15; obj* x_16; 
x_15 = lean::cnstr_get(x_13, 0);
x_16 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_12, x_15);
lean::cnstr_set(x_13, 0, x_16);
return x_13;
}
else
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_17 = lean::cnstr_get(x_13, 0);
x_18 = lean::cnstr_get(x_13, 1);
lean::inc(x_18);
lean::inc(x_17);
lean::dec(x_13);
x_19 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_12, x_17);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_18);
return x_20;
}
}
else
{
uint8 x_21; 
lean::dec(x_2);
lean::dec(x_1);
x_21 = !lean::is_exclusive(x_4);
if (x_21 == 0)
{
obj* x_22; 
x_22 = lean::cnstr_get(x_4, 0);
lean::dec(x_22);
return x_4;
}
else
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_4, 1);
lean::inc(x_23);
lean::dec(x_4);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_5);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
}
}
}
obj* l_Lean_Parser_tokenCont(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; 
lean::inc(x_3);
x_6 = l___private_init_lean_parser_token_4__ident_x27(x_3, x_4, x_5);
x_7 = lean::cnstr_get(x_6, 0);
lean::inc(x_7);
if (lean::obj_tag(x_7) == 0)
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_6);
if (x_8 == 0)
{
obj* x_9; obj* x_10; uint8 x_11; 
x_9 = lean::cnstr_get(x_6, 1);
x_10 = lean::cnstr_get(x_6, 0);
lean::dec(x_10);
x_11 = !lean::is_exclusive(x_7);
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; 
x_12 = lean::cnstr_get(x_7, 0);
x_13 = lean::cnstr_get(x_7, 1);
x_14 = lean::cnstr_get(x_7, 2);
x_15 = lean::cnstr_get(x_13, 1);
lean::inc(x_15);
x_16 = lean::cnstr_get(x_1, 1);
lean::inc(x_16);
x_17 = lean::cnstr_get(x_2, 0);
x_18 = lean::string_length(x_17);
x_19 = lean::nat_add(x_16, x_18);
lean::dec(x_18);
lean::dec(x_16);
x_20 = lean::nat_dec_le(x_15, x_19);
lean::dec(x_19);
lean::dec(x_15);
if (x_20 == 0)
{
obj* x_21; obj* x_22; 
lean::dec(x_3);
lean::dec(x_1);
x_21 = l_Lean_Parser_finishCommentBlock___closed__2;
lean::cnstr_set(x_7, 2, x_21);
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_7);
lean::cnstr_set(x_6, 0, x_22);
return x_6;
}
else
{
obj* x_23; uint8 x_24; 
lean::free_heap_obj(x_7);
lean::dec(x_12);
lean::free_heap_obj(x_6);
x_23 = l___private_init_lean_parser_token_5__mkConsumeToken(x_2, x_1, x_3, x_13, x_9);
lean::dec(x_13);
lean::dec(x_3);
x_24 = !lean::is_exclusive(x_23);
if (x_24 == 0)
{
obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_25 = lean::cnstr_get(x_23, 0);
x_26 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_27 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_26, x_25);
x_28 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_27);
lean::cnstr_set(x_23, 0, x_28);
return x_23;
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; 
x_29 = lean::cnstr_get(x_23, 0);
x_30 = lean::cnstr_get(x_23, 1);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_23);
x_31 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_31, x_29);
x_33 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_32);
x_34 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_30);
return x_34;
}
}
}
else
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; uint8 x_43; 
x_35 = lean::cnstr_get(x_7, 0);
x_36 = lean::cnstr_get(x_7, 1);
x_37 = lean::cnstr_get(x_7, 2);
lean::inc(x_37);
lean::inc(x_36);
lean::inc(x_35);
lean::dec(x_7);
x_38 = lean::cnstr_get(x_36, 1);
lean::inc(x_38);
x_39 = lean::cnstr_get(x_1, 1);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_2, 0);
x_41 = lean::string_length(x_40);
x_42 = lean::nat_add(x_39, x_41);
lean::dec(x_41);
lean::dec(x_39);
x_43 = lean::nat_dec_le(x_38, x_42);
lean::dec(x_42);
lean::dec(x_38);
if (x_43 == 0)
{
obj* x_44; obj* x_45; obj* x_46; 
lean::dec(x_3);
lean::dec(x_1);
x_44 = l_Lean_Parser_finishCommentBlock___closed__2;
x_45 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_45, 0, x_35);
lean::cnstr_set(x_45, 1, x_36);
lean::cnstr_set(x_45, 2, x_44);
x_46 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_37, x_45);
lean::cnstr_set(x_6, 0, x_46);
return x_6;
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_35);
lean::free_heap_obj(x_6);
x_47 = l___private_init_lean_parser_token_5__mkConsumeToken(x_2, x_1, x_3, x_36, x_9);
lean::dec(x_36);
lean::dec(x_3);
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
x_49 = lean::cnstr_get(x_47, 1);
lean::inc(x_49);
if (lean::is_exclusive(x_47)) {
 lean::cnstr_release(x_47, 0);
 lean::cnstr_release(x_47, 1);
 x_50 = x_47;
} else {
 lean::dec_ref(x_47);
 x_50 = lean::box(0);
}
x_51 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_52 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_51, x_48);
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_37, x_52);
if (lean::is_scalar(x_50)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_50;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_49);
return x_54;
}
}
}
else
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; uint8 x_65; 
x_55 = lean::cnstr_get(x_6, 1);
lean::inc(x_55);
lean::dec(x_6);
x_56 = lean::cnstr_get(x_7, 0);
lean::inc(x_56);
x_57 = lean::cnstr_get(x_7, 1);
lean::inc(x_57);
x_58 = lean::cnstr_get(x_7, 2);
lean::inc(x_58);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 lean::cnstr_release(x_7, 1);
 lean::cnstr_release(x_7, 2);
 x_59 = x_7;
} else {
 lean::dec_ref(x_7);
 x_59 = lean::box(0);
}
x_60 = lean::cnstr_get(x_57, 1);
lean::inc(x_60);
x_61 = lean::cnstr_get(x_1, 1);
lean::inc(x_61);
x_62 = lean::cnstr_get(x_2, 0);
x_63 = lean::string_length(x_62);
x_64 = lean::nat_add(x_61, x_63);
lean::dec(x_63);
lean::dec(x_61);
x_65 = lean::nat_dec_le(x_60, x_64);
lean::dec(x_64);
lean::dec(x_60);
if (x_65 == 0)
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_3);
lean::dec(x_1);
x_66 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_59)) {
 x_67 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_67 = x_59;
}
lean::cnstr_set(x_67, 0, x_56);
lean::cnstr_set(x_67, 1, x_57);
lean::cnstr_set(x_67, 2, x_66);
x_68 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_67);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_55);
return x_69;
}
else
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; 
lean::dec(x_59);
lean::dec(x_56);
x_70 = l___private_init_lean_parser_token_5__mkConsumeToken(x_2, x_1, x_3, x_57, x_55);
lean::dec(x_57);
lean::dec(x_3);
x_71 = lean::cnstr_get(x_70, 0);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_70, 1);
lean::inc(x_72);
if (lean::is_exclusive(x_70)) {
 lean::cnstr_release(x_70, 0);
 lean::cnstr_release(x_70, 1);
 x_73 = x_70;
} else {
 lean::dec_ref(x_70);
 x_73 = lean::box(0);
}
x_74 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_75 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_74, x_71);
x_76 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_75);
if (lean::is_scalar(x_73)) {
 x_77 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_77 = x_73;
}
lean::cnstr_set(x_77, 0, x_76);
lean::cnstr_set(x_77, 1, x_72);
return x_77;
}
}
}
else
{
uint8 x_78; 
lean::dec(x_3);
lean::dec(x_1);
x_78 = !lean::is_exclusive(x_6);
if (x_78 == 0)
{
obj* x_79; uint8 x_80; 
x_79 = lean::cnstr_get(x_6, 0);
lean::dec(x_79);
x_80 = !lean::is_exclusive(x_7);
if (x_80 == 0)
{
return x_6;
}
else
{
obj* x_81; uint8 x_82; obj* x_83; 
x_81 = lean::cnstr_get(x_7, 0);
x_82 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
lean::inc(x_81);
lean::dec(x_7);
x_83 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_83, 0, x_81);
lean::cnstr_set_scalar(x_83, sizeof(void*)*1, x_82);
lean::cnstr_set(x_6, 0, x_83);
return x_6;
}
}
else
{
obj* x_84; obj* x_85; uint8 x_86; obj* x_87; obj* x_88; obj* x_89; 
x_84 = lean::cnstr_get(x_6, 1);
lean::inc(x_84);
lean::dec(x_6);
x_85 = lean::cnstr_get(x_7, 0);
lean::inc(x_85);
x_86 = lean::cnstr_get_scalar<uint8>(x_7, sizeof(void*)*1);
if (lean::is_exclusive(x_7)) {
 lean::cnstr_release(x_7, 0);
 x_87 = x_7;
} else {
 lean::dec_ref(x_7);
 x_87 = lean::box(0);
}
if (lean::is_scalar(x_87)) {
 x_88 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_88 = x_87;
}
lean::cnstr_set(x_88, 0, x_85);
lean::cnstr_set_scalar(x_88, sizeof(void*)*1, x_86);
x_89 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_84);
return x_89;
}
}
}
}
obj* l_Lean_Parser_tokenCont___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_tokenCont(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_2);
return x_6;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_token___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; obj* x_7; uint8 x_19; 
x_19 = l_String_OldIterator_hasNext___main(x_4);
if (x_19 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_20 = lean::box(0);
x_21 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
lean::inc(x_4);
x_22 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_21, x_1, x_20, x_20, x_3, x_4, x_5);
x_23 = lean::cnstr_get(x_22, 0);
lean::inc(x_23);
x_24 = lean::cnstr_get(x_22, 1);
lean::inc(x_24);
lean::dec(x_22);
x_25 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_2, x_23);
if (lean::obj_tag(x_25) == 0)
{
x_6 = x_25;
x_7 = x_24;
goto block_18;
}
else
{
uint8 x_26; 
x_26 = lean::cnstr_get_scalar<uint8>(x_25, sizeof(void*)*1);
if (x_26 == 0)
{
obj* x_27; uint32 x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_27 = lean::cnstr_get(x_25, 0);
lean::inc(x_27);
lean::dec(x_25);
x_28 = l_Lean_idBeginEscape;
lean::inc(x_4);
x_29 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6(x_28, x_3, x_4, x_24);
x_30 = lean::cnstr_get(x_29, 0);
lean::inc(x_30);
x_31 = lean::cnstr_get(x_29, 1);
lean::inc(x_31);
lean::dec(x_29);
x_32 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_27, x_30);
x_6 = x_32;
x_7 = x_31;
goto block_18;
}
else
{
x_6 = x_25;
x_7 = x_24;
goto block_18;
}
}
}
else
{
uint32 x_33; uint8 x_34; 
x_33 = l_String_OldIterator_curr___main(x_4);
x_34 = l_Lean_isIdFirst(x_33);
if (x_34 == 0)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
x_35 = l_Char_quoteCore(x_33);
x_36 = l_Char_HasRepr___closed__1;
x_37 = lean::string_append(x_36, x_35);
lean::dec(x_35);
x_38 = lean::string_append(x_37, x_36);
x_39 = lean::box(0);
lean::inc(x_4);
x_40 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_38, x_1, x_39, x_39, x_3, x_4, x_5);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_42 = lean::cnstr_get(x_40, 1);
lean::inc(x_42);
lean::dec(x_40);
x_43 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_2, x_41);
if (lean::obj_tag(x_43) == 0)
{
x_6 = x_43;
x_7 = x_42;
goto block_18;
}
else
{
uint8 x_44; 
x_44 = lean::cnstr_get_scalar<uint8>(x_43, sizeof(void*)*1);
if (x_44 == 0)
{
obj* x_45; uint32 x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_45 = lean::cnstr_get(x_43, 0);
lean::inc(x_45);
lean::dec(x_43);
x_46 = l_Lean_idBeginEscape;
lean::inc(x_4);
x_47 = l_Lean_Parser_MonadParsec_ch___at___private_init_lean_parser_token_4__ident_x27___spec__6(x_46, x_3, x_4, x_42);
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
x_49 = lean::cnstr_get(x_47, 1);
lean::inc(x_49);
lean::dec(x_47);
x_50 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_45, x_48);
x_6 = x_50;
x_7 = x_49;
goto block_18;
}
else
{
x_6 = x_43;
x_7 = x_42;
goto block_18;
}
}
}
else
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_2);
lean::dec(x_1);
lean::inc(x_4);
x_51 = l_String_OldIterator_next___main(x_4);
x_52 = lean::box(0);
x_53 = lean::box_uint32(x_33);
x_54 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_51);
lean::cnstr_set(x_54, 2, x_52);
x_6 = x_54;
x_7 = x_5;
goto block_18;
}
}
block_18:
{
if (lean::obj_tag(x_6) == 0)
{
uint8 x_8; 
x_8 = !lean::is_exclusive(x_6);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_6, 2);
lean::dec(x_9);
x_10 = lean::cnstr_get(x_6, 1);
lean::dec(x_10);
x_11 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_6, 2, x_11);
lean::cnstr_set(x_6, 1, x_4);
x_12 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_12, 0, x_6);
lean::cnstr_set(x_12, 1, x_7);
return x_12;
}
else
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_6, 0);
lean::inc(x_13);
lean::dec(x_6);
x_14 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_15 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set(x_15, 1, x_4);
lean::cnstr_set(x_15, 2, x_14);
x_16 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_16, 0, x_15);
lean::cnstr_set(x_16, 1, x_7);
return x_16;
}
}
else
{
obj* x_17; 
lean::dec(x_4);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_6);
lean::cnstr_set(x_17, 1, x_7);
return x_17;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_observing___at_Lean_Parser_token___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::apply_3(x_1, x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_5);
if (x_7 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::cnstr_get(x_5, 0);
lean::dec(x_8);
x_9 = !lean::is_exclusive(x_6);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_6, 0);
x_11 = lean::cnstr_get(x_6, 2);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_10);
x_13 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_6, 2, x_13);
lean::cnstr_set(x_6, 0, x_12);
x_14 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_6);
if (lean::obj_tag(x_14) == 0)
{
lean::cnstr_set(x_5, 0, x_14);
return x_5;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
lean::dec(x_14);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_17 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_17, 0, x_15);
x_18 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
lean::cnstr_set(x_18, 2, x_13);
lean::cnstr_set(x_5, 0, x_18);
return x_5;
}
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_19 = lean::cnstr_get(x_6, 0);
x_20 = lean::cnstr_get(x_6, 1);
x_21 = lean::cnstr_get(x_6, 2);
lean::inc(x_21);
lean::inc(x_20);
lean::inc(x_19);
lean::dec(x_6);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_19);
x_23 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_20);
lean::cnstr_set(x_24, 2, x_23);
x_25 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_24);
if (lean::obj_tag(x_25) == 0)
{
lean::cnstr_set(x_5, 0, x_25);
return x_5;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
lean::dec(x_25);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_28 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_28, 0, x_26);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_27);
lean::cnstr_set(x_29, 2, x_23);
lean::cnstr_set(x_5, 0, x_29);
return x_5;
}
}
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_30 = lean::cnstr_get(x_5, 1);
lean::inc(x_30);
lean::dec(x_5);
x_31 = lean::cnstr_get(x_6, 0);
lean::inc(x_31);
x_32 = lean::cnstr_get(x_6, 1);
lean::inc(x_32);
x_33 = lean::cnstr_get(x_6, 2);
lean::inc(x_33);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_34 = x_6;
} else {
 lean::dec_ref(x_6);
 x_34 = lean::box(0);
}
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_31);
x_36 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_34)) {
 x_37 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_37 = x_34;
}
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set(x_37, 1, x_32);
lean::cnstr_set(x_37, 2, x_36);
x_38 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_33, x_37);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; 
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_30);
return x_39;
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_40 = lean::cnstr_get(x_38, 0);
lean::inc(x_40);
lean::dec(x_38);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_42 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_42, 0, x_40);
x_43 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_41);
lean::cnstr_set(x_43, 2, x_36);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_30);
return x_44;
}
}
}
else
{
uint8 x_45; 
x_45 = !lean::is_exclusive(x_5);
if (x_45 == 0)
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_46 = lean::cnstr_get(x_5, 0);
lean::dec(x_46);
x_47 = lean::cnstr_get(x_6, 0);
lean::inc(x_47);
lean::dec(x_6);
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
x_49 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_49, 0, x_47);
x_50 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_51 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set(x_51, 1, x_48);
lean::cnstr_set(x_51, 2, x_50);
lean::cnstr_set(x_5, 0, x_51);
return x_5;
}
else
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_52 = lean::cnstr_get(x_5, 1);
lean::inc(x_52);
lean::dec(x_5);
x_53 = lean::cnstr_get(x_6, 0);
lean::inc(x_53);
lean::dec(x_6);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
x_55 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_55, 0, x_53);
x_56 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_57 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set(x_57, 1, x_54);
lean::cnstr_set(x_57, 2, x_56);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_52);
return x_58;
}
}
}
}
obj* l_Lean_Parser_withTrailing___at_Lean_Parser_token___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_3);
x_5 = l_Lean_Parser_whitespace(x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_5);
if (x_7 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::cnstr_get(x_5, 0);
lean::dec(x_8);
x_9 = !lean::is_exclusive(x_6);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_10 = lean::cnstr_get(x_6, 1);
x_11 = lean::cnstr_get(x_6, 2);
x_12 = lean::cnstr_get(x_6, 0);
lean::dec(x_12);
lean::inc(x_10);
x_13 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_13, 0, x_3);
lean::cnstr_set(x_13, 1, x_10);
x_14 = l_Lean_Parser_finishCommentBlock___closed__2;
lean::cnstr_set(x_6, 2, x_14);
lean::cnstr_set(x_6, 0, x_13);
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_6);
x_16 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_17 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_15);
if (lean::obj_tag(x_17) == 0)
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_17);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_19 = lean::cnstr_get(x_17, 0);
x_20 = lean::cnstr_get(x_17, 2);
x_21 = l___private_init_lean_parser_token_3__updateTrailing___main(x_19, x_1);
lean::cnstr_set(x_17, 2, x_16);
lean::cnstr_set(x_17, 0, x_21);
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_20, x_17);
lean::cnstr_set(x_5, 0, x_22);
return x_5;
}
else
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_23 = lean::cnstr_get(x_17, 0);
x_24 = lean::cnstr_get(x_17, 1);
x_25 = lean::cnstr_get(x_17, 2);
lean::inc(x_25);
lean::inc(x_24);
lean::inc(x_23);
lean::dec(x_17);
x_26 = l___private_init_lean_parser_token_3__updateTrailing___main(x_23, x_1);
x_27 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_27, 0, x_26);
lean::cnstr_set(x_27, 1, x_24);
lean::cnstr_set(x_27, 2, x_16);
x_28 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_25, x_27);
lean::cnstr_set(x_5, 0, x_28);
return x_5;
}
}
else
{
uint8 x_29; 
lean::dec(x_1);
x_29 = !lean::is_exclusive(x_17);
if (x_29 == 0)
{
lean::cnstr_set(x_5, 0, x_17);
return x_5;
}
else
{
obj* x_30; uint8 x_31; obj* x_32; 
x_30 = lean::cnstr_get(x_17, 0);
x_31 = lean::cnstr_get_scalar<uint8>(x_17, sizeof(void*)*1);
lean::inc(x_30);
lean::dec(x_17);
x_32 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_32, 0, x_30);
lean::cnstr_set_scalar(x_32, sizeof(void*)*1, x_31);
lean::cnstr_set(x_5, 0, x_32);
return x_5;
}
}
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; obj* x_40; 
x_33 = lean::cnstr_get(x_6, 1);
x_34 = lean::cnstr_get(x_6, 2);
lean::inc(x_34);
lean::inc(x_33);
lean::dec(x_6);
lean::inc(x_33);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_3);
lean::cnstr_set(x_35, 1, x_33);
x_36 = l_Lean_Parser_finishCommentBlock___closed__2;
x_37 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set(x_37, 1, x_33);
lean::cnstr_set(x_37, 2, x_36);
x_38 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_34, x_37);
x_39 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_40 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_39, x_38);
if (lean::obj_tag(x_40) == 0)
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_42 = lean::cnstr_get(x_40, 1);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_40, 2);
lean::inc(x_43);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_release(x_40, 0);
 lean::cnstr_release(x_40, 1);
 lean::cnstr_release(x_40, 2);
 x_44 = x_40;
} else {
 lean::dec_ref(x_40);
 x_44 = lean::box(0);
}
x_45 = l___private_init_lean_parser_token_3__updateTrailing___main(x_41, x_1);
if (lean::is_scalar(x_44)) {
 x_46 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_46 = x_44;
}
lean::cnstr_set(x_46, 0, x_45);
lean::cnstr_set(x_46, 1, x_42);
lean::cnstr_set(x_46, 2, x_39);
x_47 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_43, x_46);
lean::cnstr_set(x_5, 0, x_47);
return x_5;
}
else
{
obj* x_48; uint8 x_49; obj* x_50; obj* x_51; 
lean::dec(x_1);
x_48 = lean::cnstr_get(x_40, 0);
lean::inc(x_48);
x_49 = lean::cnstr_get_scalar<uint8>(x_40, sizeof(void*)*1);
if (lean::is_exclusive(x_40)) {
 lean::cnstr_release(x_40, 0);
 x_50 = x_40;
} else {
 lean::dec_ref(x_40);
 x_50 = lean::box(0);
}
if (lean::is_scalar(x_50)) {
 x_51 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_51 = x_50;
}
lean::cnstr_set(x_51, 0, x_48);
lean::cnstr_set_scalar(x_51, sizeof(void*)*1, x_49);
lean::cnstr_set(x_5, 0, x_51);
return x_5;
}
}
}
else
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
x_52 = lean::cnstr_get(x_5, 1);
lean::inc(x_52);
lean::dec(x_5);
x_53 = lean::cnstr_get(x_6, 1);
lean::inc(x_53);
x_54 = lean::cnstr_get(x_6, 2);
lean::inc(x_54);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_55 = x_6;
} else {
 lean::dec_ref(x_6);
 x_55 = lean::box(0);
}
lean::inc(x_53);
x_56 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_56, 0, x_3);
lean::cnstr_set(x_56, 1, x_53);
x_57 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_55)) {
 x_58 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_58 = x_55;
}
lean::cnstr_set(x_58, 0, x_56);
lean::cnstr_set(x_58, 1, x_53);
lean::cnstr_set(x_58, 2, x_57);
x_59 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_54, x_58);
x_60 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_61 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_60, x_59);
if (lean::obj_tag(x_61) == 0)
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; 
x_62 = lean::cnstr_get(x_61, 0);
lean::inc(x_62);
x_63 = lean::cnstr_get(x_61, 1);
lean::inc(x_63);
x_64 = lean::cnstr_get(x_61, 2);
lean::inc(x_64);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 lean::cnstr_release(x_61, 1);
 lean::cnstr_release(x_61, 2);
 x_65 = x_61;
} else {
 lean::dec_ref(x_61);
 x_65 = lean::box(0);
}
x_66 = l___private_init_lean_parser_token_3__updateTrailing___main(x_62, x_1);
if (lean::is_scalar(x_65)) {
 x_67 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_67 = x_65;
}
lean::cnstr_set(x_67, 0, x_66);
lean::cnstr_set(x_67, 1, x_63);
lean::cnstr_set(x_67, 2, x_60);
x_68 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_64, x_67);
x_69 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_69, 0, x_68);
lean::cnstr_set(x_69, 1, x_52);
return x_69;
}
else
{
obj* x_70; uint8 x_71; obj* x_72; obj* x_73; obj* x_74; 
lean::dec(x_1);
x_70 = lean::cnstr_get(x_61, 0);
lean::inc(x_70);
x_71 = lean::cnstr_get_scalar<uint8>(x_61, sizeof(void*)*1);
if (lean::is_exclusive(x_61)) {
 lean::cnstr_release(x_61, 0);
 x_72 = x_61;
} else {
 lean::dec_ref(x_61);
 x_72 = lean::box(0);
}
if (lean::is_scalar(x_72)) {
 x_73 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_73 = x_72;
}
lean::cnstr_set(x_73, 0, x_70);
lean::cnstr_set_scalar(x_73, sizeof(void*)*1, x_71);
x_74 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_74, 0, x_73);
lean::cnstr_set(x_74, 1, x_52);
return x_74;
}
}
}
else
{
uint8 x_75; 
lean::dec(x_3);
x_75 = !lean::is_exclusive(x_5);
if (x_75 == 0)
{
obj* x_76; uint8 x_77; 
x_76 = lean::cnstr_get(x_5, 0);
lean::dec(x_76);
x_77 = !lean::is_exclusive(x_6);
if (x_77 == 0)
{
obj* x_78; obj* x_79; 
x_78 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_79 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_78, x_6);
if (lean::obj_tag(x_79) == 0)
{
uint8 x_80; 
x_80 = !lean::is_exclusive(x_79);
if (x_80 == 0)
{
obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_81 = lean::cnstr_get(x_79, 0);
x_82 = lean::cnstr_get(x_79, 2);
x_83 = l___private_init_lean_parser_token_3__updateTrailing___main(x_81, x_1);
lean::cnstr_set(x_79, 2, x_78);
lean::cnstr_set(x_79, 0, x_83);
x_84 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_82, x_79);
lean::cnstr_set(x_5, 0, x_84);
return x_5;
}
else
{
obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; 
x_85 = lean::cnstr_get(x_79, 0);
x_86 = lean::cnstr_get(x_79, 1);
x_87 = lean::cnstr_get(x_79, 2);
lean::inc(x_87);
lean::inc(x_86);
lean::inc(x_85);
lean::dec(x_79);
x_88 = l___private_init_lean_parser_token_3__updateTrailing___main(x_85, x_1);
x_89 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_86);
lean::cnstr_set(x_89, 2, x_78);
x_90 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_87, x_89);
lean::cnstr_set(x_5, 0, x_90);
return x_5;
}
}
else
{
uint8 x_91; 
lean::dec(x_1);
x_91 = !lean::is_exclusive(x_79);
if (x_91 == 0)
{
lean::cnstr_set(x_5, 0, x_79);
return x_5;
}
else
{
obj* x_92; uint8 x_93; obj* x_94; 
x_92 = lean::cnstr_get(x_79, 0);
x_93 = lean::cnstr_get_scalar<uint8>(x_79, sizeof(void*)*1);
lean::inc(x_92);
lean::dec(x_79);
x_94 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_94, 0, x_92);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_93);
lean::cnstr_set(x_5, 0, x_94);
return x_5;
}
}
}
else
{
obj* x_95; uint8 x_96; obj* x_97; obj* x_98; obj* x_99; 
x_95 = lean::cnstr_get(x_6, 0);
x_96 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
lean::inc(x_95);
lean::dec(x_6);
x_97 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_97, 0, x_95);
lean::cnstr_set_scalar(x_97, sizeof(void*)*1, x_96);
x_98 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_99 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_98, x_97);
if (lean::obj_tag(x_99) == 0)
{
obj* x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_100 = lean::cnstr_get(x_99, 0);
lean::inc(x_100);
x_101 = lean::cnstr_get(x_99, 1);
lean::inc(x_101);
x_102 = lean::cnstr_get(x_99, 2);
lean::inc(x_102);
if (lean::is_exclusive(x_99)) {
 lean::cnstr_release(x_99, 0);
 lean::cnstr_release(x_99, 1);
 lean::cnstr_release(x_99, 2);
 x_103 = x_99;
} else {
 lean::dec_ref(x_99);
 x_103 = lean::box(0);
}
x_104 = l___private_init_lean_parser_token_3__updateTrailing___main(x_100, x_1);
if (lean::is_scalar(x_103)) {
 x_105 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_105 = x_103;
}
lean::cnstr_set(x_105, 0, x_104);
lean::cnstr_set(x_105, 1, x_101);
lean::cnstr_set(x_105, 2, x_98);
x_106 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_102, x_105);
lean::cnstr_set(x_5, 0, x_106);
return x_5;
}
else
{
obj* x_107; uint8 x_108; obj* x_109; obj* x_110; 
lean::dec(x_1);
x_107 = lean::cnstr_get(x_99, 0);
lean::inc(x_107);
x_108 = lean::cnstr_get_scalar<uint8>(x_99, sizeof(void*)*1);
if (lean::is_exclusive(x_99)) {
 lean::cnstr_release(x_99, 0);
 x_109 = x_99;
} else {
 lean::dec_ref(x_99);
 x_109 = lean::box(0);
}
if (lean::is_scalar(x_109)) {
 x_110 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_110 = x_109;
}
lean::cnstr_set(x_110, 0, x_107);
lean::cnstr_set_scalar(x_110, sizeof(void*)*1, x_108);
lean::cnstr_set(x_5, 0, x_110);
return x_5;
}
}
}
else
{
obj* x_111; obj* x_112; uint8 x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
x_111 = lean::cnstr_get(x_5, 1);
lean::inc(x_111);
lean::dec(x_5);
x_112 = lean::cnstr_get(x_6, 0);
lean::inc(x_112);
x_113 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_114 = x_6;
} else {
 lean::dec_ref(x_6);
 x_114 = lean::box(0);
}
if (lean::is_scalar(x_114)) {
 x_115 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_115 = x_114;
}
lean::cnstr_set(x_115, 0, x_112);
lean::cnstr_set_scalar(x_115, sizeof(void*)*1, x_113);
x_116 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_117 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_116, x_115);
if (lean::obj_tag(x_117) == 0)
{
obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; 
x_118 = lean::cnstr_get(x_117, 0);
lean::inc(x_118);
x_119 = lean::cnstr_get(x_117, 1);
lean::inc(x_119);
x_120 = lean::cnstr_get(x_117, 2);
lean::inc(x_120);
if (lean::is_exclusive(x_117)) {
 lean::cnstr_release(x_117, 0);
 lean::cnstr_release(x_117, 1);
 lean::cnstr_release(x_117, 2);
 x_121 = x_117;
} else {
 lean::dec_ref(x_117);
 x_121 = lean::box(0);
}
x_122 = l___private_init_lean_parser_token_3__updateTrailing___main(x_118, x_1);
if (lean::is_scalar(x_121)) {
 x_123 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_123 = x_121;
}
lean::cnstr_set(x_123, 0, x_122);
lean::cnstr_set(x_123, 1, x_119);
lean::cnstr_set(x_123, 2, x_116);
x_124 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_120, x_123);
x_125 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_125, 0, x_124);
lean::cnstr_set(x_125, 1, x_111);
return x_125;
}
else
{
obj* x_126; uint8 x_127; obj* x_128; obj* x_129; obj* x_130; 
lean::dec(x_1);
x_126 = lean::cnstr_get(x_117, 0);
lean::inc(x_126);
x_127 = lean::cnstr_get_scalar<uint8>(x_117, sizeof(void*)*1);
if (lean::is_exclusive(x_117)) {
 lean::cnstr_release(x_117, 0);
 x_128 = x_117;
} else {
 lean::dec_ref(x_117);
 x_128 = lean::box(0);
}
if (lean::is_scalar(x_128)) {
 x_129 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_129 = x_128;
}
lean::cnstr_set(x_129, 0, x_126);
lean::cnstr_set_scalar(x_129, sizeof(void*)*1, x_127);
x_130 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_130, 0, x_129);
lean::cnstr_set(x_130, 1, x_111);
return x_130;
}
}
}
}
}
obj* l_Lean_Parser_ParsecT_failure___at_Lean_Parser_token___spec__4___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; uint8 x_7; obj* x_8; obj* x_9; 
x_3 = lean::box(0);
x_4 = l_Lean_Parser_ParsecT_failure___rarg___closed__1;
x_5 = l_mjoin___rarg___closed__1;
x_6 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_6, 0, x_1);
lean::cnstr_set(x_6, 1, x_4);
lean::cnstr_set(x_6, 2, x_5);
lean::cnstr_set(x_6, 3, x_3);
x_7 = 0;
x_8 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set_scalar(x_8, sizeof(void*)*1, x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_2);
return x_9;
}
}
obj* l_Lean_Parser_ParsecT_failure___at_Lean_Parser_token___spec__4(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_failure___at_Lean_Parser_token___spec__4___rarg), 2, 0);
return x_3;
}
}
obj* _init_l_Lean_Parser_token___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_id___rarg___boxed), 1, 0);
lean::inc(x_1);
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_token___spec__1___boxed), 5, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* _init_l_Lean_Parser_token___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::mk_string("token: not implemented");
return x_1;
}
}
obj* l_Lean_Parser_token(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_155; 
x_155 = lean::cnstr_get(x_3, 0);
lean::inc(x_155);
if (lean::obj_tag(x_155) == 0)
{
obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
lean::dec(x_155);
lean::inc(x_3);
lean::inc(x_2);
x_156 = l_Lean_Parser_ParsecT_failure___at_Lean_Parser_token___spec__4___rarg(x_2, x_3);
x_157 = lean::cnstr_get(x_156, 0);
lean::inc(x_157);
x_158 = lean::cnstr_get(x_156, 1);
lean::inc(x_158);
lean::dec(x_156);
x_159 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_160 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_159, x_157);
x_4 = x_160;
x_5 = x_158;
goto block_154;
}
else
{
obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; uint8 x_169; 
x_161 = lean::cnstr_get(x_155, 0);
lean::inc(x_161);
x_162 = lean::cnstr_get(x_3, 1);
lean::inc(x_162);
x_163 = lean::cnstr_get(x_3, 2);
lean::inc(x_163);
x_164 = lean::cnstr_get(x_2, 1);
lean::inc(x_164);
x_165 = lean::cnstr_get(x_161, 0);
lean::inc(x_165);
x_166 = lean::cnstr_get(x_161, 1);
lean::inc(x_166);
x_167 = lean::cnstr_get(x_161, 2);
lean::inc(x_167);
lean::dec(x_161);
x_168 = lean::cnstr_get(x_165, 1);
lean::inc(x_168);
lean::dec(x_165);
x_169 = lean::nat_dec_eq(x_164, x_168);
lean::dec(x_168);
lean::dec(x_164);
if (x_169 == 0)
{
obj* x_170; obj* x_171; 
lean::inc(x_3);
lean::inc(x_2);
x_170 = l_Lean_Parser_ParsecT_failure___at_Lean_Parser_token___spec__4___rarg(x_2, x_3);
x_171 = lean::cnstr_get(x_170, 0);
lean::inc(x_171);
if (lean::obj_tag(x_171) == 0)
{
uint8 x_172; 
lean::dec(x_170);
x_172 = !lean::is_exclusive(x_171);
if (x_172 == 0)
{
obj* x_173; obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; 
x_173 = lean::cnstr_get(x_171, 2);
x_174 = lean::cnstr_get(x_171, 1);
lean::dec(x_174);
x_175 = lean::cnstr_get(x_171, 0);
lean::dec(x_175);
x_176 = lean::box(0);
x_177 = lean::mk_nat_obj(1u);
x_178 = lean::nat_add(x_162, x_177);
lean::dec(x_162);
x_179 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_179, 0, x_155);
lean::cnstr_set(x_179, 1, x_178);
lean::cnstr_set(x_179, 2, x_163);
lean::cnstr_set(x_171, 2, x_176);
lean::cnstr_set(x_171, 1, x_166);
lean::cnstr_set(x_171, 0, x_167);
x_180 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_173, x_171);
x_181 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_182 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_181, x_180);
x_4 = x_182;
x_5 = x_179;
goto block_154;
}
else
{
obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; obj* x_191; 
x_183 = lean::cnstr_get(x_171, 2);
lean::inc(x_183);
lean::dec(x_171);
x_184 = lean::box(0);
x_185 = lean::mk_nat_obj(1u);
x_186 = lean::nat_add(x_162, x_185);
lean::dec(x_162);
x_187 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_187, 0, x_155);
lean::cnstr_set(x_187, 1, x_186);
lean::cnstr_set(x_187, 2, x_163);
x_188 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_188, 0, x_167);
lean::cnstr_set(x_188, 1, x_166);
lean::cnstr_set(x_188, 2, x_184);
x_189 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_183, x_188);
x_190 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_191 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_190, x_189);
x_4 = x_191;
x_5 = x_187;
goto block_154;
}
}
else
{
obj* x_192; uint8 x_193; 
lean::dec(x_167);
lean::dec(x_166);
lean::dec(x_163);
lean::dec(x_162);
lean::dec(x_155);
x_192 = lean::cnstr_get(x_170, 1);
lean::inc(x_192);
lean::dec(x_170);
x_193 = !lean::is_exclusive(x_171);
if (x_193 == 0)
{
obj* x_194; obj* x_195; 
x_194 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_195 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_194, x_171);
x_4 = x_195;
x_5 = x_192;
goto block_154;
}
else
{
obj* x_196; uint8 x_197; obj* x_198; obj* x_199; obj* x_200; 
x_196 = lean::cnstr_get(x_171, 0);
x_197 = lean::cnstr_get_scalar<uint8>(x_171, sizeof(void*)*1);
lean::inc(x_196);
lean::dec(x_171);
x_198 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_198, 0, x_196);
lean::cnstr_set_scalar(x_198, sizeof(void*)*1, x_197);
x_199 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_200 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_199, x_198);
x_4 = x_200;
x_5 = x_192;
goto block_154;
}
}
}
else
{
obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; 
x_201 = lean::box(0);
x_202 = lean::mk_nat_obj(1u);
x_203 = lean::nat_add(x_162, x_202);
lean::dec(x_162);
x_204 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_204, 0, x_155);
lean::cnstr_set(x_204, 1, x_203);
lean::cnstr_set(x_204, 2, x_163);
x_205 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_205, 0, x_167);
lean::cnstr_set(x_205, 1, x_166);
lean::cnstr_set(x_205, 2, x_201);
x_4 = x_205;
x_5 = x_204;
goto block_154;
}
}
block_154:
{
if (lean::obj_tag(x_4) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_6 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_7 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_4);
x_8 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_5);
return x_9;
}
else
{
obj* x_10; uint8 x_11; obj* x_12; obj* x_13; obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_10 = lean::cnstr_get(x_4, 0);
lean::inc(x_10);
x_11 = lean::cnstr_get_scalar<uint8>(x_4, sizeof(void*)*1);
lean::dec(x_4);
x_38 = lean::cnstr_get(x_10, 0);
lean::inc(x_38);
lean::dec(x_10);
x_39 = l_Lean_Parser_token___closed__1;
lean::inc(x_1);
x_40 = l_Lean_Parser_MonadParsec_observing___at_Lean_Parser_token___spec__2(x_39, x_1, x_38, x_5);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
if (lean::obj_tag(x_41) == 0)
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_42 = lean::cnstr_get(x_40, 1);
lean::inc(x_42);
lean::dec(x_40);
x_43 = lean::cnstr_get(x_41, 0);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_41, 1);
lean::inc(x_44);
x_45 = lean::cnstr_get(x_41, 2);
lean::inc(x_45);
lean::dec(x_41);
lean::inc(x_1);
x_46 = l_Lean_Parser_matchToken(x_1, x_44, x_42);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
if (lean::obj_tag(x_47) == 0)
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; 
x_48 = lean::cnstr_get(x_46, 1);
lean::inc(x_48);
lean::dec(x_46);
x_49 = lean::cnstr_get(x_47, 0);
lean::inc(x_49);
x_50 = lean::cnstr_get(x_47, 1);
lean::inc(x_50);
x_51 = lean::cnstr_get(x_47, 2);
lean::inc(x_51);
lean::dec(x_47);
if (lean::obj_tag(x_49) == 0)
{
lean::dec(x_49);
if (lean::obj_tag(x_43) == 0)
{
obj* x_122; obj* x_123; obj* x_124; 
lean::dec(x_43);
lean::inc(x_1);
x_122 = l_Lean_Parser_numberOrStringLit(x_1, x_50, x_48);
x_123 = lean::cnstr_get(x_122, 0);
lean::inc(x_123);
x_124 = lean::cnstr_get(x_122, 1);
lean::inc(x_124);
lean::dec(x_122);
x_52 = x_123;
x_53 = x_124;
goto block_121;
}
else
{
obj* x_125; obj* x_126; obj* x_127; 
lean::dec(x_43);
lean::inc(x_1);
x_125 = l___private_init_lean_parser_token_4__ident_x27(x_1, x_50, x_48);
x_126 = lean::cnstr_get(x_125, 0);
lean::inc(x_126);
x_127 = lean::cnstr_get(x_125, 1);
lean::inc(x_127);
lean::dec(x_125);
x_52 = x_126;
x_53 = x_127;
goto block_121;
}
}
else
{
obj* x_128; obj* x_129; 
x_128 = lean::cnstr_get(x_49, 0);
lean::inc(x_128);
lean::dec(x_49);
x_129 = lean::cnstr_get(x_128, 2);
lean::inc(x_129);
if (lean::obj_tag(x_129) == 0)
{
lean::dec(x_129);
if (lean::obj_tag(x_43) == 0)
{
obj* x_130; obj* x_131; obj* x_132; 
lean::dec(x_43);
lean::inc(x_2);
x_130 = l___private_init_lean_parser_token_5__mkConsumeToken(x_128, x_2, x_1, x_50, x_48);
lean::dec(x_50);
lean::dec(x_128);
x_131 = lean::cnstr_get(x_130, 0);
lean::inc(x_131);
x_132 = lean::cnstr_get(x_130, 1);
lean::inc(x_132);
lean::dec(x_130);
x_52 = x_131;
x_53 = x_132;
goto block_121;
}
else
{
obj* x_133; obj* x_134; obj* x_135; 
lean::dec(x_43);
lean::inc(x_1);
lean::inc(x_2);
x_133 = l_Lean_Parser_tokenCont(x_2, x_128, x_1, x_50, x_48);
lean::dec(x_128);
x_134 = lean::cnstr_get(x_133, 0);
lean::inc(x_134);
x_135 = lean::cnstr_get(x_133, 1);
lean::inc(x_135);
lean::dec(x_133);
x_52 = x_134;
x_53 = x_135;
goto block_121;
}
}
else
{
obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
lean::dec(x_129);
lean::dec(x_128);
lean::dec(x_43);
x_136 = lean::box(0);
x_137 = l_Lean_Parser_token___closed__2;
x_138 = l_mjoin___rarg___closed__1;
x_139 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_137, x_138, x_136, x_136, x_1, x_50, x_48);
x_140 = lean::cnstr_get(x_139, 0);
lean::inc(x_140);
x_141 = lean::cnstr_get(x_139, 1);
lean::inc(x_141);
lean::dec(x_139);
x_52 = x_140;
x_53 = x_141;
goto block_121;
}
}
block_121:
{
if (lean::obj_tag(x_52) == 0)
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_54 = lean::cnstr_get(x_52, 0);
lean::inc(x_54);
x_55 = lean::cnstr_get(x_52, 1);
lean::inc(x_55);
x_56 = lean::cnstr_get(x_52, 2);
lean::inc(x_56);
lean::dec(x_52);
x_57 = l_Lean_Parser_withTrailing___at_Lean_Parser_token___spec__3(x_54, x_1, x_55, x_53);
lean::dec(x_1);
x_58 = lean::cnstr_get(x_57, 0);
lean::inc(x_58);
if (lean::obj_tag(x_58) == 0)
{
uint8 x_59; 
lean::dec(x_57);
x_59 = !lean::is_exclusive(x_58);
if (x_59 == 0)
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; uint8 x_65; 
x_60 = lean::cnstr_get(x_58, 0);
x_61 = lean::cnstr_get(x_58, 1);
x_62 = lean::cnstr_get(x_58, 2);
lean::inc(x_60);
lean::inc(x_61);
x_63 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_63, 0, x_2);
lean::cnstr_set(x_63, 1, x_61);
lean::cnstr_set(x_63, 2, x_60);
x_64 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_64, 0, x_63);
x_65 = !lean::is_exclusive(x_3);
if (x_65 == 0)
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; 
x_66 = lean::cnstr_get(x_3, 2);
x_67 = lean::cnstr_get(x_3, 0);
lean::dec(x_67);
x_68 = lean::mk_nat_obj(1u);
x_69 = lean::nat_add(x_66, x_68);
lean::dec(x_66);
lean::cnstr_set(x_3, 2, x_69);
lean::cnstr_set(x_3, 0, x_64);
x_70 = l_Lean_Parser_matchToken___closed__1;
lean::cnstr_set(x_58, 2, x_70);
x_71 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_62, x_58);
x_72 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_56, x_71);
x_73 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_51, x_72);
x_74 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_45, x_73);
x_12 = x_74;
x_13 = x_3;
goto block_37;
}
else
{
obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_75 = lean::cnstr_get(x_3, 1);
x_76 = lean::cnstr_get(x_3, 2);
lean::inc(x_76);
lean::inc(x_75);
lean::dec(x_3);
x_77 = lean::mk_nat_obj(1u);
x_78 = lean::nat_add(x_76, x_77);
lean::dec(x_76);
x_79 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_79, 0, x_64);
lean::cnstr_set(x_79, 1, x_75);
lean::cnstr_set(x_79, 2, x_78);
x_80 = l_Lean_Parser_matchToken___closed__1;
lean::cnstr_set(x_58, 2, x_80);
x_81 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_62, x_58);
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_56, x_81);
x_83 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_51, x_82);
x_84 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_45, x_83);
x_12 = x_84;
x_13 = x_79;
goto block_37;
}
}
else
{
obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; 
x_85 = lean::cnstr_get(x_58, 0);
x_86 = lean::cnstr_get(x_58, 1);
x_87 = lean::cnstr_get(x_58, 2);
lean::inc(x_87);
lean::inc(x_86);
lean::inc(x_85);
lean::dec(x_58);
lean::inc(x_85);
lean::inc(x_86);
x_88 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_88, 0, x_2);
lean::cnstr_set(x_88, 1, x_86);
lean::cnstr_set(x_88, 2, x_85);
x_89 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_89, 0, x_88);
x_90 = lean::cnstr_get(x_3, 1);
lean::inc(x_90);
x_91 = lean::cnstr_get(x_3, 2);
lean::inc(x_91);
if (lean::is_exclusive(x_3)) {
 lean::cnstr_release(x_3, 0);
 lean::cnstr_release(x_3, 1);
 lean::cnstr_release(x_3, 2);
 x_92 = x_3;
} else {
 lean::dec_ref(x_3);
 x_92 = lean::box(0);
}
x_93 = lean::mk_nat_obj(1u);
x_94 = lean::nat_add(x_91, x_93);
lean::dec(x_91);
if (lean::is_scalar(x_92)) {
 x_95 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_95 = x_92;
}
lean::cnstr_set(x_95, 0, x_89);
lean::cnstr_set(x_95, 1, x_90);
lean::cnstr_set(x_95, 2, x_94);
x_96 = l_Lean_Parser_matchToken___closed__1;
x_97 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_97, 0, x_85);
lean::cnstr_set(x_97, 1, x_86);
lean::cnstr_set(x_97, 2, x_96);
x_98 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_87, x_97);
x_99 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_56, x_98);
x_100 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_51, x_99);
x_101 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_45, x_100);
x_12 = x_101;
x_13 = x_95;
goto block_37;
}
}
else
{
obj* x_102; uint8 x_103; 
lean::dec(x_3);
lean::dec(x_2);
x_102 = lean::cnstr_get(x_57, 1);
lean::inc(x_102);
lean::dec(x_57);
x_103 = !lean::is_exclusive(x_58);
if (x_103 == 0)
{
obj* x_104; obj* x_105; obj* x_106; 
x_104 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_56, x_58);
x_105 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_51, x_104);
x_106 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_45, x_105);
x_12 = x_106;
x_13 = x_102;
goto block_37;
}
else
{
obj* x_107; uint8 x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; 
x_107 = lean::cnstr_get(x_58, 0);
x_108 = lean::cnstr_get_scalar<uint8>(x_58, sizeof(void*)*1);
lean::inc(x_107);
lean::dec(x_58);
x_109 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_109, 0, x_107);
lean::cnstr_set_scalar(x_109, sizeof(void*)*1, x_108);
x_110 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_56, x_109);
x_111 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_51, x_110);
x_112 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_45, x_111);
x_12 = x_112;
x_13 = x_102;
goto block_37;
}
}
}
else
{
uint8 x_113; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_113 = !lean::is_exclusive(x_52);
if (x_113 == 0)
{
obj* x_114; obj* x_115; 
x_114 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_51, x_52);
x_115 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_45, x_114);
x_12 = x_115;
x_13 = x_53;
goto block_37;
}
else
{
obj* x_116; uint8 x_117; obj* x_118; obj* x_119; obj* x_120; 
x_116 = lean::cnstr_get(x_52, 0);
x_117 = lean::cnstr_get_scalar<uint8>(x_52, sizeof(void*)*1);
lean::inc(x_116);
lean::dec(x_52);
x_118 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_118, 0, x_116);
lean::cnstr_set_scalar(x_118, sizeof(void*)*1, x_117);
x_119 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_51, x_118);
x_120 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_45, x_119);
x_12 = x_120;
x_13 = x_53;
goto block_37;
}
}
}
}
else
{
obj* x_142; uint8 x_143; 
lean::dec(x_43);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_142 = lean::cnstr_get(x_46, 1);
lean::inc(x_142);
lean::dec(x_46);
x_143 = !lean::is_exclusive(x_47);
if (x_143 == 0)
{
obj* x_144; 
x_144 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_45, x_47);
x_12 = x_144;
x_13 = x_142;
goto block_37;
}
else
{
obj* x_145; uint8 x_146; obj* x_147; obj* x_148; 
x_145 = lean::cnstr_get(x_47, 0);
x_146 = lean::cnstr_get_scalar<uint8>(x_47, sizeof(void*)*1);
lean::inc(x_145);
lean::dec(x_47);
x_147 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_147, 0, x_145);
lean::cnstr_set_scalar(x_147, sizeof(void*)*1, x_146);
x_148 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_45, x_147);
x_12 = x_148;
x_13 = x_142;
goto block_37;
}
}
}
else
{
obj* x_149; uint8 x_150; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_149 = lean::cnstr_get(x_40, 1);
lean::inc(x_149);
lean::dec(x_40);
x_150 = !lean::is_exclusive(x_41);
if (x_150 == 0)
{
x_12 = x_41;
x_13 = x_149;
goto block_37;
}
else
{
obj* x_151; uint8 x_152; obj* x_153; 
x_151 = lean::cnstr_get(x_41, 0);
x_152 = lean::cnstr_get_scalar<uint8>(x_41, sizeof(void*)*1);
lean::inc(x_151);
lean::dec(x_41);
x_153 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_153, 0, x_151);
lean::cnstr_set_scalar(x_153, sizeof(void*)*1, x_152);
x_12 = x_153;
x_13 = x_149;
goto block_37;
}
}
block_37:
{
if (lean::obj_tag(x_12) == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_14 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_15 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_12);
x_16 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_14, x_15);
x_17 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_17, 0, x_16);
lean::cnstr_set(x_17, 1, x_13);
return x_17;
}
else
{
if (x_11 == 0)
{
uint8 x_18; 
x_18 = !lean::is_exclusive(x_12);
if (x_18 == 0)
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; 
x_19 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_20 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_19, x_12);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_19, x_20);
x_22 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_22, 0, x_21);
lean::cnstr_set(x_22, 1, x_13);
return x_22;
}
else
{
obj* x_23; uint8 x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_23 = lean::cnstr_get(x_12, 0);
x_24 = lean::cnstr_get_scalar<uint8>(x_12, sizeof(void*)*1);
lean::inc(x_23);
lean::dec(x_12);
x_25 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_25, 0, x_23);
lean::cnstr_set_scalar(x_25, sizeof(void*)*1, x_24);
x_26 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_27 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_26, x_25);
x_28 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_26, x_27);
x_29 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_13);
return x_29;
}
}
else
{
uint8 x_30; 
x_30 = !lean::is_exclusive(x_12);
if (x_30 == 0)
{
uint8 x_31; obj* x_32; 
x_31 = 1;
lean::cnstr_set_scalar(x_12, sizeof(void*)*1, x_31);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_12);
lean::cnstr_set(x_32, 1, x_13);
return x_32;
}
else
{
obj* x_33; uint8 x_34; obj* x_35; obj* x_36; 
x_33 = lean::cnstr_get(x_12, 0);
lean::inc(x_33);
lean::dec(x_12);
x_34 = 1;
x_35 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_35, 0, x_33);
lean::cnstr_set_scalar(x_35, sizeof(void*)*1, x_34);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_13);
return x_36;
}
}
}
}
}
}
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_token___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_token___spec__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_Parser_withTrailing___at_Lean_Parser_token___spec__3___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_withTrailing___at_Lean_Parser_token___spec__3(x_1, x_2, x_3, x_4);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_peekToken___spec__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
lean::inc(x_2);
x_4 = l_Lean_Parser_token(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_4);
if (x_6 == 0)
{
obj* x_7; uint8 x_8; 
x_7 = lean::cnstr_get(x_4, 0);
lean::dec(x_7);
x_8 = !lean::is_exclusive(x_5);
if (x_8 == 0)
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_5, 2);
lean::dec(x_9);
x_10 = lean::cnstr_get(x_5, 1);
lean::dec(x_10);
x_11 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_5, 2, x_11);
lean::cnstr_set(x_5, 1, x_2);
return x_4;
}
else
{
obj* x_12; obj* x_13; obj* x_14; 
x_12 = lean::cnstr_get(x_5, 0);
lean::inc(x_12);
lean::dec(x_5);
x_13 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_14 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_14, 0, x_12);
lean::cnstr_set(x_14, 1, x_2);
lean::cnstr_set(x_14, 2, x_13);
lean::cnstr_set(x_4, 0, x_14);
return x_4;
}
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_15 = lean::cnstr_get(x_4, 1);
lean::inc(x_15);
lean::dec(x_4);
x_16 = lean::cnstr_get(x_5, 0);
lean::inc(x_16);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_17 = x_5;
} else {
 lean::dec_ref(x_5);
 x_17 = lean::box(0);
}
x_18 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_17)) {
 x_19 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_19 = x_17;
}
lean::cnstr_set(x_19, 0, x_16);
lean::cnstr_set(x_19, 1, x_2);
lean::cnstr_set(x_19, 2, x_18);
x_20 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_20, 0, x_19);
lean::cnstr_set(x_20, 1, x_15);
return x_20;
}
}
else
{
uint8 x_21; 
lean::dec(x_2);
x_21 = !lean::is_exclusive(x_4);
if (x_21 == 0)
{
obj* x_22; 
x_22 = lean::cnstr_get(x_4, 0);
lean::dec(x_22);
return x_4;
}
else
{
obj* x_23; obj* x_24; 
x_23 = lean::cnstr_get(x_4, 1);
lean::inc(x_23);
lean::dec(x_4);
x_24 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_24, 0, x_5);
lean::cnstr_set(x_24, 1, x_23);
return x_24;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_observing___at_Lean_Parser_peekToken___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
x_5 = lean::apply_3(x_1, x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_5);
if (x_7 == 0)
{
obj* x_8; uint8 x_9; 
x_8 = lean::cnstr_get(x_5, 0);
lean::dec(x_8);
x_9 = !lean::is_exclusive(x_6);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_10 = lean::cnstr_get(x_6, 0);
x_11 = lean::cnstr_get(x_6, 2);
x_12 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_12, 0, x_10);
x_13 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_6, 2, x_13);
lean::cnstr_set(x_6, 0, x_12);
x_14 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_6);
if (lean::obj_tag(x_14) == 0)
{
lean::cnstr_set(x_5, 0, x_14);
return x_5;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_14, 0);
lean::inc(x_15);
lean::dec(x_14);
x_16 = lean::cnstr_get(x_15, 0);
lean::inc(x_16);
x_17 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_17, 0, x_15);
x_18 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_18, 0, x_17);
lean::cnstr_set(x_18, 1, x_16);
lean::cnstr_set(x_18, 2, x_13);
lean::cnstr_set(x_5, 0, x_18);
return x_5;
}
}
else
{
obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_19 = lean::cnstr_get(x_6, 0);
x_20 = lean::cnstr_get(x_6, 1);
x_21 = lean::cnstr_get(x_6, 2);
lean::inc(x_21);
lean::inc(x_20);
lean::inc(x_19);
lean::dec(x_6);
x_22 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_22, 0, x_19);
x_23 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_22);
lean::cnstr_set(x_24, 1, x_20);
lean::cnstr_set(x_24, 2, x_23);
x_25 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_21, x_24);
if (lean::obj_tag(x_25) == 0)
{
lean::cnstr_set(x_5, 0, x_25);
return x_5;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; 
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
lean::dec(x_25);
x_27 = lean::cnstr_get(x_26, 0);
lean::inc(x_27);
x_28 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_28, 0, x_26);
x_29 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_29, 0, x_28);
lean::cnstr_set(x_29, 1, x_27);
lean::cnstr_set(x_29, 2, x_23);
lean::cnstr_set(x_5, 0, x_29);
return x_5;
}
}
}
else
{
obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_30 = lean::cnstr_get(x_5, 1);
lean::inc(x_30);
lean::dec(x_5);
x_31 = lean::cnstr_get(x_6, 0);
lean::inc(x_31);
x_32 = lean::cnstr_get(x_6, 1);
lean::inc(x_32);
x_33 = lean::cnstr_get(x_6, 2);
lean::inc(x_33);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_34 = x_6;
} else {
 lean::dec_ref(x_6);
 x_34 = lean::box(0);
}
x_35 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_35, 0, x_31);
x_36 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_34)) {
 x_37 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_37 = x_34;
}
lean::cnstr_set(x_37, 0, x_35);
lean::cnstr_set(x_37, 1, x_32);
lean::cnstr_set(x_37, 2, x_36);
x_38 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_33, x_37);
if (lean::obj_tag(x_38) == 0)
{
obj* x_39; 
x_39 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_39, 0, x_38);
lean::cnstr_set(x_39, 1, x_30);
return x_39;
}
else
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_40 = lean::cnstr_get(x_38, 0);
lean::inc(x_40);
lean::dec(x_38);
x_41 = lean::cnstr_get(x_40, 0);
lean::inc(x_41);
x_42 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_42, 0, x_40);
x_43 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_43, 0, x_42);
lean::cnstr_set(x_43, 1, x_41);
lean::cnstr_set(x_43, 2, x_36);
x_44 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_44, 0, x_43);
lean::cnstr_set(x_44, 1, x_30);
return x_44;
}
}
}
else
{
uint8 x_45; 
x_45 = !lean::is_exclusive(x_5);
if (x_45 == 0)
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_46 = lean::cnstr_get(x_5, 0);
lean::dec(x_46);
x_47 = lean::cnstr_get(x_6, 0);
lean::inc(x_47);
lean::dec(x_6);
x_48 = lean::cnstr_get(x_47, 0);
lean::inc(x_48);
x_49 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_49, 0, x_47);
x_50 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_51 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_51, 0, x_49);
lean::cnstr_set(x_51, 1, x_48);
lean::cnstr_set(x_51, 2, x_50);
lean::cnstr_set(x_5, 0, x_51);
return x_5;
}
else
{
obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; 
x_52 = lean::cnstr_get(x_5, 1);
lean::inc(x_52);
lean::dec(x_5);
x_53 = lean::cnstr_get(x_6, 0);
lean::inc(x_53);
lean::dec(x_6);
x_54 = lean::cnstr_get(x_53, 0);
lean::inc(x_54);
x_55 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_55, 0, x_53);
x_56 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_57 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_57, 0, x_55);
lean::cnstr_set(x_57, 1, x_54);
lean::cnstr_set(x_57, 2, x_56);
x_58 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_58, 0, x_57);
lean::cnstr_set(x_58, 1, x_52);
return x_58;
}
}
}
}
obj* l_Lean_Parser_peekToken___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = l_Lean_Parser_ParsecT_lookahead___at_Lean_Parser_peekToken___spec__1(x_1, x_2, x_3);
x_5 = !lean::is_exclusive(x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; 
x_6 = lean::cnstr_get(x_4, 0);
x_7 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_6);
lean::cnstr_set(x_4, 0, x_7);
return x_4;
}
else
{
obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_8 = lean::cnstr_get(x_4, 0);
x_9 = lean::cnstr_get(x_4, 1);
lean::inc(x_9);
lean::inc(x_8);
lean::dec(x_4);
x_10 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_8);
x_11 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_11, 0, x_10);
lean::cnstr_set(x_11, 1, x_9);
return x_11;
}
}
}
obj* _init_l_Lean_Parser_peekToken___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_peekToken___lambda__1), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_peekToken(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
x_4 = l_Lean_Parser_peekToken___closed__1;
x_5 = l_Lean_Parser_MonadParsec_observing___at_Lean_Parser_peekToken___spec__2(x_4, x_1, x_2, x_3);
return x_5;
}
}
obj* l_Lean_Parser_symbolCore___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; 
lean::inc(x_5);
lean::inc(x_4);
x_7 = l_Lean_Parser_token(x_4, x_5, x_6);
x_8 = lean::cnstr_get(x_7, 0);
lean::inc(x_8);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_7);
if (x_9 == 0)
{
obj* x_10; obj* x_11; uint8 x_12; 
x_10 = lean::cnstr_get(x_7, 1);
x_11 = lean::cnstr_get(x_7, 0);
lean::dec(x_11);
x_12 = !lean::is_exclusive(x_8);
if (x_12 == 0)
{
obj* x_13; obj* x_14; obj* x_15; obj* x_16; 
x_13 = lean::cnstr_get(x_8, 0);
x_14 = lean::cnstr_get(x_8, 1);
x_15 = lean::cnstr_get(x_8, 2);
if (lean::obj_tag(x_13) == 0)
{
obj* x_37; obj* x_38; uint8 x_39; 
x_37 = lean::cnstr_get(x_13, 0);
lean::inc(x_37);
x_38 = lean::cnstr_get(x_37, 1);
lean::inc(x_38);
lean::dec(x_37);
x_39 = lean::string_dec_eq(x_3, x_38);
if (x_39 == 0)
{
obj* x_40; obj* x_41; obj* x_42; obj* x_43; 
lean::free_heap_obj(x_8);
lean::free_heap_obj(x_7);
x_40 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_40, 0, x_5);
x_41 = lean::box(0);
x_42 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_38, x_1, x_40, x_41, x_4, x_14, x_10);
lean::dec(x_4);
lean::dec(x_40);
x_43 = lean::cnstr_get(x_42, 0);
lean::inc(x_43);
if (lean::obj_tag(x_43) == 0)
{
uint8 x_44; 
x_44 = !lean::is_exclusive(x_42);
if (x_44 == 0)
{
obj* x_45; uint8 x_46; 
x_45 = lean::cnstr_get(x_42, 0);
lean::dec(x_45);
x_46 = !lean::is_exclusive(x_43);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
x_47 = lean::cnstr_get(x_43, 2);
x_48 = lean::cnstr_get(x_43, 0);
lean::dec(x_48);
x_49 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_43, 2, x_49);
lean::cnstr_set(x_43, 0, x_13);
x_50 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_47, x_43);
x_51 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_50);
x_52 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_49, x_51);
x_53 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_52, x_2);
x_54 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_53);
lean::cnstr_set(x_42, 0, x_54);
return x_42;
}
else
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; 
x_55 = lean::cnstr_get(x_43, 1);
x_56 = lean::cnstr_get(x_43, 2);
lean::inc(x_56);
lean::inc(x_55);
lean::dec(x_43);
x_57 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_58 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_58, 0, x_13);
lean::cnstr_set(x_58, 1, x_55);
lean::cnstr_set(x_58, 2, x_57);
x_59 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_56, x_58);
x_60 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_59);
x_61 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_57, x_60);
x_62 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_61, x_2);
x_63 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_62);
lean::cnstr_set(x_42, 0, x_63);
return x_42;
}
}
else
{
obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_64 = lean::cnstr_get(x_42, 1);
lean::inc(x_64);
lean::dec(x_42);
x_65 = lean::cnstr_get(x_43, 1);
lean::inc(x_65);
x_66 = lean::cnstr_get(x_43, 2);
lean::inc(x_66);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 lean::cnstr_release(x_43, 1);
 lean::cnstr_release(x_43, 2);
 x_67 = x_43;
} else {
 lean::dec_ref(x_43);
 x_67 = lean::box(0);
}
x_68 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_67)) {
 x_69 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_69 = x_67;
}
lean::cnstr_set(x_69, 0, x_13);
lean::cnstr_set(x_69, 1, x_65);
lean::cnstr_set(x_69, 2, x_68);
x_70 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_66, x_69);
x_71 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_70);
x_72 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_68, x_71);
x_73 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_72, x_2);
x_74 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_73);
x_75 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_75, 0, x_74);
lean::cnstr_set(x_75, 1, x_64);
return x_75;
}
}
else
{
uint8 x_76; 
lean::dec(x_13);
x_76 = !lean::is_exclusive(x_42);
if (x_76 == 0)
{
obj* x_77; uint8 x_78; 
x_77 = lean::cnstr_get(x_42, 0);
lean::dec(x_77);
x_78 = !lean::is_exclusive(x_43);
if (x_78 == 0)
{
obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; 
x_79 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_43);
x_80 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_81 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_80, x_79);
x_82 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_81, x_2);
x_83 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_82);
lean::cnstr_set(x_42, 0, x_83);
return x_42;
}
else
{
obj* x_84; uint8 x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
x_84 = lean::cnstr_get(x_43, 0);
x_85 = lean::cnstr_get_scalar<uint8>(x_43, sizeof(void*)*1);
lean::inc(x_84);
lean::dec(x_43);
x_86 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_86, 0, x_84);
lean::cnstr_set_scalar(x_86, sizeof(void*)*1, x_85);
x_87 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_86);
x_88 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_89 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_88, x_87);
x_90 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_89, x_2);
x_91 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_90);
lean::cnstr_set(x_42, 0, x_91);
return x_42;
}
}
else
{
obj* x_92; obj* x_93; uint8 x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; 
x_92 = lean::cnstr_get(x_42, 1);
lean::inc(x_92);
lean::dec(x_42);
x_93 = lean::cnstr_get(x_43, 0);
lean::inc(x_93);
x_94 = lean::cnstr_get_scalar<uint8>(x_43, sizeof(void*)*1);
if (lean::is_exclusive(x_43)) {
 lean::cnstr_release(x_43, 0);
 x_95 = x_43;
} else {
 lean::dec_ref(x_43);
 x_95 = lean::box(0);
}
if (lean::is_scalar(x_95)) {
 x_96 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_96 = x_95;
}
lean::cnstr_set(x_96, 0, x_93);
lean::cnstr_set_scalar(x_96, sizeof(void*)*1, x_94);
x_97 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_96);
x_98 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_99 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_98, x_97);
x_100 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_99, x_2);
x_101 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_100);
x_102 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_102, 0, x_101);
lean::cnstr_set(x_102, 1, x_92);
return x_102;
}
}
}
else
{
obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
lean::dec(x_38);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
x_103 = l_Lean_Parser_finishCommentBlock___closed__2;
lean::cnstr_set(x_8, 2, x_103);
x_104 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_8);
x_105 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_106 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_105, x_104);
x_107 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_106, x_2);
x_108 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_107);
lean::cnstr_set(x_7, 0, x_108);
return x_7;
}
}
else
{
obj* x_109; 
lean::free_heap_obj(x_8);
lean::dec(x_13);
lean::free_heap_obj(x_7);
x_109 = lean::box(0);
x_16 = x_109;
goto block_36;
}
block_36:
{
obj* x_17; obj* x_18; obj* x_19; obj* x_20; uint8 x_21; 
lean::dec(x_16);
x_17 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_17, 0, x_5);
x_18 = lean::box(0);
x_19 = l_String_splitAux___main___closed__1;
x_20 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_19, x_1, x_17, x_18, x_4, x_14, x_10);
lean::dec(x_4);
lean::dec(x_17);
x_21 = !lean::is_exclusive(x_20);
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_22 = lean::cnstr_get(x_20, 0);
x_23 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_22);
x_24 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_25 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_24, x_23);
x_26 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_25, x_2);
x_27 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_26);
lean::cnstr_set(x_20, 0, x_27);
return x_20;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; 
x_28 = lean::cnstr_get(x_20, 0);
x_29 = lean::cnstr_get(x_20, 1);
lean::inc(x_29);
lean::inc(x_28);
lean::dec(x_20);
x_30 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_15, x_28);
x_31 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_31, x_30);
x_33 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_32, x_2);
x_34 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_33);
x_35 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_35, 0, x_34);
lean::cnstr_set(x_35, 1, x_29);
return x_35;
}
}
}
else
{
obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_110 = lean::cnstr_get(x_8, 0);
x_111 = lean::cnstr_get(x_8, 1);
x_112 = lean::cnstr_get(x_8, 2);
lean::inc(x_112);
lean::inc(x_111);
lean::inc(x_110);
lean::dec(x_8);
if (lean::obj_tag(x_110) == 0)
{
obj* x_128; obj* x_129; uint8 x_130; 
x_128 = lean::cnstr_get(x_110, 0);
lean::inc(x_128);
x_129 = lean::cnstr_get(x_128, 1);
lean::inc(x_129);
lean::dec(x_128);
x_130 = lean::string_dec_eq(x_3, x_129);
if (x_130 == 0)
{
obj* x_131; obj* x_132; obj* x_133; obj* x_134; 
lean::free_heap_obj(x_7);
x_131 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_131, 0, x_5);
x_132 = lean::box(0);
x_133 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_129, x_1, x_131, x_132, x_4, x_111, x_10);
lean::dec(x_4);
lean::dec(x_131);
x_134 = lean::cnstr_get(x_133, 0);
lean::inc(x_134);
if (lean::obj_tag(x_134) == 0)
{
obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; 
x_135 = lean::cnstr_get(x_133, 1);
lean::inc(x_135);
if (lean::is_exclusive(x_133)) {
 lean::cnstr_release(x_133, 0);
 lean::cnstr_release(x_133, 1);
 x_136 = x_133;
} else {
 lean::dec_ref(x_133);
 x_136 = lean::box(0);
}
x_137 = lean::cnstr_get(x_134, 1);
lean::inc(x_137);
x_138 = lean::cnstr_get(x_134, 2);
lean::inc(x_138);
if (lean::is_exclusive(x_134)) {
 lean::cnstr_release(x_134, 0);
 lean::cnstr_release(x_134, 1);
 lean::cnstr_release(x_134, 2);
 x_139 = x_134;
} else {
 lean::dec_ref(x_134);
 x_139 = lean::box(0);
}
x_140 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_139)) {
 x_141 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_141 = x_139;
}
lean::cnstr_set(x_141, 0, x_110);
lean::cnstr_set(x_141, 1, x_137);
lean::cnstr_set(x_141, 2, x_140);
x_142 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_138, x_141);
x_143 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_112, x_142);
x_144 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_140, x_143);
x_145 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_144, x_2);
x_146 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_145);
if (lean::is_scalar(x_136)) {
 x_147 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_147 = x_136;
}
lean::cnstr_set(x_147, 0, x_146);
lean::cnstr_set(x_147, 1, x_135);
return x_147;
}
else
{
obj* x_148; obj* x_149; obj* x_150; uint8 x_151; obj* x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; 
lean::dec(x_110);
x_148 = lean::cnstr_get(x_133, 1);
lean::inc(x_148);
if (lean::is_exclusive(x_133)) {
 lean::cnstr_release(x_133, 0);
 lean::cnstr_release(x_133, 1);
 x_149 = x_133;
} else {
 lean::dec_ref(x_133);
 x_149 = lean::box(0);
}
x_150 = lean::cnstr_get(x_134, 0);
lean::inc(x_150);
x_151 = lean::cnstr_get_scalar<uint8>(x_134, sizeof(void*)*1);
if (lean::is_exclusive(x_134)) {
 lean::cnstr_release(x_134, 0);
 x_152 = x_134;
} else {
 lean::dec_ref(x_134);
 x_152 = lean::box(0);
}
if (lean::is_scalar(x_152)) {
 x_153 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_153 = x_152;
}
lean::cnstr_set(x_153, 0, x_150);
lean::cnstr_set_scalar(x_153, sizeof(void*)*1, x_151);
x_154 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_112, x_153);
x_155 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_156 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_155, x_154);
x_157 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_156, x_2);
x_158 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_157);
if (lean::is_scalar(x_149)) {
 x_159 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_159 = x_149;
}
lean::cnstr_set(x_159, 0, x_158);
lean::cnstr_set(x_159, 1, x_148);
return x_159;
}
}
else
{
obj* x_160; obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; 
lean::dec(x_129);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
x_160 = l_Lean_Parser_finishCommentBlock___closed__2;
x_161 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_161, 0, x_110);
lean::cnstr_set(x_161, 1, x_111);
lean::cnstr_set(x_161, 2, x_160);
x_162 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_112, x_161);
x_163 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_164 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_163, x_162);
x_165 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_164, x_2);
x_166 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_165);
lean::cnstr_set(x_7, 0, x_166);
return x_7;
}
}
else
{
obj* x_167; 
lean::dec(x_110);
lean::free_heap_obj(x_7);
x_167 = lean::box(0);
x_113 = x_167;
goto block_127;
}
block_127:
{
obj* x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; 
lean::dec(x_113);
x_114 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_114, 0, x_5);
x_115 = lean::box(0);
x_116 = l_String_splitAux___main___closed__1;
x_117 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_116, x_1, x_114, x_115, x_4, x_111, x_10);
lean::dec(x_4);
lean::dec(x_114);
x_118 = lean::cnstr_get(x_117, 0);
lean::inc(x_118);
x_119 = lean::cnstr_get(x_117, 1);
lean::inc(x_119);
if (lean::is_exclusive(x_117)) {
 lean::cnstr_release(x_117, 0);
 lean::cnstr_release(x_117, 1);
 x_120 = x_117;
} else {
 lean::dec_ref(x_117);
 x_120 = lean::box(0);
}
x_121 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_112, x_118);
x_122 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_123 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_122, x_121);
x_124 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_123, x_2);
x_125 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_124);
if (lean::is_scalar(x_120)) {
 x_126 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_126 = x_120;
}
lean::cnstr_set(x_126, 0, x_125);
lean::cnstr_set(x_126, 1, x_119);
return x_126;
}
}
}
else
{
obj* x_168; obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; 
x_168 = lean::cnstr_get(x_7, 1);
lean::inc(x_168);
lean::dec(x_7);
x_169 = lean::cnstr_get(x_8, 0);
lean::inc(x_169);
x_170 = lean::cnstr_get(x_8, 1);
lean::inc(x_170);
x_171 = lean::cnstr_get(x_8, 2);
lean::inc(x_171);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 lean::cnstr_release(x_8, 1);
 lean::cnstr_release(x_8, 2);
 x_172 = x_8;
} else {
 lean::dec_ref(x_8);
 x_172 = lean::box(0);
}
if (lean::obj_tag(x_169) == 0)
{
obj* x_188; obj* x_189; uint8 x_190; 
x_188 = lean::cnstr_get(x_169, 0);
lean::inc(x_188);
x_189 = lean::cnstr_get(x_188, 1);
lean::inc(x_189);
lean::dec(x_188);
x_190 = lean::string_dec_eq(x_3, x_189);
if (x_190 == 0)
{
obj* x_191; obj* x_192; obj* x_193; obj* x_194; 
lean::dec(x_172);
x_191 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_191, 0, x_5);
x_192 = lean::box(0);
x_193 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_189, x_1, x_191, x_192, x_4, x_170, x_168);
lean::dec(x_4);
lean::dec(x_191);
x_194 = lean::cnstr_get(x_193, 0);
lean::inc(x_194);
if (lean::obj_tag(x_194) == 0)
{
obj* x_195; obj* x_196; obj* x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; 
x_195 = lean::cnstr_get(x_193, 1);
lean::inc(x_195);
if (lean::is_exclusive(x_193)) {
 lean::cnstr_release(x_193, 0);
 lean::cnstr_release(x_193, 1);
 x_196 = x_193;
} else {
 lean::dec_ref(x_193);
 x_196 = lean::box(0);
}
x_197 = lean::cnstr_get(x_194, 1);
lean::inc(x_197);
x_198 = lean::cnstr_get(x_194, 2);
lean::inc(x_198);
if (lean::is_exclusive(x_194)) {
 lean::cnstr_release(x_194, 0);
 lean::cnstr_release(x_194, 1);
 lean::cnstr_release(x_194, 2);
 x_199 = x_194;
} else {
 lean::dec_ref(x_194);
 x_199 = lean::box(0);
}
x_200 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_199)) {
 x_201 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_201 = x_199;
}
lean::cnstr_set(x_201, 0, x_169);
lean::cnstr_set(x_201, 1, x_197);
lean::cnstr_set(x_201, 2, x_200);
x_202 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_198, x_201);
x_203 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_171, x_202);
x_204 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_200, x_203);
x_205 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_204, x_2);
x_206 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_205);
if (lean::is_scalar(x_196)) {
 x_207 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_207 = x_196;
}
lean::cnstr_set(x_207, 0, x_206);
lean::cnstr_set(x_207, 1, x_195);
return x_207;
}
else
{
obj* x_208; obj* x_209; obj* x_210; uint8 x_211; obj* x_212; obj* x_213; obj* x_214; obj* x_215; obj* x_216; obj* x_217; obj* x_218; obj* x_219; 
lean::dec(x_169);
x_208 = lean::cnstr_get(x_193, 1);
lean::inc(x_208);
if (lean::is_exclusive(x_193)) {
 lean::cnstr_release(x_193, 0);
 lean::cnstr_release(x_193, 1);
 x_209 = x_193;
} else {
 lean::dec_ref(x_193);
 x_209 = lean::box(0);
}
x_210 = lean::cnstr_get(x_194, 0);
lean::inc(x_210);
x_211 = lean::cnstr_get_scalar<uint8>(x_194, sizeof(void*)*1);
if (lean::is_exclusive(x_194)) {
 lean::cnstr_release(x_194, 0);
 x_212 = x_194;
} else {
 lean::dec_ref(x_194);
 x_212 = lean::box(0);
}
if (lean::is_scalar(x_212)) {
 x_213 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_213 = x_212;
}
lean::cnstr_set(x_213, 0, x_210);
lean::cnstr_set_scalar(x_213, sizeof(void*)*1, x_211);
x_214 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_171, x_213);
x_215 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_216 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_215, x_214);
x_217 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_216, x_2);
x_218 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_217);
if (lean::is_scalar(x_209)) {
 x_219 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_219 = x_209;
}
lean::cnstr_set(x_219, 0, x_218);
lean::cnstr_set(x_219, 1, x_208);
return x_219;
}
}
else
{
obj* x_220; obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; 
lean::dec(x_189);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
x_220 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_172)) {
 x_221 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_221 = x_172;
}
lean::cnstr_set(x_221, 0, x_169);
lean::cnstr_set(x_221, 1, x_170);
lean::cnstr_set(x_221, 2, x_220);
x_222 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_171, x_221);
x_223 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_224 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_223, x_222);
x_225 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_224, x_2);
x_226 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_225);
x_227 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_227, 0, x_226);
lean::cnstr_set(x_227, 1, x_168);
return x_227;
}
}
else
{
obj* x_228; 
lean::dec(x_172);
lean::dec(x_169);
x_228 = lean::box(0);
x_173 = x_228;
goto block_187;
}
block_187:
{
obj* x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; 
lean::dec(x_173);
x_174 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_174, 0, x_5);
x_175 = lean::box(0);
x_176 = l_String_splitAux___main___closed__1;
x_177 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_176, x_1, x_174, x_175, x_4, x_170, x_168);
lean::dec(x_4);
lean::dec(x_174);
x_178 = lean::cnstr_get(x_177, 0);
lean::inc(x_178);
x_179 = lean::cnstr_get(x_177, 1);
lean::inc(x_179);
if (lean::is_exclusive(x_177)) {
 lean::cnstr_release(x_177, 0);
 lean::cnstr_release(x_177, 1);
 x_180 = x_177;
} else {
 lean::dec_ref(x_177);
 x_180 = lean::box(0);
}
x_181 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_171, x_178);
x_182 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_183 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_182, x_181);
x_184 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_183, x_2);
x_185 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_184);
if (lean::is_scalar(x_180)) {
 x_186 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_186 = x_180;
}
lean::cnstr_set(x_186, 0, x_185);
lean::cnstr_set(x_186, 1, x_179);
return x_186;
}
}
}
else
{
uint8 x_229; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_1);
x_229 = !lean::is_exclusive(x_7);
if (x_229 == 0)
{
obj* x_230; uint8 x_231; 
x_230 = lean::cnstr_get(x_7, 0);
lean::dec(x_230);
x_231 = !lean::is_exclusive(x_8);
if (x_231 == 0)
{
obj* x_232; obj* x_233; obj* x_234; obj* x_235; 
x_232 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_233 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_232, x_8);
x_234 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_233, x_2);
x_235 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_234);
lean::cnstr_set(x_7, 0, x_235);
return x_7;
}
else
{
obj* x_236; uint8 x_237; obj* x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; 
x_236 = lean::cnstr_get(x_8, 0);
x_237 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
lean::inc(x_236);
lean::dec(x_8);
x_238 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_238, 0, x_236);
lean::cnstr_set_scalar(x_238, sizeof(void*)*1, x_237);
x_239 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_240 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_239, x_238);
x_241 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_240, x_2);
x_242 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_241);
lean::cnstr_set(x_7, 0, x_242);
return x_7;
}
}
else
{
obj* x_243; obj* x_244; uint8 x_245; obj* x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; obj* x_252; 
x_243 = lean::cnstr_get(x_7, 1);
lean::inc(x_243);
lean::dec(x_7);
x_244 = lean::cnstr_get(x_8, 0);
lean::inc(x_244);
x_245 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
if (lean::is_exclusive(x_8)) {
 lean::cnstr_release(x_8, 0);
 x_246 = x_8;
} else {
 lean::dec_ref(x_8);
 x_246 = lean::box(0);
}
if (lean::is_scalar(x_246)) {
 x_247 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_247 = x_246;
}
lean::cnstr_set(x_247, 0, x_244);
lean::cnstr_set_scalar(x_247, sizeof(void*)*1, x_245);
x_248 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_249 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_248, x_247);
x_250 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_249, x_2);
x_251 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_250);
x_252 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_252, 0, x_251);
lean::cnstr_set(x_252, 1, x_243);
return x_252;
}
}
}
}
obj* l_Lean_Parser_symbolCore___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; 
lean::inc(x_2);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_5, 0, x_2);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___rarg___lambda__1___boxed), 6, 3);
lean::closure_set(x_6, 0, x_4);
lean::closure_set(x_6, 1, x_5);
lean::closure_set(x_6, 2, x_2);
x_7 = lean::apply_2(x_1, lean::box(0), x_6);
return x_7;
}
}
obj* l_Lean_Parser_symbolCore(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Lean_Parser_symbolCore___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_symbolCore___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_3);
return x_7;
}
}
obj* l_Lean_Parser_symbolCore___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_symbolCore___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
return x_5;
}
}
obj* l_Lean_Parser_symbolCore___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_symbolCore(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_symbol___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_String_trim(x_2);
lean::inc(x_4);
x_5 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_5, 0, x_4);
x_6 = l_Lean_Parser_symbolCore___rarg(x_1, x_4, x_3, x_5);
return x_6;
}
}
obj* l_Lean_Parser_symbol(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbol___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_symbol___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_symbol___rarg(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
obj* l_Lean_Parser_symbol___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_symbol(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_symbol_tokens___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_3 = l_String_trim(x_1);
x_4 = lean::box(0);
x_5 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_5, 0, x_3);
lean::cnstr_set(x_5, 1, x_2);
lean::cnstr_set(x_5, 2, x_4);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_7, 0, x_5);
lean::cnstr_set(x_7, 1, x_6);
return x_7;
}
}
obj* l_Lean_Parser_symbol_tokens(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbol_tokens___rarg___boxed), 2, 0);
return x_3;
}
}
obj* l_Lean_Parser_symbol_tokens___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_symbol_tokens___rarg(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_symbol_tokens___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_symbol_tokens(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_symbol_View___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = l_Lean_Parser_raw_view___rarg___closed__1;
x_5 = l_Lean_Parser_raw_view___rarg___closed__2;
x_6 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_6, 0, x_4);
lean::cnstr_set(x_6, 1, x_5);
return x_6;
}
}
obj* l_Lean_Parser_symbol_View(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbol_View___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_symbol_View___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_symbol_View___rarg(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_symbol_View___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_symbol_View(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_symbol_viewDefault___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::box(0);
return x_4;
}
}
obj* l_Lean_Parser_symbol_viewDefault(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbol_viewDefault___rarg___boxed), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_symbol_viewDefault___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_symbol_viewDefault___rarg(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_symbol_viewDefault___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_symbol_viewDefault(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_number_Parser___rarg___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = lean::mk_string("number");
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
return x_2;
}
}
obj* l_Lean_Parser_number_Parser___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; 
lean::inc(x_2);
lean::inc(x_1);
x_4 = l_Lean_Parser_token(x_1, x_2, x_3);
x_5 = lean::cnstr_get(x_4, 0);
lean::inc(x_5);
if (lean::obj_tag(x_5) == 0)
{
uint8 x_6; 
x_6 = !lean::is_exclusive(x_4);
if (x_6 == 0)
{
obj* x_7; obj* x_8; uint8 x_9; 
x_7 = lean::cnstr_get(x_4, 1);
x_8 = lean::cnstr_get(x_4, 0);
lean::dec(x_8);
x_9 = !lean::is_exclusive(x_5);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; obj* x_13; uint8 x_14; 
x_10 = lean::cnstr_get(x_5, 0);
x_11 = lean::cnstr_get(x_5, 1);
x_12 = lean::cnstr_get(x_5, 2);
x_13 = l_Lean_Parser_number;
x_14 = l_Lean_Parser_Syntax_isOfKind___main(x_13, x_10);
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; 
lean::free_heap_obj(x_5);
lean::dec(x_10);
lean::free_heap_obj(x_4);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_2);
x_16 = lean::box(0);
x_17 = l_String_splitAux___main___closed__1;
x_18 = l_Lean_Parser_number_Parser___rarg___lambda__1___closed__1;
x_19 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_17, x_18, x_15, x_16, x_1, x_11, x_7);
lean::dec(x_1);
lean::dec(x_15);
x_20 = !lean::is_exclusive(x_19);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_21 = lean::cnstr_get(x_19, 0);
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_21);
x_23 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_24 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_23, x_22);
x_25 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_24);
lean::cnstr_set(x_19, 0, x_25);
return x_19;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_26 = lean::cnstr_get(x_19, 0);
x_27 = lean::cnstr_get(x_19, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_19);
x_28 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_26);
x_29 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_30 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_29, x_28);
x_31 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_30);
x_32 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_32, 0, x_31);
lean::cnstr_set(x_32, 1, x_27);
return x_32;
}
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
lean::dec(x_2);
lean::dec(x_1);
x_33 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_5, 2, x_33);
x_34 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_5);
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_33, x_34);
x_36 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_35);
lean::cnstr_set(x_4, 0, x_36);
return x_4;
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; uint8 x_41; 
x_37 = lean::cnstr_get(x_5, 0);
x_38 = lean::cnstr_get(x_5, 1);
x_39 = lean::cnstr_get(x_5, 2);
lean::inc(x_39);
lean::inc(x_38);
lean::inc(x_37);
lean::dec(x_5);
x_40 = l_Lean_Parser_number;
x_41 = l_Lean_Parser_Syntax_isOfKind___main(x_40, x_37);
if (x_41 == 0)
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; 
lean::dec(x_37);
lean::free_heap_obj(x_4);
x_42 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_42, 0, x_2);
x_43 = lean::box(0);
x_44 = l_String_splitAux___main___closed__1;
x_45 = l_Lean_Parser_number_Parser___rarg___lambda__1___closed__1;
x_46 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_44, x_45, x_42, x_43, x_1, x_38, x_7);
lean::dec(x_1);
lean::dec(x_42);
x_47 = lean::cnstr_get(x_46, 0);
lean::inc(x_47);
x_48 = lean::cnstr_get(x_46, 1);
lean::inc(x_48);
if (lean::is_exclusive(x_46)) {
 lean::cnstr_release(x_46, 0);
 lean::cnstr_release(x_46, 1);
 x_49 = x_46;
} else {
 lean::dec_ref(x_46);
 x_49 = lean::box(0);
}
x_50 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_39, x_47);
x_51 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_52 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_51, x_50);
x_53 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_52);
if (lean::is_scalar(x_49)) {
 x_54 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_54 = x_49;
}
lean::cnstr_set(x_54, 0, x_53);
lean::cnstr_set(x_54, 1, x_48);
return x_54;
}
else
{
obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; 
lean::dec(x_2);
lean::dec(x_1);
x_55 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_56 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_56, 0, x_37);
lean::cnstr_set(x_56, 1, x_38);
lean::cnstr_set(x_56, 2, x_55);
x_57 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_39, x_56);
x_58 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_55, x_57);
x_59 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_58);
lean::cnstr_set(x_4, 0, x_59);
return x_4;
}
}
}
else
{
obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; uint8 x_66; 
x_60 = lean::cnstr_get(x_4, 1);
lean::inc(x_60);
lean::dec(x_4);
x_61 = lean::cnstr_get(x_5, 0);
lean::inc(x_61);
x_62 = lean::cnstr_get(x_5, 1);
lean::inc(x_62);
x_63 = lean::cnstr_get(x_5, 2);
lean::inc(x_63);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 lean::cnstr_release(x_5, 2);
 x_64 = x_5;
} else {
 lean::dec_ref(x_5);
 x_64 = lean::box(0);
}
x_65 = l_Lean_Parser_number;
x_66 = l_Lean_Parser_Syntax_isOfKind___main(x_65, x_61);
if (x_66 == 0)
{
obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; 
lean::dec(x_64);
lean::dec(x_61);
x_67 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_67, 0, x_2);
x_68 = lean::box(0);
x_69 = l_String_splitAux___main___closed__1;
x_70 = l_Lean_Parser_number_Parser___rarg___lambda__1___closed__1;
x_71 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_69, x_70, x_67, x_68, x_1, x_62, x_60);
lean::dec(x_1);
lean::dec(x_67);
x_72 = lean::cnstr_get(x_71, 0);
lean::inc(x_72);
x_73 = lean::cnstr_get(x_71, 1);
lean::inc(x_73);
if (lean::is_exclusive(x_71)) {
 lean::cnstr_release(x_71, 0);
 lean::cnstr_release(x_71, 1);
 x_74 = x_71;
} else {
 lean::dec_ref(x_71);
 x_74 = lean::box(0);
}
x_75 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_63, x_72);
x_76 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_77 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_76, x_75);
x_78 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_77);
if (lean::is_scalar(x_74)) {
 x_79 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_79 = x_74;
}
lean::cnstr_set(x_79, 0, x_78);
lean::cnstr_set(x_79, 1, x_73);
return x_79;
}
else
{
obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
lean::dec(x_2);
lean::dec(x_1);
x_80 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_64)) {
 x_81 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_81 = x_64;
}
lean::cnstr_set(x_81, 0, x_61);
lean::cnstr_set(x_81, 1, x_62);
lean::cnstr_set(x_81, 2, x_80);
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_63, x_81);
x_83 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_80, x_82);
x_84 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_83);
x_85 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_85, 0, x_84);
lean::cnstr_set(x_85, 1, x_60);
return x_85;
}
}
}
else
{
uint8 x_86; 
lean::dec(x_2);
lean::dec(x_1);
x_86 = !lean::is_exclusive(x_4);
if (x_86 == 0)
{
obj* x_87; uint8 x_88; 
x_87 = lean::cnstr_get(x_4, 0);
lean::dec(x_87);
x_88 = !lean::is_exclusive(x_5);
if (x_88 == 0)
{
obj* x_89; obj* x_90; obj* x_91; 
x_89 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_90 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_89, x_5);
x_91 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_90);
lean::cnstr_set(x_4, 0, x_91);
return x_4;
}
else
{
obj* x_92; uint8 x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_92 = lean::cnstr_get(x_5, 0);
x_93 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
lean::inc(x_92);
lean::dec(x_5);
x_94 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_94, 0, x_92);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_93);
x_95 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_96 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_95, x_94);
x_97 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_96);
lean::cnstr_set(x_4, 0, x_97);
return x_4;
}
}
else
{
obj* x_98; obj* x_99; uint8 x_100; obj* x_101; obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_98 = lean::cnstr_get(x_4, 1);
lean::inc(x_98);
lean::dec(x_4);
x_99 = lean::cnstr_get(x_5, 0);
lean::inc(x_99);
x_100 = lean::cnstr_get_scalar<uint8>(x_5, sizeof(void*)*1);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 x_101 = x_5;
} else {
 lean::dec_ref(x_5);
 x_101 = lean::box(0);
}
if (lean::is_scalar(x_101)) {
 x_102 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_102 = x_101;
}
lean::cnstr_set(x_102, 0, x_99);
lean::cnstr_set_scalar(x_102, sizeof(void*)*1, x_100);
x_103 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_104 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_103, x_102);
x_105 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_104);
x_106 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_106, 0, x_105);
lean::cnstr_set(x_106, 1, x_98);
return x_106;
}
}
}
}
obj* _init_l_Lean_Parser_number_Parser___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser___rarg___lambda__1), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_number_Parser___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Parser_number_Parser___rarg___closed__1;
x_3 = lean::apply_2(x_1, lean::box(0), x_2);
return x_3;
}
}
obj* l_Lean_Parser_number_Parser(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_Parser_number_Parser___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_number_Parser(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_number_Parser_tokens(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
}
obj* l_Lean_Parser_number_Parser_tokens___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_number_Parser_tokens(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_number_Parser_view___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_number_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
return x_2;
}
}
obj* _init_l_Lean_Parser_number_Parser_view___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_number_HasView;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
return x_2;
}
}
obj* l_Lean_Parser_number_Parser_view___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Parser_number_Parser_view___rarg___closed__1;
x_3 = l_Lean_Parser_number_Parser_view___rarg___closed__2;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_Lean_Parser_number_Parser_view(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_number_Parser_view___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_Parser_number_Parser_view___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_number_Parser_view___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_number_Parser_view___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_number_Parser_view(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l___private_init_lean_parser_token_7__toNatCore___main(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; uint8 x_6; 
x_5 = lean::mk_nat_obj(0u);
x_6 = lean::nat_dec_eq(x_3, x_5);
if (x_6 == 0)
{
obj* x_7; obj* x_8; uint32 x_9; uint8 x_10; obj* x_11; obj* x_12; 
x_7 = lean::mk_nat_obj(1u);
x_8 = lean::nat_sub(x_3, x_7);
lean::dec(x_3);
x_9 = l_String_OldIterator_curr___main(x_2);
x_10 = l_Char_isDigit(x_9);
x_11 = lean::nat_mul(x_4, x_1);
lean::dec(x_4);
x_12 = l_String_OldIterator_next___main(x_2);
if (x_10 == 0)
{
uint32 x_13; uint8 x_14; 
x_13 = 97;
x_14 = x_13 <= x_9;
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_15 = lean::uint32_to_nat(x_9);
x_16 = l_Lean_Parser_parseHexDigit___rarg___lambda__5___closed__1;
x_17 = lean::nat_sub(x_15, x_16);
lean::dec(x_15);
x_18 = lean::nat_add(x_11, x_17);
lean::dec(x_17);
lean::dec(x_11);
x_2 = x_12;
x_3 = x_8;
x_4 = x_18;
goto _start;
}
else
{
uint32 x_20; uint8 x_21; 
x_20 = 102;
x_21 = x_9 <= x_20;
if (x_21 == 0)
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; 
x_22 = lean::uint32_to_nat(x_9);
x_23 = l_Lean_Parser_parseHexDigit___rarg___lambda__5___closed__1;
x_24 = lean::nat_sub(x_22, x_23);
lean::dec(x_22);
x_25 = lean::nat_add(x_11, x_24);
lean::dec(x_24);
lean::dec(x_11);
x_2 = x_12;
x_3 = x_8;
x_4 = x_25;
goto _start;
}
else
{
obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; 
x_27 = lean::uint32_to_nat(x_9);
x_28 = l_Lean_Parser_parseHexDigit___rarg___lambda__3___closed__1;
x_29 = lean::nat_sub(x_27, x_28);
lean::dec(x_27);
x_30 = lean::nat_add(x_11, x_29);
lean::dec(x_29);
lean::dec(x_11);
x_2 = x_12;
x_3 = x_8;
x_4 = x_30;
goto _start;
}
}
}
else
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_32 = lean::uint32_to_nat(x_9);
x_33 = l_String_foldlAux___main___at_String_toNat___spec__1___closed__1;
x_34 = lean::nat_sub(x_32, x_33);
lean::dec(x_32);
x_35 = lean::nat_add(x_11, x_34);
lean::dec(x_34);
lean::dec(x_11);
x_2 = x_12;
x_3 = x_8;
x_4 = x_35;
goto _start;
}
}
else
{
lean::dec(x_3);
lean::dec(x_2);
return x_4;
}
}
}
obj* l___private_init_lean_parser_token_7__toNatCore___main___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_token_7__toNatCore___main(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l___private_init_lean_parser_token_7__toNatCore(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_token_7__toNatCore___main(x_1, x_2, x_3, x_4);
return x_5;
}
}
obj* l___private_init_lean_parser_token_7__toNatCore___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l___private_init_lean_parser_token_7__toNatCore(x_1, x_2, x_3, x_4);
lean::dec(x_1);
return x_5;
}
}
obj* l___private_init_lean_parser_token_8__toNatBase(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_3 = lean::mk_nat_obj(0u);
lean::inc(x_1);
x_4 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_4, 0, x_1);
lean::cnstr_set(x_4, 1, x_3);
lean::cnstr_set(x_4, 2, x_3);
x_5 = lean::string_length(x_1);
lean::dec(x_1);
x_6 = l___private_init_lean_parser_token_7__toNatCore___main(x_2, x_4, x_5, x_3);
return x_6;
}
}
obj* l___private_init_lean_parser_token_8__toNatBase___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l___private_init_lean_parser_token_8__toNatBase(x_1, x_2);
lean::dec(x_2);
return x_3;
}
}
obj* l_Lean_Parser_number_View_toNat___main(obj* x_1) {
_start:
{
switch (lean::obj_tag(x_1)) {
case 0:
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
lean::dec(x_1);
if (lean::obj_tag(x_2) == 0)
{
obj* x_3; 
lean::dec(x_2);
x_3 = lean::mk_nat_obj(1138u);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; 
x_4 = lean::cnstr_get(x_2, 0);
lean::inc(x_4);
lean::dec(x_2);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = l_String_toNat(x_5);
lean::dec(x_5);
return x_6;
}
}
case 1:
{
obj* x_7; 
x_7 = lean::cnstr_get(x_1, 0);
lean::inc(x_7);
lean::dec(x_1);
if (lean::obj_tag(x_7) == 0)
{
obj* x_8; 
lean::dec(x_7);
x_8 = lean::mk_nat_obj(1138u);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; obj* x_12; 
x_9 = lean::cnstr_get(x_7, 0);
lean::inc(x_9);
lean::dec(x_7);
x_10 = lean::cnstr_get(x_9, 1);
lean::inc(x_10);
lean::dec(x_9);
x_11 = lean::mk_nat_obj(2u);
x_12 = l___private_init_lean_parser_token_8__toNatBase(x_10, x_11);
return x_12;
}
}
case 2:
{
obj* x_13; 
x_13 = lean::cnstr_get(x_1, 0);
lean::inc(x_13);
lean::dec(x_1);
if (lean::obj_tag(x_13) == 0)
{
obj* x_14; 
lean::dec(x_13);
x_14 = lean::mk_nat_obj(1138u);
return x_14;
}
else
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_15 = lean::cnstr_get(x_13, 0);
lean::inc(x_15);
lean::dec(x_13);
x_16 = lean::cnstr_get(x_15, 1);
lean::inc(x_16);
lean::dec(x_15);
x_17 = lean::mk_nat_obj(8u);
x_18 = l___private_init_lean_parser_token_8__toNatBase(x_16, x_17);
return x_18;
}
}
default: 
{
obj* x_19; 
x_19 = lean::cnstr_get(x_1, 0);
lean::inc(x_19);
lean::dec(x_1);
if (lean::obj_tag(x_19) == 0)
{
obj* x_20; 
lean::dec(x_19);
x_20 = lean::mk_nat_obj(1138u);
return x_20;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_21 = lean::cnstr_get(x_19, 0);
lean::inc(x_21);
lean::dec(x_19);
x_22 = lean::cnstr_get(x_21, 1);
lean::inc(x_22);
lean::dec(x_21);
x_23 = lean::mk_nat_obj(16u);
x_24 = l___private_init_lean_parser_token_8__toNatBase(x_22, x_23);
return x_24;
}
}
}
}
}
obj* l_Lean_Parser_number_View_toNat(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_number_View_toNat___main(x_1);
return x_2;
}
}
obj* l_Lean_Parser_number_View_ofNat(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; 
x_2 = lean::box(0);
x_3 = l_Nat_repr(x_1);
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
x_5 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_5, 0, x_4);
x_6 = lean::alloc_cnstr(0, 1, 0);
lean::cnstr_set(x_6, 0, x_5);
return x_6;
}
}
obj* l_Lean_Parser_tryView___at_Lean_Parser_stringLit_Parser___spec__1(obj* x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_Lean_Parser_Syntax_isOfKind___main(x_1, x_2);
if (x_3 == 0)
{
obj* x_4; 
lean::dec(x_2);
x_4 = lean::box(0);
return x_4;
}
else
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_5 = l_Lean_Parser_stringLit_HasView;
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
x_7 = lean::apply_1(x_6, x_2);
x_8 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_8, 0, x_7);
return x_8;
}
}
}
obj* l_Lean_Parser_stringLit_Parser___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_3);
lean::inc(x_2);
x_5 = l_Lean_Parser_token(x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_5);
if (x_7 == 0)
{
obj* x_8; obj* x_9; uint8 x_10; 
x_8 = lean::cnstr_get(x_5, 1);
x_9 = lean::cnstr_get(x_5, 0);
lean::dec(x_9);
x_10 = !lean::is_exclusive(x_6);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_11 = lean::cnstr_get(x_6, 0);
x_12 = lean::cnstr_get(x_6, 1);
x_13 = lean::cnstr_get(x_6, 2);
x_14 = l_Lean_Parser_stringLit;
lean::inc(x_11);
x_15 = l_Lean_Parser_tryView___at_Lean_Parser_stringLit_Parser___spec__1(x_14, x_11);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; obj* x_17; obj* x_18; obj* x_19; uint8 x_20; 
lean::dec(x_15);
lean::free_heap_obj(x_6);
lean::dec(x_11);
lean::free_heap_obj(x_5);
x_16 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_16, 0, x_3);
x_17 = lean::box(0);
x_18 = l_String_splitAux___main___closed__1;
lean::inc(x_1);
x_19 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_18, x_1, x_16, x_17, x_2, x_12, x_8);
lean::dec(x_2);
lean::dec(x_16);
x_20 = !lean::is_exclusive(x_19);
if (x_20 == 0)
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; 
x_21 = lean::cnstr_get(x_19, 0);
x_22 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_23 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_21);
x_24 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_23);
x_25 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_24);
x_26 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_25, x_1);
x_27 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_26);
lean::cnstr_set(x_19, 0, x_27);
return x_19;
}
else
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_28 = lean::cnstr_get(x_19, 0);
x_29 = lean::cnstr_get(x_19, 1);
lean::inc(x_29);
lean::inc(x_28);
lean::dec(x_19);
x_30 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_31 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_30, x_28);
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_31);
x_33 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_30, x_32);
x_34 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_33, x_1);
x_35 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_34);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_29);
return x_36;
}
}
else
{
obj* x_37; obj* x_38; obj* x_39; obj* x_40; obj* x_41; obj* x_42; 
lean::dec(x_15);
lean::dec(x_3);
lean::dec(x_2);
x_37 = l_Lean_Parser_finishCommentBlock___closed__2;
lean::cnstr_set(x_6, 2, x_37);
x_38 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_6);
x_39 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_40 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_39, x_38);
x_41 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_40, x_1);
x_42 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_41);
lean::cnstr_set(x_5, 0, x_42);
return x_5;
}
}
else
{
obj* x_43; obj* x_44; obj* x_45; obj* x_46; obj* x_47; 
x_43 = lean::cnstr_get(x_6, 0);
x_44 = lean::cnstr_get(x_6, 1);
x_45 = lean::cnstr_get(x_6, 2);
lean::inc(x_45);
lean::inc(x_44);
lean::inc(x_43);
lean::dec(x_6);
x_46 = l_Lean_Parser_stringLit;
lean::inc(x_43);
x_47 = l_Lean_Parser_tryView___at_Lean_Parser_stringLit_Parser___spec__1(x_46, x_43);
if (lean::obj_tag(x_47) == 0)
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; 
lean::dec(x_47);
lean::dec(x_43);
lean::free_heap_obj(x_5);
x_48 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_48, 0, x_3);
x_49 = lean::box(0);
x_50 = l_String_splitAux___main___closed__1;
lean::inc(x_1);
x_51 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_50, x_1, x_48, x_49, x_2, x_44, x_8);
lean::dec(x_2);
lean::dec(x_48);
x_52 = lean::cnstr_get(x_51, 0);
lean::inc(x_52);
x_53 = lean::cnstr_get(x_51, 1);
lean::inc(x_53);
if (lean::is_exclusive(x_51)) {
 lean::cnstr_release(x_51, 0);
 lean::cnstr_release(x_51, 1);
 x_54 = x_51;
} else {
 lean::dec_ref(x_51);
 x_54 = lean::box(0);
}
x_55 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_56 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_55, x_52);
x_57 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_45, x_56);
x_58 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_55, x_57);
x_59 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_58, x_1);
x_60 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_59);
if (lean::is_scalar(x_54)) {
 x_61 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_61 = x_54;
}
lean::cnstr_set(x_61, 0, x_60);
lean::cnstr_set(x_61, 1, x_53);
return x_61;
}
else
{
obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
lean::dec(x_47);
lean::dec(x_3);
lean::dec(x_2);
x_62 = l_Lean_Parser_finishCommentBlock___closed__2;
x_63 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_63, 0, x_43);
lean::cnstr_set(x_63, 1, x_44);
lean::cnstr_set(x_63, 2, x_62);
x_64 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_45, x_63);
x_65 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_66 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_65, x_64);
x_67 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_66, x_1);
x_68 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_67);
lean::cnstr_set(x_5, 0, x_68);
return x_5;
}
}
}
else
{
obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; 
x_69 = lean::cnstr_get(x_5, 1);
lean::inc(x_69);
lean::dec(x_5);
x_70 = lean::cnstr_get(x_6, 0);
lean::inc(x_70);
x_71 = lean::cnstr_get(x_6, 1);
lean::inc(x_71);
x_72 = lean::cnstr_get(x_6, 2);
lean::inc(x_72);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_73 = x_6;
} else {
 lean::dec_ref(x_6);
 x_73 = lean::box(0);
}
x_74 = l_Lean_Parser_stringLit;
lean::inc(x_70);
x_75 = l_Lean_Parser_tryView___at_Lean_Parser_stringLit_Parser___spec__1(x_74, x_70);
if (lean::obj_tag(x_75) == 0)
{
obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; obj* x_86; obj* x_87; obj* x_88; obj* x_89; 
lean::dec(x_75);
lean::dec(x_73);
lean::dec(x_70);
x_76 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_76, 0, x_3);
x_77 = lean::box(0);
x_78 = l_String_splitAux___main___closed__1;
lean::inc(x_1);
x_79 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_78, x_1, x_76, x_77, x_2, x_71, x_69);
lean::dec(x_2);
lean::dec(x_76);
x_80 = lean::cnstr_get(x_79, 0);
lean::inc(x_80);
x_81 = lean::cnstr_get(x_79, 1);
lean::inc(x_81);
if (lean::is_exclusive(x_79)) {
 lean::cnstr_release(x_79, 0);
 lean::cnstr_release(x_79, 1);
 x_82 = x_79;
} else {
 lean::dec_ref(x_79);
 x_82 = lean::box(0);
}
x_83 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_84 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_83, x_80);
x_85 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_72, x_84);
x_86 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_83, x_85);
x_87 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_86, x_1);
x_88 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_87);
if (lean::is_scalar(x_82)) {
 x_89 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_89 = x_82;
}
lean::cnstr_set(x_89, 0, x_88);
lean::cnstr_set(x_89, 1, x_81);
return x_89;
}
else
{
obj* x_90; obj* x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
lean::dec(x_75);
lean::dec(x_3);
lean::dec(x_2);
x_90 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_73)) {
 x_91 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_91 = x_73;
}
lean::cnstr_set(x_91, 0, x_70);
lean::cnstr_set(x_91, 1, x_71);
lean::cnstr_set(x_91, 2, x_90);
x_92 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_72, x_91);
x_93 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_94 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_93, x_92);
x_95 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_94, x_1);
x_96 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_95);
x_97 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_97, 0, x_96);
lean::cnstr_set(x_97, 1, x_69);
return x_97;
}
}
}
else
{
uint8 x_98; 
lean::dec(x_3);
lean::dec(x_2);
x_98 = !lean::is_exclusive(x_5);
if (x_98 == 0)
{
obj* x_99; uint8 x_100; 
x_99 = lean::cnstr_get(x_5, 0);
lean::dec(x_99);
x_100 = !lean::is_exclusive(x_6);
if (x_100 == 0)
{
obj* x_101; obj* x_102; obj* x_103; obj* x_104; 
x_101 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_102 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_101, x_6);
x_103 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_102, x_1);
x_104 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_103);
lean::cnstr_set(x_5, 0, x_104);
return x_5;
}
else
{
obj* x_105; uint8 x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; 
x_105 = lean::cnstr_get(x_6, 0);
x_106 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
lean::inc(x_105);
lean::dec(x_6);
x_107 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_107, 0, x_105);
lean::cnstr_set_scalar(x_107, sizeof(void*)*1, x_106);
x_108 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_109 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_108, x_107);
x_110 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_109, x_1);
x_111 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_110);
lean::cnstr_set(x_5, 0, x_111);
return x_5;
}
}
else
{
obj* x_112; obj* x_113; uint8 x_114; obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; 
x_112 = lean::cnstr_get(x_5, 1);
lean::inc(x_112);
lean::dec(x_5);
x_113 = lean::cnstr_get(x_6, 0);
lean::inc(x_113);
x_114 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_115 = x_6;
} else {
 lean::dec_ref(x_6);
 x_115 = lean::box(0);
}
if (lean::is_scalar(x_115)) {
 x_116 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_116 = x_115;
}
lean::cnstr_set(x_116, 0, x_113);
lean::cnstr_set_scalar(x_116, sizeof(void*)*1, x_114);
x_117 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_118 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_117, x_116);
x_119 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_118, x_1);
x_120 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_119);
x_121 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_121, 0, x_120);
lean::cnstr_set(x_121, 1, x_112);
return x_121;
}
}
}
}
obj* _init_l_Lean_Parser_stringLit_Parser___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_string("String");
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_stringLit_Parser___rarg___lambda__1), 4, 1);
lean::closure_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_Lean_Parser_stringLit_Parser___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Parser_stringLit_Parser___rarg___closed__1;
x_3 = lean::apply_2(x_1, lean::box(0), x_2);
return x_3;
}
}
obj* l_Lean_Parser_stringLit_Parser(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_stringLit_Parser___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_Parser_tryView___at_Lean_Parser_stringLit_Parser___spec__1___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_tryView___at_Lean_Parser_stringLit_Parser___spec__1(x_1, x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_stringLit_Parser___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_stringLit_Parser(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_stringLit_Parser_tokens(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
}
obj* l_Lean_Parser_stringLit_Parser_tokens___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_stringLit_Parser_tokens(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_stringLit_Parser_View___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_stringLit_HasView;
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
return x_2;
}
}
obj* _init_l_Lean_Parser_stringLit_Parser_View___rarg___closed__2() {
_start:
{
obj* x_1; obj* x_2; 
x_1 = l_Lean_Parser_stringLit_HasView;
x_2 = lean::cnstr_get(x_1, 1);
lean::inc(x_2);
return x_2;
}
}
obj* l_Lean_Parser_stringLit_Parser_View___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Parser_stringLit_Parser_View___rarg___closed__1;
x_3 = l_Lean_Parser_stringLit_Parser_View___rarg___closed__2;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_Lean_Parser_stringLit_Parser_View(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_stringLit_Parser_View___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_Parser_stringLit_Parser_View___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_stringLit_Parser_View___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_stringLit_Parser_View___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_stringLit_Parser_View(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_3) == 0)
{
obj* x_6; uint8 x_7; obj* x_8; 
x_6 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_6, 0, x_5);
lean::cnstr_set(x_6, 1, x_1);
lean::cnstr_set(x_6, 2, x_2);
lean::cnstr_set(x_6, 3, x_4);
x_7 = 0;
x_8 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set_scalar(x_8, sizeof(void*)*1, x_7);
return x_8;
}
else
{
obj* x_9; obj* x_10; uint8 x_11; obj* x_12; 
lean::dec(x_5);
x_9 = lean::cnstr_get(x_3, 0);
lean::inc(x_9);
x_10 = lean::alloc_cnstr(0, 4, 0);
lean::cnstr_set(x_10, 0, x_9);
lean::cnstr_set(x_10, 1, x_1);
lean::cnstr_set(x_10, 2, x_2);
lean::cnstr_set(x_10, 3, x_4);
x_11 = 0;
x_12 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set_scalar(x_12, sizeof(void*)*1, x_11);
return x_12;
}
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg___boxed), 5, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_stringLit_View_value___spec__2(uint32 x_1, obj* x_2) {
_start:
{
uint8 x_3; 
x_3 = l_String_OldIterator_hasNext___main(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_4 = lean::box(0);
x_5 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_5, x_6, x_4, x_4, x_2);
x_8 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_9 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_8, x_7);
return x_9;
}
else
{
uint32 x_10; uint8 x_11; 
x_10 = l_String_OldIterator_curr___main(x_2);
x_11 = x_10 == x_1;
if (x_11 == 0)
{
obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; 
x_12 = l_Char_quoteCore(x_10);
x_13 = l_Char_HasRepr___closed__1;
x_14 = lean::string_append(x_13, x_12);
lean::dec(x_12);
x_15 = lean::string_append(x_14, x_13);
x_16 = lean::box(0);
x_17 = l_mjoin___rarg___closed__1;
x_18 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_15, x_17, x_16, x_16, x_2);
x_19 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_20 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_19, x_18);
return x_20;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_21 = l_String_OldIterator_next___main(x_2);
x_22 = lean::box(0);
x_23 = lean::box_uint32(x_10);
x_24 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_24, 0, x_23);
lean::cnstr_set(x_24, 1, x_21);
lean::cnstr_set(x_24, 2, x_22);
return x_24;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_any___at_Lean_Parser_stringLit_View_value___spec__5(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_String_OldIterator_hasNext___main(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::box(0);
x_4 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_5 = l_mjoin___rarg___closed__1;
x_6 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_4, x_5, x_3, x_3, x_1);
x_7 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_8 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_7, x_6);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = l_String_OldIterator_curr___main(x_1);
x_10 = l_True_Decidable;
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_11 = l_Char_quoteCore(x_9);
x_12 = l_Char_HasRepr___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_14 = lean::string_append(x_13, x_12);
x_15 = lean::box(0);
x_16 = l_mjoin___rarg___closed__1;
x_17 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_14, x_16, x_15, x_15, x_1);
x_18 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_19 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_17);
return x_19;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_20 = l_String_OldIterator_next___main(x_1);
x_21 = lean::box(0);
x_22 = lean::box_uint32(x_9);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_20);
lean::cnstr_set(x_23, 2, x_21);
return x_23;
}
}
}
}
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_View_value___spec__7___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_4, 0, x_2);
x_5 = lean::box(0);
x_6 = l_mjoin___rarg___closed__1;
x_7 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_1, x_6, x_4, x_5, x_3);
lean::dec(x_4);
return x_7;
}
}
obj* l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_View_value___spec__7(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_View_value___spec__7___rarg), 3, 0);
return x_2;
}
}
obj* l_Lean_Parser_MonadParsec_digit___at_Lean_Parser_stringLit_View_value___spec__9(obj* x_1) {
_start:
{
uint8 x_2; 
x_2 = l_String_OldIterator_hasNext___main(x_1);
if (x_2 == 0)
{
obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_3 = lean::box(0);
x_4 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_5 = l_mjoin___rarg___closed__1;
x_6 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_4, x_5, x_3, x_3, x_1);
x_7 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_8 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_7, x_6);
return x_8;
}
else
{
uint32 x_9; uint8 x_10; 
x_9 = l_String_OldIterator_curr___main(x_1);
x_10 = l_Char_isDigit(x_9);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; 
x_11 = l_Char_quoteCore(x_9);
x_12 = l_Char_HasRepr___closed__1;
x_13 = lean::string_append(x_12, x_11);
lean::dec(x_11);
x_14 = lean::string_append(x_13, x_12);
x_15 = lean::box(0);
x_16 = l_mjoin___rarg___closed__1;
x_17 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_14, x_16, x_15, x_15, x_1);
x_18 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_19 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_17);
return x_19;
}
else
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; 
x_20 = l_String_OldIterator_next___main(x_1);
x_21 = lean::box(0);
x_22 = lean::box_uint32(x_9);
x_23 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_23, 0, x_22);
lean::cnstr_set(x_23, 1, x_20);
lean::cnstr_set(x_23, 2, x_21);
return x_23;
}
}
}
}
obj* l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_View_value___spec__8(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; uint8 x_4; obj* x_157; 
lean::inc(x_1);
x_157 = l_Lean_Parser_MonadParsec_digit___at_Lean_Parser_stringLit_View_value___spec__9(x_1);
if (lean::obj_tag(x_157) == 0)
{
uint8 x_158; 
x_158 = !lean::is_exclusive(x_157);
if (x_158 == 0)
{
obj* x_159; obj* x_160; uint32 x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; 
x_159 = lean::cnstr_get(x_157, 0);
x_160 = lean::cnstr_get(x_157, 2);
x_161 = lean::unbox_uint32(x_159);
lean::dec(x_159);
x_162 = lean::uint32_to_nat(x_161);
x_163 = l_String_foldlAux___main___at_String_toNat___spec__1___closed__1;
x_164 = lean::nat_sub(x_162, x_163);
lean::dec(x_162);
x_165 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_157, 2, x_165);
lean::cnstr_set(x_157, 0, x_164);
x_166 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_160, x_157);
if (lean::obj_tag(x_166) == 0)
{
obj* x_167; obj* x_168; 
lean::dec(x_1);
x_167 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1;
x_168 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_166, x_167);
return x_168;
}
else
{
obj* x_169; uint8 x_170; 
x_169 = lean::cnstr_get(x_166, 0);
lean::inc(x_169);
x_170 = lean::cnstr_get_scalar<uint8>(x_166, sizeof(void*)*1);
x_2 = x_166;
x_3 = x_169;
x_4 = x_170;
goto block_156;
}
}
else
{
obj* x_171; obj* x_172; obj* x_173; uint32 x_174; obj* x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; 
x_171 = lean::cnstr_get(x_157, 0);
x_172 = lean::cnstr_get(x_157, 1);
x_173 = lean::cnstr_get(x_157, 2);
lean::inc(x_173);
lean::inc(x_172);
lean::inc(x_171);
lean::dec(x_157);
x_174 = lean::unbox_uint32(x_171);
lean::dec(x_171);
x_175 = lean::uint32_to_nat(x_174);
x_176 = l_String_foldlAux___main___at_String_toNat___spec__1___closed__1;
x_177 = lean::nat_sub(x_175, x_176);
lean::dec(x_175);
x_178 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_179 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_179, 0, x_177);
lean::cnstr_set(x_179, 1, x_172);
lean::cnstr_set(x_179, 2, x_178);
x_180 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_173, x_179);
if (lean::obj_tag(x_180) == 0)
{
obj* x_181; obj* x_182; 
lean::dec(x_1);
x_181 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1;
x_182 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_180, x_181);
return x_182;
}
else
{
obj* x_183; uint8 x_184; 
x_183 = lean::cnstr_get(x_180, 0);
lean::inc(x_183);
x_184 = lean::cnstr_get_scalar<uint8>(x_180, sizeof(void*)*1);
x_2 = x_180;
x_3 = x_183;
x_4 = x_184;
goto block_156;
}
}
}
else
{
uint8 x_185; 
x_185 = !lean::is_exclusive(x_157);
if (x_185 == 0)
{
obj* x_186; uint8 x_187; 
x_186 = lean::cnstr_get(x_157, 0);
x_187 = lean::cnstr_get_scalar<uint8>(x_157, sizeof(void*)*1);
lean::inc(x_186);
x_2 = x_157;
x_3 = x_186;
x_4 = x_187;
goto block_156;
}
else
{
obj* x_188; uint8 x_189; obj* x_190; 
x_188 = lean::cnstr_get(x_157, 0);
x_189 = lean::cnstr_get_scalar<uint8>(x_157, sizeof(void*)*1);
lean::inc(x_188);
lean::dec(x_157);
lean::inc(x_188);
x_190 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_190, 0, x_188);
lean::cnstr_set_scalar(x_190, sizeof(void*)*1, x_189);
x_2 = x_190;
x_3 = x_188;
x_4 = x_189;
goto block_156;
}
}
block_156:
{
obj* x_5; obj* x_6; uint8 x_7; 
if (x_4 == 0)
{
obj* x_85; uint8 x_126; 
lean::dec(x_2);
x_126 = l_String_OldIterator_hasNext___main(x_1);
if (x_126 == 0)
{
obj* x_127; obj* x_128; obj* x_129; obj* x_130; 
x_127 = lean::box(0);
x_128 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_129 = l_mjoin___rarg___closed__1;
lean::inc(x_1);
x_130 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_128, x_129, x_127, x_127, x_1);
x_85 = x_130;
goto block_125;
}
else
{
uint32 x_131; uint32 x_132; uint8 x_133; 
x_131 = l_String_OldIterator_curr___main(x_1);
x_132 = 97;
x_133 = x_132 <= x_131;
if (x_133 == 0)
{
obj* x_134; obj* x_135; obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; 
x_134 = l_Char_quoteCore(x_131);
x_135 = l_Char_HasRepr___closed__1;
x_136 = lean::string_append(x_135, x_134);
lean::dec(x_134);
x_137 = lean::string_append(x_136, x_135);
x_138 = lean::box(0);
x_139 = l_mjoin___rarg___closed__1;
lean::inc(x_1);
x_140 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_137, x_139, x_138, x_138, x_1);
x_85 = x_140;
goto block_125;
}
else
{
uint32 x_141; uint8 x_142; 
x_141 = 102;
x_142 = x_131 <= x_141;
if (x_142 == 0)
{
obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; obj* x_149; 
x_143 = l_Char_quoteCore(x_131);
x_144 = l_Char_HasRepr___closed__1;
x_145 = lean::string_append(x_144, x_143);
lean::dec(x_143);
x_146 = lean::string_append(x_145, x_144);
x_147 = lean::box(0);
x_148 = l_mjoin___rarg___closed__1;
lean::inc(x_1);
x_149 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_146, x_148, x_147, x_147, x_1);
x_85 = x_149;
goto block_125;
}
else
{
obj* x_150; obj* x_151; obj* x_152; obj* x_153; 
lean::inc(x_1);
x_150 = l_String_OldIterator_next___main(x_1);
x_151 = lean::box(0);
x_152 = lean::box_uint32(x_131);
x_153 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_153, 0, x_152);
lean::cnstr_set(x_153, 1, x_150);
lean::cnstr_set(x_153, 2, x_151);
x_85 = x_153;
goto block_125;
}
}
}
block_125:
{
obj* x_86; obj* x_87; 
x_86 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_87 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_86, x_85);
if (lean::obj_tag(x_87) == 0)
{
uint8 x_88; 
x_88 = !lean::is_exclusive(x_87);
if (x_88 == 0)
{
obj* x_89; obj* x_90; uint32 x_91; obj* x_92; obj* x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; 
x_89 = lean::cnstr_get(x_87, 0);
x_90 = lean::cnstr_get(x_87, 2);
x_91 = lean::unbox_uint32(x_89);
lean::dec(x_89);
x_92 = lean::uint32_to_nat(x_91);
x_93 = l_Lean_Parser_parseHexDigit___rarg___lambda__3___closed__1;
x_94 = lean::nat_sub(x_92, x_93);
lean::dec(x_92);
x_95 = lean::mk_nat_obj(10u);
x_96 = lean::nat_add(x_95, x_94);
lean::dec(x_94);
lean::cnstr_set(x_87, 2, x_86);
lean::cnstr_set(x_87, 0, x_96);
x_97 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_90, x_87);
if (lean::obj_tag(x_97) == 0)
{
obj* x_98; obj* x_99; obj* x_100; 
lean::dec(x_1);
x_98 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_3, x_97);
x_99 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1;
x_100 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_98, x_99);
return x_100;
}
else
{
obj* x_101; uint8 x_102; 
x_101 = lean::cnstr_get(x_97, 0);
lean::inc(x_101);
x_102 = lean::cnstr_get_scalar<uint8>(x_97, sizeof(void*)*1);
x_5 = x_97;
x_6 = x_101;
x_7 = x_102;
goto block_84;
}
}
else
{
obj* x_103; obj* x_104; obj* x_105; uint32 x_106; obj* x_107; obj* x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; 
x_103 = lean::cnstr_get(x_87, 0);
x_104 = lean::cnstr_get(x_87, 1);
x_105 = lean::cnstr_get(x_87, 2);
lean::inc(x_105);
lean::inc(x_104);
lean::inc(x_103);
lean::dec(x_87);
x_106 = lean::unbox_uint32(x_103);
lean::dec(x_103);
x_107 = lean::uint32_to_nat(x_106);
x_108 = l_Lean_Parser_parseHexDigit___rarg___lambda__3___closed__1;
x_109 = lean::nat_sub(x_107, x_108);
lean::dec(x_107);
x_110 = lean::mk_nat_obj(10u);
x_111 = lean::nat_add(x_110, x_109);
lean::dec(x_109);
x_112 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_112, 0, x_111);
lean::cnstr_set(x_112, 1, x_104);
lean::cnstr_set(x_112, 2, x_86);
x_113 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_105, x_112);
if (lean::obj_tag(x_113) == 0)
{
obj* x_114; obj* x_115; obj* x_116; 
lean::dec(x_1);
x_114 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_3, x_113);
x_115 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1;
x_116 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_114, x_115);
return x_116;
}
else
{
obj* x_117; uint8 x_118; 
x_117 = lean::cnstr_get(x_113, 0);
lean::inc(x_117);
x_118 = lean::cnstr_get_scalar<uint8>(x_113, sizeof(void*)*1);
x_5 = x_113;
x_6 = x_117;
x_7 = x_118;
goto block_84;
}
}
}
else
{
uint8 x_119; 
x_119 = !lean::is_exclusive(x_87);
if (x_119 == 0)
{
obj* x_120; uint8 x_121; 
x_120 = lean::cnstr_get(x_87, 0);
x_121 = lean::cnstr_get_scalar<uint8>(x_87, sizeof(void*)*1);
lean::inc(x_120);
x_5 = x_87;
x_6 = x_120;
x_7 = x_121;
goto block_84;
}
else
{
obj* x_122; uint8 x_123; obj* x_124; 
x_122 = lean::cnstr_get(x_87, 0);
x_123 = lean::cnstr_get_scalar<uint8>(x_87, sizeof(void*)*1);
lean::inc(x_122);
lean::dec(x_87);
lean::inc(x_122);
x_124 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_124, 0, x_122);
lean::cnstr_set_scalar(x_124, sizeof(void*)*1, x_123);
x_5 = x_124;
x_6 = x_122;
x_7 = x_123;
goto block_84;
}
}
}
}
else
{
obj* x_154; obj* x_155; 
lean::dec(x_3);
lean::dec(x_1);
x_154 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1;
x_155 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_2, x_154);
return x_155;
}
block_84:
{
if (x_7 == 0)
{
obj* x_8; uint8 x_53; 
lean::dec(x_5);
x_53 = l_String_OldIterator_hasNext___main(x_1);
if (x_53 == 0)
{
obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_54 = lean::box(0);
x_55 = l_Lean_Parser_MonadParsec_eoiError___rarg___closed__1;
x_56 = l_mjoin___rarg___closed__1;
x_57 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_55, x_56, x_54, x_54, x_1);
x_8 = x_57;
goto block_52;
}
else
{
uint32 x_58; uint32 x_59; uint8 x_60; 
x_58 = l_String_OldIterator_curr___main(x_1);
x_59 = 65;
x_60 = x_59 <= x_58;
if (x_60 == 0)
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; obj* x_65; obj* x_66; obj* x_67; 
x_61 = l_Char_quoteCore(x_58);
x_62 = l_Char_HasRepr___closed__1;
x_63 = lean::string_append(x_62, x_61);
lean::dec(x_61);
x_64 = lean::string_append(x_63, x_62);
x_65 = lean::box(0);
x_66 = l_mjoin___rarg___closed__1;
x_67 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_64, x_66, x_65, x_65, x_1);
x_8 = x_67;
goto block_52;
}
else
{
uint32 x_68; uint8 x_69; 
x_68 = 70;
x_69 = x_58 <= x_68;
if (x_69 == 0)
{
obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_70 = l_Char_quoteCore(x_58);
x_71 = l_Char_HasRepr___closed__1;
x_72 = lean::string_append(x_71, x_70);
lean::dec(x_70);
x_73 = lean::string_append(x_72, x_71);
x_74 = lean::box(0);
x_75 = l_mjoin___rarg___closed__1;
x_76 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_73, x_75, x_74, x_74, x_1);
x_8 = x_76;
goto block_52;
}
else
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_77 = l_String_OldIterator_next___main(x_1);
x_78 = lean::box(0);
x_79 = lean::box_uint32(x_58);
x_80 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_77);
lean::cnstr_set(x_80, 2, x_78);
x_8 = x_80;
goto block_52;
}
}
}
block_52:
{
obj* x_9; obj* x_10; 
x_9 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_10 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_8);
if (lean::obj_tag(x_10) == 0)
{
uint8 x_11; 
x_11 = !lean::is_exclusive(x_10);
if (x_11 == 0)
{
obj* x_12; obj* x_13; uint32 x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; 
x_12 = lean::cnstr_get(x_10, 0);
x_13 = lean::cnstr_get(x_10, 2);
x_14 = lean::unbox_uint32(x_12);
lean::dec(x_12);
x_15 = lean::uint32_to_nat(x_14);
x_16 = l_Lean_Parser_parseHexDigit___rarg___lambda__5___closed__1;
x_17 = lean::nat_sub(x_15, x_16);
lean::dec(x_15);
x_18 = lean::mk_nat_obj(10u);
x_19 = lean::nat_add(x_18, x_17);
lean::dec(x_17);
lean::cnstr_set(x_10, 2, x_9);
lean::cnstr_set(x_10, 0, x_19);
x_20 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_10);
x_21 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_6, x_20);
x_22 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_3, x_21);
x_23 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1;
x_24 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_22, x_23);
return x_24;
}
else
{
obj* x_25; obj* x_26; obj* x_27; uint32 x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
x_25 = lean::cnstr_get(x_10, 0);
x_26 = lean::cnstr_get(x_10, 1);
x_27 = lean::cnstr_get(x_10, 2);
lean::inc(x_27);
lean::inc(x_26);
lean::inc(x_25);
lean::dec(x_10);
x_28 = lean::unbox_uint32(x_25);
lean::dec(x_25);
x_29 = lean::uint32_to_nat(x_28);
x_30 = l_Lean_Parser_parseHexDigit___rarg___lambda__5___closed__1;
x_31 = lean::nat_sub(x_29, x_30);
lean::dec(x_29);
x_32 = lean::mk_nat_obj(10u);
x_33 = lean::nat_add(x_32, x_31);
lean::dec(x_31);
x_34 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_34, 0, x_33);
lean::cnstr_set(x_34, 1, x_26);
lean::cnstr_set(x_34, 2, x_9);
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_27, x_34);
x_36 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_6, x_35);
x_37 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_3, x_36);
x_38 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1;
x_39 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_37, x_38);
return x_39;
}
}
else
{
uint8 x_40; 
x_40 = !lean::is_exclusive(x_10);
if (x_40 == 0)
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_41 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_6, x_10);
x_42 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_3, x_41);
x_43 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1;
x_44 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_42, x_43);
return x_44;
}
else
{
obj* x_45; uint8 x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; 
x_45 = lean::cnstr_get(x_10, 0);
x_46 = lean::cnstr_get_scalar<uint8>(x_10, sizeof(void*)*1);
lean::inc(x_45);
lean::dec(x_10);
x_47 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_47, 0, x_45);
lean::cnstr_set_scalar(x_47, sizeof(void*)*1, x_46);
x_48 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_6, x_47);
x_49 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_3, x_48);
x_50 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1;
x_51 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_49, x_50);
return x_51;
}
}
}
}
else
{
obj* x_81; obj* x_82; obj* x_83; 
lean::dec(x_6);
lean::dec(x_1);
x_81 = l_Lean_Parser_ParsecT_orelseMkRes___rarg(x_3, x_5);
x_82 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1;
x_83 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_81, x_82);
return x_83;
}
}
}
}
}
obj* l_Lean_Parser_parseQuotedChar___at_Lean_Parser_stringLit_View_value___spec__6(obj* x_1) {
_start:
{
obj* x_2; 
lean::inc(x_1);
x_2 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_stringLit_View_value___spec__5(x_1);
if (lean::obj_tag(x_2) == 0)
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_2);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; uint32 x_7; uint32 x_8; uint8 x_9; 
x_4 = lean::cnstr_get(x_2, 0);
x_5 = lean::cnstr_get(x_2, 1);
x_6 = lean::cnstr_get(x_2, 2);
x_7 = 92;
x_8 = lean::unbox_uint32(x_4);
x_9 = x_8 == x_7;
if (x_9 == 0)
{
uint32 x_10; uint32 x_11; uint8 x_12; 
x_10 = 34;
x_11 = lean::unbox_uint32(x_4);
x_12 = x_11 == x_10;
if (x_12 == 0)
{
uint32 x_13; uint32 x_14; uint8 x_15; 
x_13 = 39;
x_14 = lean::unbox_uint32(x_4);
x_15 = x_14 == x_13;
if (x_15 == 0)
{
uint32 x_16; uint32 x_17; uint8 x_18; 
x_16 = 110;
x_17 = lean::unbox_uint32(x_4);
x_18 = x_17 == x_16;
if (x_18 == 0)
{
uint32 x_19; uint32 x_20; uint8 x_21; 
x_19 = 116;
x_20 = lean::unbox_uint32(x_4);
x_21 = x_20 == x_19;
if (x_21 == 0)
{
uint32 x_22; uint32 x_23; uint8 x_24; 
lean::free_heap_obj(x_2);
x_22 = 120;
x_23 = lean::unbox_uint32(x_4);
x_24 = x_23 == x_22;
if (x_24 == 0)
{
uint32 x_25; uint32 x_26; uint8 x_27; 
x_25 = 117;
x_26 = lean::unbox_uint32(x_4);
lean::dec(x_4);
x_27 = x_26 == x_25;
if (x_27 == 0)
{
obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; 
x_28 = l_Lean_Parser_parseQuotedChar___rarg___lambda__7___closed__1;
x_29 = l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_View_value___spec__7___rarg(x_28, x_1, x_5);
x_30 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_29);
x_31 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_31, x_30);
return x_32;
}
else
{
obj* x_33; 
lean::dec(x_1);
x_33 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_View_value___spec__8(x_5);
if (lean::obj_tag(x_33) == 0)
{
obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_34 = lean::cnstr_get(x_33, 0);
lean::inc(x_34);
x_35 = lean::cnstr_get(x_33, 1);
lean::inc(x_35);
x_36 = lean::cnstr_get(x_33, 2);
lean::inc(x_36);
lean::dec(x_33);
x_37 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_View_value___spec__8(x_35);
if (lean::obj_tag(x_37) == 0)
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; 
x_38 = lean::cnstr_get(x_37, 0);
lean::inc(x_38);
x_39 = lean::cnstr_get(x_37, 1);
lean::inc(x_39);
x_40 = lean::cnstr_get(x_37, 2);
lean::inc(x_40);
lean::dec(x_37);
x_41 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_View_value___spec__8(x_39);
if (lean::obj_tag(x_41) == 0)
{
obj* x_42; obj* x_43; obj* x_44; obj* x_45; 
x_42 = lean::cnstr_get(x_41, 0);
lean::inc(x_42);
x_43 = lean::cnstr_get(x_41, 1);
lean::inc(x_43);
x_44 = lean::cnstr_get(x_41, 2);
lean::inc(x_44);
lean::dec(x_41);
x_45 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_View_value___spec__8(x_43);
if (lean::obj_tag(x_45) == 0)
{
uint8 x_46; 
x_46 = !lean::is_exclusive(x_45);
if (x_46 == 0)
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; uint32 x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_47 = lean::cnstr_get(x_45, 0);
x_48 = lean::cnstr_get(x_45, 2);
x_49 = lean::mk_nat_obj(16u);
x_50 = lean::nat_mul(x_49, x_34);
lean::dec(x_34);
x_51 = lean::nat_add(x_50, x_38);
lean::dec(x_38);
lean::dec(x_50);
x_52 = lean::nat_mul(x_49, x_51);
lean::dec(x_51);
x_53 = lean::nat_add(x_52, x_42);
lean::dec(x_42);
lean::dec(x_52);
x_54 = lean::nat_mul(x_49, x_53);
lean::dec(x_53);
x_55 = lean::nat_add(x_54, x_47);
lean::dec(x_47);
lean::dec(x_54);
x_56 = l_Char_ofNat(x_55);
lean::dec(x_55);
x_57 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_58 = lean::box_uint32(x_56);
lean::cnstr_set(x_45, 2, x_57);
lean::cnstr_set(x_45, 0, x_58);
x_59 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_48, x_45);
x_60 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_44, x_59);
x_61 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_40, x_60);
x_62 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_36, x_61);
x_63 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_62);
x_64 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_57, x_63);
return x_64;
}
else
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; uint32 x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_65 = lean::cnstr_get(x_45, 0);
x_66 = lean::cnstr_get(x_45, 1);
x_67 = lean::cnstr_get(x_45, 2);
lean::inc(x_67);
lean::inc(x_66);
lean::inc(x_65);
lean::dec(x_45);
x_68 = lean::mk_nat_obj(16u);
x_69 = lean::nat_mul(x_68, x_34);
lean::dec(x_34);
x_70 = lean::nat_add(x_69, x_38);
lean::dec(x_38);
lean::dec(x_69);
x_71 = lean::nat_mul(x_68, x_70);
lean::dec(x_70);
x_72 = lean::nat_add(x_71, x_42);
lean::dec(x_42);
lean::dec(x_71);
x_73 = lean::nat_mul(x_68, x_72);
lean::dec(x_72);
x_74 = lean::nat_add(x_73, x_65);
lean::dec(x_65);
lean::dec(x_73);
x_75 = l_Char_ofNat(x_74);
lean::dec(x_74);
x_76 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_77 = lean::box_uint32(x_75);
x_78 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_78, 0, x_77);
lean::cnstr_set(x_78, 1, x_66);
lean::cnstr_set(x_78, 2, x_76);
x_79 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_67, x_78);
x_80 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_44, x_79);
x_81 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_40, x_80);
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_36, x_81);
x_83 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_82);
x_84 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_76, x_83);
return x_84;
}
}
else
{
uint8 x_85; 
lean::dec(x_42);
lean::dec(x_38);
lean::dec(x_34);
x_85 = !lean::is_exclusive(x_45);
if (x_85 == 0)
{
obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; 
x_86 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_44, x_45);
x_87 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_40, x_86);
x_88 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_36, x_87);
x_89 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_88);
x_90 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_91 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_90, x_89);
return x_91;
}
else
{
obj* x_92; uint8 x_93; obj* x_94; obj* x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_92 = lean::cnstr_get(x_45, 0);
x_93 = lean::cnstr_get_scalar<uint8>(x_45, sizeof(void*)*1);
lean::inc(x_92);
lean::dec(x_45);
x_94 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_94, 0, x_92);
lean::cnstr_set_scalar(x_94, sizeof(void*)*1, x_93);
x_95 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_44, x_94);
x_96 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_40, x_95);
x_97 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_36, x_96);
x_98 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_97);
x_99 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_100 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_99, x_98);
return x_100;
}
}
}
else
{
uint8 x_101; 
lean::dec(x_38);
lean::dec(x_34);
x_101 = !lean::is_exclusive(x_41);
if (x_101 == 0)
{
obj* x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; 
x_102 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_40, x_41);
x_103 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_36, x_102);
x_104 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_103);
x_105 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_106 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_105, x_104);
return x_106;
}
else
{
obj* x_107; uint8 x_108; obj* x_109; obj* x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
x_107 = lean::cnstr_get(x_41, 0);
x_108 = lean::cnstr_get_scalar<uint8>(x_41, sizeof(void*)*1);
lean::inc(x_107);
lean::dec(x_41);
x_109 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_109, 0, x_107);
lean::cnstr_set_scalar(x_109, sizeof(void*)*1, x_108);
x_110 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_40, x_109);
x_111 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_36, x_110);
x_112 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_111);
x_113 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_114 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_113, x_112);
return x_114;
}
}
}
else
{
uint8 x_115; 
lean::dec(x_34);
x_115 = !lean::is_exclusive(x_37);
if (x_115 == 0)
{
obj* x_116; obj* x_117; obj* x_118; obj* x_119; 
x_116 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_36, x_37);
x_117 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_116);
x_118 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_119 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_118, x_117);
return x_119;
}
else
{
obj* x_120; uint8 x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; 
x_120 = lean::cnstr_get(x_37, 0);
x_121 = lean::cnstr_get_scalar<uint8>(x_37, sizeof(void*)*1);
lean::inc(x_120);
lean::dec(x_37);
x_122 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_122, 0, x_120);
lean::cnstr_set_scalar(x_122, sizeof(void*)*1, x_121);
x_123 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_36, x_122);
x_124 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_123);
x_125 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_126 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_125, x_124);
return x_126;
}
}
}
else
{
uint8 x_127; 
x_127 = !lean::is_exclusive(x_33);
if (x_127 == 0)
{
obj* x_128; obj* x_129; obj* x_130; 
x_128 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_33);
x_129 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_130 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_129, x_128);
return x_130;
}
else
{
obj* x_131; uint8 x_132; obj* x_133; obj* x_134; obj* x_135; obj* x_136; 
x_131 = lean::cnstr_get(x_33, 0);
x_132 = lean::cnstr_get_scalar<uint8>(x_33, sizeof(void*)*1);
lean::inc(x_131);
lean::dec(x_33);
x_133 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_133, 0, x_131);
lean::cnstr_set_scalar(x_133, sizeof(void*)*1, x_132);
x_134 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_133);
x_135 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_136 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_135, x_134);
return x_136;
}
}
}
}
else
{
obj* x_137; 
lean::dec(x_4);
lean::dec(x_1);
x_137 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_View_value___spec__8(x_5);
if (lean::obj_tag(x_137) == 0)
{
obj* x_138; obj* x_139; obj* x_140; obj* x_141; 
x_138 = lean::cnstr_get(x_137, 0);
lean::inc(x_138);
x_139 = lean::cnstr_get(x_137, 1);
lean::inc(x_139);
x_140 = lean::cnstr_get(x_137, 2);
lean::inc(x_140);
lean::dec(x_137);
x_141 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_View_value___spec__8(x_139);
if (lean::obj_tag(x_141) == 0)
{
uint8 x_142; 
x_142 = !lean::is_exclusive(x_141);
if (x_142 == 0)
{
obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; uint32 x_148; obj* x_149; obj* x_150; obj* x_151; obj* x_152; obj* x_153; obj* x_154; 
x_143 = lean::cnstr_get(x_141, 0);
x_144 = lean::cnstr_get(x_141, 2);
x_145 = lean::mk_nat_obj(16u);
x_146 = lean::nat_mul(x_145, x_138);
lean::dec(x_138);
x_147 = lean::nat_add(x_146, x_143);
lean::dec(x_143);
lean::dec(x_146);
x_148 = l_Char_ofNat(x_147);
lean::dec(x_147);
x_149 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_150 = lean::box_uint32(x_148);
lean::cnstr_set(x_141, 2, x_149);
lean::cnstr_set(x_141, 0, x_150);
x_151 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_144, x_141);
x_152 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_140, x_151);
x_153 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_152);
x_154 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_149, x_153);
return x_154;
}
else
{
obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; uint32 x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; obj* x_168; 
x_155 = lean::cnstr_get(x_141, 0);
x_156 = lean::cnstr_get(x_141, 1);
x_157 = lean::cnstr_get(x_141, 2);
lean::inc(x_157);
lean::inc(x_156);
lean::inc(x_155);
lean::dec(x_141);
x_158 = lean::mk_nat_obj(16u);
x_159 = lean::nat_mul(x_158, x_138);
lean::dec(x_138);
x_160 = lean::nat_add(x_159, x_155);
lean::dec(x_155);
lean::dec(x_159);
x_161 = l_Char_ofNat(x_160);
lean::dec(x_160);
x_162 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_163 = lean::box_uint32(x_161);
x_164 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_164, 0, x_163);
lean::cnstr_set(x_164, 1, x_156);
lean::cnstr_set(x_164, 2, x_162);
x_165 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_157, x_164);
x_166 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_140, x_165);
x_167 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_166);
x_168 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_162, x_167);
return x_168;
}
}
else
{
uint8 x_169; 
lean::dec(x_138);
x_169 = !lean::is_exclusive(x_141);
if (x_169 == 0)
{
obj* x_170; obj* x_171; obj* x_172; obj* x_173; 
x_170 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_140, x_141);
x_171 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_170);
x_172 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_173 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_172, x_171);
return x_173;
}
else
{
obj* x_174; uint8 x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; 
x_174 = lean::cnstr_get(x_141, 0);
x_175 = lean::cnstr_get_scalar<uint8>(x_141, sizeof(void*)*1);
lean::inc(x_174);
lean::dec(x_141);
x_176 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_176, 0, x_174);
lean::cnstr_set_scalar(x_176, sizeof(void*)*1, x_175);
x_177 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_140, x_176);
x_178 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_177);
x_179 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_180 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_179, x_178);
return x_180;
}
}
}
else
{
uint8 x_181; 
x_181 = !lean::is_exclusive(x_137);
if (x_181 == 0)
{
obj* x_182; obj* x_183; obj* x_184; 
x_182 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_137);
x_183 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_184 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_183, x_182);
return x_184;
}
else
{
obj* x_185; uint8 x_186; obj* x_187; obj* x_188; obj* x_189; obj* x_190; 
x_185 = lean::cnstr_get(x_137, 0);
x_186 = lean::cnstr_get_scalar<uint8>(x_137, sizeof(void*)*1);
lean::inc(x_185);
lean::dec(x_137);
x_187 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_187, 0, x_185);
lean::cnstr_set_scalar(x_187, sizeof(void*)*1, x_186);
x_188 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_187);
x_189 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_190 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_189, x_188);
return x_190;
}
}
}
}
else
{
uint32 x_191; obj* x_192; obj* x_193; obj* x_194; obj* x_195; 
lean::dec(x_4);
lean::dec(x_1);
x_191 = 9;
x_192 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_193 = lean::box_uint32(x_191);
lean::cnstr_set(x_2, 2, x_192);
lean::cnstr_set(x_2, 0, x_193);
x_194 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_2);
x_195 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_192, x_194);
return x_195;
}
}
else
{
uint32 x_196; obj* x_197; obj* x_198; obj* x_199; obj* x_200; 
lean::dec(x_4);
lean::dec(x_1);
x_196 = 10;
x_197 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_198 = lean::box_uint32(x_196);
lean::cnstr_set(x_2, 2, x_197);
lean::cnstr_set(x_2, 0, x_198);
x_199 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_2);
x_200 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_197, x_199);
return x_200;
}
}
else
{
obj* x_201; obj* x_202; obj* x_203; obj* x_204; 
lean::dec(x_4);
lean::dec(x_1);
x_201 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_202 = lean::box_uint32(x_13);
lean::cnstr_set(x_2, 2, x_201);
lean::cnstr_set(x_2, 0, x_202);
x_203 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_2);
x_204 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_201, x_203);
return x_204;
}
}
else
{
obj* x_205; obj* x_206; obj* x_207; obj* x_208; 
lean::dec(x_4);
lean::dec(x_1);
x_205 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_206 = lean::box_uint32(x_10);
lean::cnstr_set(x_2, 2, x_205);
lean::cnstr_set(x_2, 0, x_206);
x_207 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_2);
x_208 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_205, x_207);
return x_208;
}
}
else
{
obj* x_209; obj* x_210; obj* x_211; obj* x_212; 
lean::dec(x_4);
lean::dec(x_1);
x_209 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_210 = lean::box_uint32(x_7);
lean::cnstr_set(x_2, 2, x_209);
lean::cnstr_set(x_2, 0, x_210);
x_211 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_6, x_2);
x_212 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_209, x_211);
return x_212;
}
}
else
{
obj* x_213; obj* x_214; obj* x_215; uint32 x_216; uint32 x_217; uint8 x_218; 
x_213 = lean::cnstr_get(x_2, 0);
x_214 = lean::cnstr_get(x_2, 1);
x_215 = lean::cnstr_get(x_2, 2);
lean::inc(x_215);
lean::inc(x_214);
lean::inc(x_213);
lean::dec(x_2);
x_216 = 92;
x_217 = lean::unbox_uint32(x_213);
x_218 = x_217 == x_216;
if (x_218 == 0)
{
uint32 x_219; uint32 x_220; uint8 x_221; 
x_219 = 34;
x_220 = lean::unbox_uint32(x_213);
x_221 = x_220 == x_219;
if (x_221 == 0)
{
uint32 x_222; uint32 x_223; uint8 x_224; 
x_222 = 39;
x_223 = lean::unbox_uint32(x_213);
x_224 = x_223 == x_222;
if (x_224 == 0)
{
uint32 x_225; uint32 x_226; uint8 x_227; 
x_225 = 110;
x_226 = lean::unbox_uint32(x_213);
x_227 = x_226 == x_225;
if (x_227 == 0)
{
uint32 x_228; uint32 x_229; uint8 x_230; 
x_228 = 116;
x_229 = lean::unbox_uint32(x_213);
x_230 = x_229 == x_228;
if (x_230 == 0)
{
uint32 x_231; uint32 x_232; uint8 x_233; 
x_231 = 120;
x_232 = lean::unbox_uint32(x_213);
x_233 = x_232 == x_231;
if (x_233 == 0)
{
uint32 x_234; uint32 x_235; uint8 x_236; 
x_234 = 117;
x_235 = lean::unbox_uint32(x_213);
lean::dec(x_213);
x_236 = x_235 == x_234;
if (x_236 == 0)
{
obj* x_237; obj* x_238; obj* x_239; obj* x_240; obj* x_241; 
x_237 = l_Lean_Parser_parseQuotedChar___rarg___lambda__7___closed__1;
x_238 = l_Lean_Parser_MonadParsec_unexpectedAt___at_Lean_Parser_stringLit_View_value___spec__7___rarg(x_237, x_1, x_214);
x_239 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_215, x_238);
x_240 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_241 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_240, x_239);
return x_241;
}
else
{
obj* x_242; 
lean::dec(x_1);
x_242 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_View_value___spec__8(x_214);
if (lean::obj_tag(x_242) == 0)
{
obj* x_243; obj* x_244; obj* x_245; obj* x_246; 
x_243 = lean::cnstr_get(x_242, 0);
lean::inc(x_243);
x_244 = lean::cnstr_get(x_242, 1);
lean::inc(x_244);
x_245 = lean::cnstr_get(x_242, 2);
lean::inc(x_245);
lean::dec(x_242);
x_246 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_View_value___spec__8(x_244);
if (lean::obj_tag(x_246) == 0)
{
obj* x_247; obj* x_248; obj* x_249; obj* x_250; 
x_247 = lean::cnstr_get(x_246, 0);
lean::inc(x_247);
x_248 = lean::cnstr_get(x_246, 1);
lean::inc(x_248);
x_249 = lean::cnstr_get(x_246, 2);
lean::inc(x_249);
lean::dec(x_246);
x_250 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_View_value___spec__8(x_248);
if (lean::obj_tag(x_250) == 0)
{
obj* x_251; obj* x_252; obj* x_253; obj* x_254; 
x_251 = lean::cnstr_get(x_250, 0);
lean::inc(x_251);
x_252 = lean::cnstr_get(x_250, 1);
lean::inc(x_252);
x_253 = lean::cnstr_get(x_250, 2);
lean::inc(x_253);
lean::dec(x_250);
x_254 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_View_value___spec__8(x_252);
if (lean::obj_tag(x_254) == 0)
{
obj* x_255; obj* x_256; obj* x_257; obj* x_258; obj* x_259; obj* x_260; obj* x_261; obj* x_262; obj* x_263; obj* x_264; obj* x_265; uint32 x_266; obj* x_267; obj* x_268; obj* x_269; obj* x_270; obj* x_271; obj* x_272; obj* x_273; obj* x_274; obj* x_275; 
x_255 = lean::cnstr_get(x_254, 0);
lean::inc(x_255);
x_256 = lean::cnstr_get(x_254, 1);
lean::inc(x_256);
x_257 = lean::cnstr_get(x_254, 2);
lean::inc(x_257);
if (lean::is_exclusive(x_254)) {
 lean::cnstr_release(x_254, 0);
 lean::cnstr_release(x_254, 1);
 lean::cnstr_release(x_254, 2);
 x_258 = x_254;
} else {
 lean::dec_ref(x_254);
 x_258 = lean::box(0);
}
x_259 = lean::mk_nat_obj(16u);
x_260 = lean::nat_mul(x_259, x_243);
lean::dec(x_243);
x_261 = lean::nat_add(x_260, x_247);
lean::dec(x_247);
lean::dec(x_260);
x_262 = lean::nat_mul(x_259, x_261);
lean::dec(x_261);
x_263 = lean::nat_add(x_262, x_251);
lean::dec(x_251);
lean::dec(x_262);
x_264 = lean::nat_mul(x_259, x_263);
lean::dec(x_263);
x_265 = lean::nat_add(x_264, x_255);
lean::dec(x_255);
lean::dec(x_264);
x_266 = l_Char_ofNat(x_265);
lean::dec(x_265);
x_267 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_268 = lean::box_uint32(x_266);
if (lean::is_scalar(x_258)) {
 x_269 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_269 = x_258;
}
lean::cnstr_set(x_269, 0, x_268);
lean::cnstr_set(x_269, 1, x_256);
lean::cnstr_set(x_269, 2, x_267);
x_270 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_257, x_269);
x_271 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_253, x_270);
x_272 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_249, x_271);
x_273 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_245, x_272);
x_274 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_215, x_273);
x_275 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_267, x_274);
return x_275;
}
else
{
obj* x_276; uint8 x_277; obj* x_278; obj* x_279; obj* x_280; obj* x_281; obj* x_282; obj* x_283; obj* x_284; obj* x_285; 
lean::dec(x_251);
lean::dec(x_247);
lean::dec(x_243);
x_276 = lean::cnstr_get(x_254, 0);
lean::inc(x_276);
x_277 = lean::cnstr_get_scalar<uint8>(x_254, sizeof(void*)*1);
if (lean::is_exclusive(x_254)) {
 lean::cnstr_release(x_254, 0);
 x_278 = x_254;
} else {
 lean::dec_ref(x_254);
 x_278 = lean::box(0);
}
if (lean::is_scalar(x_278)) {
 x_279 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_279 = x_278;
}
lean::cnstr_set(x_279, 0, x_276);
lean::cnstr_set_scalar(x_279, sizeof(void*)*1, x_277);
x_280 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_253, x_279);
x_281 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_249, x_280);
x_282 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_245, x_281);
x_283 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_215, x_282);
x_284 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_285 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_284, x_283);
return x_285;
}
}
else
{
obj* x_286; uint8 x_287; obj* x_288; obj* x_289; obj* x_290; obj* x_291; obj* x_292; obj* x_293; obj* x_294; 
lean::dec(x_247);
lean::dec(x_243);
x_286 = lean::cnstr_get(x_250, 0);
lean::inc(x_286);
x_287 = lean::cnstr_get_scalar<uint8>(x_250, sizeof(void*)*1);
if (lean::is_exclusive(x_250)) {
 lean::cnstr_release(x_250, 0);
 x_288 = x_250;
} else {
 lean::dec_ref(x_250);
 x_288 = lean::box(0);
}
if (lean::is_scalar(x_288)) {
 x_289 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_289 = x_288;
}
lean::cnstr_set(x_289, 0, x_286);
lean::cnstr_set_scalar(x_289, sizeof(void*)*1, x_287);
x_290 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_249, x_289);
x_291 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_245, x_290);
x_292 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_215, x_291);
x_293 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_294 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_293, x_292);
return x_294;
}
}
else
{
obj* x_295; uint8 x_296; obj* x_297; obj* x_298; obj* x_299; obj* x_300; obj* x_301; obj* x_302; 
lean::dec(x_243);
x_295 = lean::cnstr_get(x_246, 0);
lean::inc(x_295);
x_296 = lean::cnstr_get_scalar<uint8>(x_246, sizeof(void*)*1);
if (lean::is_exclusive(x_246)) {
 lean::cnstr_release(x_246, 0);
 x_297 = x_246;
} else {
 lean::dec_ref(x_246);
 x_297 = lean::box(0);
}
if (lean::is_scalar(x_297)) {
 x_298 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_298 = x_297;
}
lean::cnstr_set(x_298, 0, x_295);
lean::cnstr_set_scalar(x_298, sizeof(void*)*1, x_296);
x_299 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_245, x_298);
x_300 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_215, x_299);
x_301 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_302 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_301, x_300);
return x_302;
}
}
else
{
obj* x_303; uint8 x_304; obj* x_305; obj* x_306; obj* x_307; obj* x_308; obj* x_309; 
x_303 = lean::cnstr_get(x_242, 0);
lean::inc(x_303);
x_304 = lean::cnstr_get_scalar<uint8>(x_242, sizeof(void*)*1);
if (lean::is_exclusive(x_242)) {
 lean::cnstr_release(x_242, 0);
 x_305 = x_242;
} else {
 lean::dec_ref(x_242);
 x_305 = lean::box(0);
}
if (lean::is_scalar(x_305)) {
 x_306 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_306 = x_305;
}
lean::cnstr_set(x_306, 0, x_303);
lean::cnstr_set_scalar(x_306, sizeof(void*)*1, x_304);
x_307 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_215, x_306);
x_308 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_309 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_308, x_307);
return x_309;
}
}
}
else
{
obj* x_310; 
lean::dec(x_213);
lean::dec(x_1);
x_310 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_View_value___spec__8(x_214);
if (lean::obj_tag(x_310) == 0)
{
obj* x_311; obj* x_312; obj* x_313; obj* x_314; 
x_311 = lean::cnstr_get(x_310, 0);
lean::inc(x_311);
x_312 = lean::cnstr_get(x_310, 1);
lean::inc(x_312);
x_313 = lean::cnstr_get(x_310, 2);
lean::inc(x_313);
lean::dec(x_310);
x_314 = l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_View_value___spec__8(x_312);
if (lean::obj_tag(x_314) == 0)
{
obj* x_315; obj* x_316; obj* x_317; obj* x_318; obj* x_319; obj* x_320; obj* x_321; uint32 x_322; obj* x_323; obj* x_324; obj* x_325; obj* x_326; obj* x_327; obj* x_328; obj* x_329; 
x_315 = lean::cnstr_get(x_314, 0);
lean::inc(x_315);
x_316 = lean::cnstr_get(x_314, 1);
lean::inc(x_316);
x_317 = lean::cnstr_get(x_314, 2);
lean::inc(x_317);
if (lean::is_exclusive(x_314)) {
 lean::cnstr_release(x_314, 0);
 lean::cnstr_release(x_314, 1);
 lean::cnstr_release(x_314, 2);
 x_318 = x_314;
} else {
 lean::dec_ref(x_314);
 x_318 = lean::box(0);
}
x_319 = lean::mk_nat_obj(16u);
x_320 = lean::nat_mul(x_319, x_311);
lean::dec(x_311);
x_321 = lean::nat_add(x_320, x_315);
lean::dec(x_315);
lean::dec(x_320);
x_322 = l_Char_ofNat(x_321);
lean::dec(x_321);
x_323 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_324 = lean::box_uint32(x_322);
if (lean::is_scalar(x_318)) {
 x_325 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_325 = x_318;
}
lean::cnstr_set(x_325, 0, x_324);
lean::cnstr_set(x_325, 1, x_316);
lean::cnstr_set(x_325, 2, x_323);
x_326 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_317, x_325);
x_327 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_313, x_326);
x_328 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_215, x_327);
x_329 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_323, x_328);
return x_329;
}
else
{
obj* x_330; uint8 x_331; obj* x_332; obj* x_333; obj* x_334; obj* x_335; obj* x_336; obj* x_337; 
lean::dec(x_311);
x_330 = lean::cnstr_get(x_314, 0);
lean::inc(x_330);
x_331 = lean::cnstr_get_scalar<uint8>(x_314, sizeof(void*)*1);
if (lean::is_exclusive(x_314)) {
 lean::cnstr_release(x_314, 0);
 x_332 = x_314;
} else {
 lean::dec_ref(x_314);
 x_332 = lean::box(0);
}
if (lean::is_scalar(x_332)) {
 x_333 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_333 = x_332;
}
lean::cnstr_set(x_333, 0, x_330);
lean::cnstr_set_scalar(x_333, sizeof(void*)*1, x_331);
x_334 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_313, x_333);
x_335 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_215, x_334);
x_336 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_337 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_336, x_335);
return x_337;
}
}
else
{
obj* x_338; uint8 x_339; obj* x_340; obj* x_341; obj* x_342; obj* x_343; obj* x_344; 
x_338 = lean::cnstr_get(x_310, 0);
lean::inc(x_338);
x_339 = lean::cnstr_get_scalar<uint8>(x_310, sizeof(void*)*1);
if (lean::is_exclusive(x_310)) {
 lean::cnstr_release(x_310, 0);
 x_340 = x_310;
} else {
 lean::dec_ref(x_310);
 x_340 = lean::box(0);
}
if (lean::is_scalar(x_340)) {
 x_341 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_341 = x_340;
}
lean::cnstr_set(x_341, 0, x_338);
lean::cnstr_set_scalar(x_341, sizeof(void*)*1, x_339);
x_342 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_215, x_341);
x_343 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_344 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_343, x_342);
return x_344;
}
}
}
else
{
uint32 x_345; obj* x_346; obj* x_347; obj* x_348; obj* x_349; obj* x_350; 
lean::dec(x_213);
lean::dec(x_1);
x_345 = 9;
x_346 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_347 = lean::box_uint32(x_345);
x_348 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_348, 0, x_347);
lean::cnstr_set(x_348, 1, x_214);
lean::cnstr_set(x_348, 2, x_346);
x_349 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_215, x_348);
x_350 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_346, x_349);
return x_350;
}
}
else
{
uint32 x_351; obj* x_352; obj* x_353; obj* x_354; obj* x_355; obj* x_356; 
lean::dec(x_213);
lean::dec(x_1);
x_351 = 10;
x_352 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_353 = lean::box_uint32(x_351);
x_354 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_354, 0, x_353);
lean::cnstr_set(x_354, 1, x_214);
lean::cnstr_set(x_354, 2, x_352);
x_355 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_215, x_354);
x_356 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_352, x_355);
return x_356;
}
}
else
{
obj* x_357; obj* x_358; obj* x_359; obj* x_360; obj* x_361; 
lean::dec(x_213);
lean::dec(x_1);
x_357 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_358 = lean::box_uint32(x_222);
x_359 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_359, 0, x_358);
lean::cnstr_set(x_359, 1, x_214);
lean::cnstr_set(x_359, 2, x_357);
x_360 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_215, x_359);
x_361 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_357, x_360);
return x_361;
}
}
else
{
obj* x_362; obj* x_363; obj* x_364; obj* x_365; obj* x_366; 
lean::dec(x_213);
lean::dec(x_1);
x_362 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_363 = lean::box_uint32(x_219);
x_364 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_364, 0, x_363);
lean::cnstr_set(x_364, 1, x_214);
lean::cnstr_set(x_364, 2, x_362);
x_365 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_215, x_364);
x_366 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_362, x_365);
return x_366;
}
}
else
{
obj* x_367; obj* x_368; obj* x_369; obj* x_370; obj* x_371; 
lean::dec(x_213);
lean::dec(x_1);
x_367 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_368 = lean::box_uint32(x_216);
x_369 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_369, 0, x_368);
lean::cnstr_set(x_369, 1, x_214);
lean::cnstr_set(x_369, 2, x_367);
x_370 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_215, x_369);
x_371 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_367, x_370);
return x_371;
}
}
}
else
{
uint8 x_372; 
lean::dec(x_1);
x_372 = !lean::is_exclusive(x_2);
if (x_372 == 0)
{
obj* x_373; obj* x_374; 
x_373 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_374 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_373, x_2);
return x_374;
}
else
{
obj* x_375; uint8 x_376; obj* x_377; obj* x_378; obj* x_379; 
x_375 = lean::cnstr_get(x_2, 0);
x_376 = lean::cnstr_get_scalar<uint8>(x_2, sizeof(void*)*1);
lean::inc(x_375);
lean::dec(x_2);
x_377 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_377, 0, x_375);
lean::cnstr_set_scalar(x_377, sizeof(void*)*1, x_376);
x_378 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_379 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_378, x_377);
return x_379;
}
}
}
}
obj* l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_View_value___spec__4(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; uint8 x_5; 
x_4 = lean::mk_nat_obj(0u);
x_5 = lean::nat_dec_eq(x_1, x_4);
if (x_5 == 0)
{
obj* x_6; obj* x_7; obj* x_8; 
x_6 = lean::mk_nat_obj(1u);
x_7 = lean::nat_sub(x_1, x_6);
x_8 = l_Lean_Parser_MonadParsec_any___at_Lean_Parser_stringLit_View_value___spec__5(x_3);
if (lean::obj_tag(x_8) == 0)
{
uint8 x_9; 
x_9 = !lean::is_exclusive(x_8);
if (x_9 == 0)
{
obj* x_10; obj* x_11; obj* x_12; uint32 x_13; uint32 x_14; uint8 x_15; 
x_10 = lean::cnstr_get(x_8, 0);
x_11 = lean::cnstr_get(x_8, 1);
x_12 = lean::cnstr_get(x_8, 2);
x_13 = 92;
x_14 = lean::unbox_uint32(x_10);
x_15 = x_14 == x_13;
if (x_15 == 0)
{
uint32 x_16; uint32 x_17; uint8 x_18; 
x_16 = 34;
x_17 = lean::unbox_uint32(x_10);
x_18 = x_17 == x_16;
if (x_18 == 0)
{
uint32 x_19; obj* x_20; obj* x_21; obj* x_22; 
lean::free_heap_obj(x_8);
x_19 = lean::unbox_uint32(x_10);
lean::dec(x_10);
x_20 = lean::string_push(x_2, x_19);
x_21 = l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_View_value___spec__4(x_7, x_20, x_11);
lean::dec(x_7);
x_22 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_21);
return x_22;
}
else
{
obj* x_23; obj* x_24; 
lean::dec(x_10);
lean::dec(x_7);
x_23 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_8, 2, x_23);
lean::cnstr_set(x_8, 0, x_2);
x_24 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_8);
return x_24;
}
}
else
{
obj* x_25; 
lean::free_heap_obj(x_8);
lean::dec(x_10);
x_25 = l_Lean_Parser_parseQuotedChar___at_Lean_Parser_stringLit_View_value___spec__6(x_11);
if (lean::obj_tag(x_25) == 0)
{
obj* x_26; obj* x_27; obj* x_28; uint32 x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_26 = lean::cnstr_get(x_25, 0);
lean::inc(x_26);
x_27 = lean::cnstr_get(x_25, 1);
lean::inc(x_27);
x_28 = lean::cnstr_get(x_25, 2);
lean::inc(x_28);
lean::dec(x_25);
x_29 = lean::unbox_uint32(x_26);
lean::dec(x_26);
x_30 = lean::string_push(x_2, x_29);
x_31 = l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_View_value___spec__4(x_7, x_30, x_27);
lean::dec(x_7);
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_28, x_31);
x_33 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_32);
return x_33;
}
else
{
uint8 x_34; 
lean::dec(x_7);
lean::dec(x_2);
x_34 = !lean::is_exclusive(x_25);
if (x_34 == 0)
{
obj* x_35; 
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_25);
return x_35;
}
else
{
obj* x_36; uint8 x_37; obj* x_38; obj* x_39; 
x_36 = lean::cnstr_get(x_25, 0);
x_37 = lean::cnstr_get_scalar<uint8>(x_25, sizeof(void*)*1);
lean::inc(x_36);
lean::dec(x_25);
x_38 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_38, 0, x_36);
lean::cnstr_set_scalar(x_38, sizeof(void*)*1, x_37);
x_39 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_12, x_38);
return x_39;
}
}
}
}
else
{
obj* x_40; obj* x_41; obj* x_42; uint32 x_43; uint32 x_44; uint8 x_45; 
x_40 = lean::cnstr_get(x_8, 0);
x_41 = lean::cnstr_get(x_8, 1);
x_42 = lean::cnstr_get(x_8, 2);
lean::inc(x_42);
lean::inc(x_41);
lean::inc(x_40);
lean::dec(x_8);
x_43 = 92;
x_44 = lean::unbox_uint32(x_40);
x_45 = x_44 == x_43;
if (x_45 == 0)
{
uint32 x_46; uint32 x_47; uint8 x_48; 
x_46 = 34;
x_47 = lean::unbox_uint32(x_40);
x_48 = x_47 == x_46;
if (x_48 == 0)
{
uint32 x_49; obj* x_50; obj* x_51; obj* x_52; 
x_49 = lean::unbox_uint32(x_40);
lean::dec(x_40);
x_50 = lean::string_push(x_2, x_49);
x_51 = l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_View_value___spec__4(x_7, x_50, x_41);
lean::dec(x_7);
x_52 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_42, x_51);
return x_52;
}
else
{
obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_40);
lean::dec(x_7);
x_53 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_54 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_54, 0, x_2);
lean::cnstr_set(x_54, 1, x_41);
lean::cnstr_set(x_54, 2, x_53);
x_55 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_42, x_54);
return x_55;
}
}
else
{
obj* x_56; 
lean::dec(x_40);
x_56 = l_Lean_Parser_parseQuotedChar___at_Lean_Parser_stringLit_View_value___spec__6(x_41);
if (lean::obj_tag(x_56) == 0)
{
obj* x_57; obj* x_58; obj* x_59; uint32 x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_57 = lean::cnstr_get(x_56, 0);
lean::inc(x_57);
x_58 = lean::cnstr_get(x_56, 1);
lean::inc(x_58);
x_59 = lean::cnstr_get(x_56, 2);
lean::inc(x_59);
lean::dec(x_56);
x_60 = lean::unbox_uint32(x_57);
lean::dec(x_57);
x_61 = lean::string_push(x_2, x_60);
x_62 = l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_View_value___spec__4(x_7, x_61, x_58);
lean::dec(x_7);
x_63 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_59, x_62);
x_64 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_42, x_63);
return x_64;
}
else
{
obj* x_65; uint8 x_66; obj* x_67; obj* x_68; obj* x_69; 
lean::dec(x_7);
lean::dec(x_2);
x_65 = lean::cnstr_get(x_56, 0);
lean::inc(x_65);
x_66 = lean::cnstr_get_scalar<uint8>(x_56, sizeof(void*)*1);
if (lean::is_exclusive(x_56)) {
 lean::cnstr_release(x_56, 0);
 x_67 = x_56;
} else {
 lean::dec_ref(x_56);
 x_67 = lean::box(0);
}
if (lean::is_scalar(x_67)) {
 x_68 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_68 = x_67;
}
lean::cnstr_set(x_68, 0, x_65);
lean::cnstr_set_scalar(x_68, sizeof(void*)*1, x_66);
x_69 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_42, x_68);
return x_69;
}
}
}
}
else
{
uint8 x_70; 
lean::dec(x_7);
lean::dec(x_2);
x_70 = !lean::is_exclusive(x_8);
if (x_70 == 0)
{
return x_8;
}
else
{
obj* x_71; uint8 x_72; obj* x_73; 
x_71 = lean::cnstr_get(x_8, 0);
x_72 = lean::cnstr_get_scalar<uint8>(x_8, sizeof(void*)*1);
lean::inc(x_71);
lean::dec(x_8);
x_73 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_73, 0, x_71);
lean::cnstr_set_scalar(x_73, sizeof(void*)*1, x_72);
return x_73;
}
}
}
else
{
uint32 x_74; obj* x_75; 
x_74 = 34;
x_75 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_stringLit_View_value___spec__2(x_74, x_3);
if (lean::obj_tag(x_75) == 0)
{
uint8 x_76; 
x_76 = !lean::is_exclusive(x_75);
if (x_76 == 0)
{
obj* x_77; obj* x_78; obj* x_79; obj* x_80; 
x_77 = lean::cnstr_get(x_75, 2);
x_78 = lean::cnstr_get(x_75, 0);
lean::dec(x_78);
x_79 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_75, 2, x_79);
lean::cnstr_set(x_75, 0, x_2);
x_80 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_77, x_75);
return x_80;
}
else
{
obj* x_81; obj* x_82; obj* x_83; obj* x_84; obj* x_85; 
x_81 = lean::cnstr_get(x_75, 1);
x_82 = lean::cnstr_get(x_75, 2);
lean::inc(x_82);
lean::inc(x_81);
lean::dec(x_75);
x_83 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_84 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_84, 0, x_2);
lean::cnstr_set(x_84, 1, x_81);
lean::cnstr_set(x_84, 2, x_83);
x_85 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_82, x_84);
return x_85;
}
}
else
{
uint8 x_86; 
lean::dec(x_2);
x_86 = !lean::is_exclusive(x_75);
if (x_86 == 0)
{
return x_75;
}
else
{
obj* x_87; uint8 x_88; obj* x_89; 
x_87 = lean::cnstr_get(x_75, 0);
x_88 = lean::cnstr_get_scalar<uint8>(x_75, sizeof(void*)*1);
lean::inc(x_87);
lean::dec(x_75);
x_89 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_89, 0, x_87);
lean::cnstr_set_scalar(x_89, sizeof(void*)*1, x_88);
return x_89;
}
}
}
}
}
obj* l_Lean_Parser_parseStringLiteral___at_Lean_Parser_stringLit_View_value___spec__1(obj* x_1) {
_start:
{
uint32 x_2; obj* x_3; 
x_2 = 34;
x_3 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_stringLit_View_value___spec__2(x_2, x_1);
if (lean::obj_tag(x_3) == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; 
x_4 = lean::cnstr_get(x_3, 1);
lean::inc(x_4);
x_5 = lean::cnstr_get(x_3, 2);
lean::inc(x_5);
lean::dec(x_3);
x_6 = l_String_OldIterator_remaining___main(x_4);
x_7 = l_String_splitAux___main___closed__1;
x_8 = l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_View_value___spec__4(x_6, x_7, x_4);
lean::dec(x_6);
x_9 = l_Lean_Parser_finishCommentBlock___closed__2;
x_10 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_9, x_8);
x_11 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_5, x_10);
return x_11;
}
else
{
uint8 x_12; 
x_12 = !lean::is_exclusive(x_3);
if (x_12 == 0)
{
return x_3;
}
else
{
obj* x_13; uint8 x_14; obj* x_15; 
x_13 = lean::cnstr_get(x_3, 0);
x_14 = lean::cnstr_get_scalar<uint8>(x_3, sizeof(void*)*1);
lean::inc(x_13);
lean::dec(x_3);
x_15 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_15, 0, x_13);
lean::cnstr_set_scalar(x_15, sizeof(void*)*1, x_14);
return x_15;
}
}
}
}
obj* _init_l_Lean_Parser_stringLit_View_value___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_parseStringLiteral___at_Lean_Parser_stringLit_View_value___spec__1), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_stringLit_View_value(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_2; 
lean::dec(x_1);
x_2 = lean::box(0);
return x_2;
}
else
{
uint8 x_3; 
x_3 = !lean::is_exclusive(x_1);
if (x_3 == 0)
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_4, 1);
lean::inc(x_5);
lean::dec(x_4);
x_6 = l_Lean_Parser_stringLit_View_value___closed__1;
x_7 = l_String_splitAux___main___closed__1;
x_8 = l_Lean_Parser_ParsecT_run___at_Lean_Parser_Parsec_parse___spec__1___rarg(x_6, x_5, x_7);
if (lean::obj_tag(x_8) == 0)
{
obj* x_9; 
lean::dec(x_8);
lean::free_heap_obj(x_1);
x_9 = lean::box(0);
return x_9;
}
else
{
obj* x_10; 
x_10 = lean::cnstr_get(x_8, 0);
lean::inc(x_10);
lean::dec(x_8);
lean::cnstr_set(x_1, 0, x_10);
return x_1;
}
}
else
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_11 = lean::cnstr_get(x_1, 0);
lean::inc(x_11);
lean::dec(x_1);
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
lean::dec(x_11);
x_13 = l_Lean_Parser_stringLit_View_value___closed__1;
x_14 = l_String_splitAux___main___closed__1;
x_15 = l_Lean_Parser_ParsecT_run___at_Lean_Parser_Parsec_parse___spec__1___rarg(x_13, x_12, x_14);
if (lean::obj_tag(x_15) == 0)
{
obj* x_16; 
lean::dec(x_15);
x_16 = lean::box(0);
return x_16;
}
else
{
obj* x_17; obj* x_18; 
x_17 = lean::cnstr_get(x_15, 0);
lean::inc(x_17);
lean::dec(x_15);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_17);
return x_18;
}
}
}
}
}
obj* l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_MonadParsec_error___at_Lean_Parser_stringLit_View_value___spec__3___rarg(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
return x_6;
}
}
obj* l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_stringLit_View_value___spec__2___boxed(obj* x_1, obj* x_2) {
_start:
{
uint32 x_3; obj* x_4; 
x_3 = lean::unbox_uint32(x_1);
lean::dec(x_1);
x_4 = l_Lean_Parser_MonadParsec_ch___at_Lean_Parser_stringLit_View_value___spec__2(x_3, x_2);
return x_4;
}
}
obj* l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_View_value___spec__4___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_parseStringLiteralAux___main___at_Lean_Parser_stringLit_View_value___spec__4(x_1, x_2, x_3);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_ident_Parser___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_3);
lean::inc(x_2);
x_5 = l_Lean_Parser_token(x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
uint8 x_7; 
x_7 = !lean::is_exclusive(x_5);
if (x_7 == 0)
{
obj* x_8; obj* x_9; uint8 x_10; 
x_8 = lean::cnstr_get(x_5, 1);
x_9 = lean::cnstr_get(x_5, 0);
lean::dec(x_9);
x_10 = !lean::is_exclusive(x_6);
if (x_10 == 0)
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; 
x_11 = lean::cnstr_get(x_6, 0);
x_12 = lean::cnstr_get(x_6, 1);
x_13 = lean::cnstr_get(x_6, 2);
if (lean::obj_tag(x_11) == 1)
{
obj* x_35; obj* x_36; obj* x_37; obj* x_38; obj* x_39; 
lean::dec(x_3);
lean::dec(x_2);
x_35 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_6, 2, x_35);
x_36 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_6);
x_37 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_35, x_36);
x_38 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_37, x_1);
x_39 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_38);
lean::cnstr_set(x_5, 0, x_39);
return x_5;
}
else
{
obj* x_40; 
lean::free_heap_obj(x_6);
lean::dec(x_11);
lean::free_heap_obj(x_5);
x_40 = lean::box(0);
x_14 = x_40;
goto block_34;
}
block_34:
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; uint8 x_19; 
lean::dec(x_14);
x_15 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_15, 0, x_3);
x_16 = lean::box(0);
x_17 = l_String_splitAux___main___closed__1;
lean::inc(x_1);
x_18 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_17, x_1, x_15, x_16, x_2, x_12, x_8);
lean::dec(x_2);
lean::dec(x_15);
x_19 = !lean::is_exclusive(x_18);
if (x_19 == 0)
{
obj* x_20; obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_20 = lean::cnstr_get(x_18, 0);
x_21 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_20);
x_22 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_23 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_22, x_21);
x_24 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_23, x_1);
x_25 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_24);
lean::cnstr_set(x_18, 0, x_25);
return x_18;
}
else
{
obj* x_26; obj* x_27; obj* x_28; obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; 
x_26 = lean::cnstr_get(x_18, 0);
x_27 = lean::cnstr_get(x_18, 1);
lean::inc(x_27);
lean::inc(x_26);
lean::dec(x_18);
x_28 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_13, x_26);
x_29 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_30 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_29, x_28);
x_31 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_30, x_1);
x_32 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_31);
x_33 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_33, 0, x_32);
lean::cnstr_set(x_33, 1, x_27);
return x_33;
}
}
}
else
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
x_41 = lean::cnstr_get(x_6, 0);
x_42 = lean::cnstr_get(x_6, 1);
x_43 = lean::cnstr_get(x_6, 2);
lean::inc(x_43);
lean::inc(x_42);
lean::inc(x_41);
lean::dec(x_6);
if (lean::obj_tag(x_41) == 1)
{
obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
lean::dec(x_3);
lean::dec(x_2);
x_59 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_60 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_60, 0, x_41);
lean::cnstr_set(x_60, 1, x_42);
lean::cnstr_set(x_60, 2, x_59);
x_61 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_43, x_60);
x_62 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_59, x_61);
x_63 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_62, x_1);
x_64 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_63);
lean::cnstr_set(x_5, 0, x_64);
return x_5;
}
else
{
obj* x_65; 
lean::dec(x_41);
lean::free_heap_obj(x_5);
x_65 = lean::box(0);
x_44 = x_65;
goto block_58;
}
block_58:
{
obj* x_45; obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
lean::dec(x_44);
x_45 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_45, 0, x_3);
x_46 = lean::box(0);
x_47 = l_String_splitAux___main___closed__1;
lean::inc(x_1);
x_48 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_47, x_1, x_45, x_46, x_2, x_42, x_8);
lean::dec(x_2);
lean::dec(x_45);
x_49 = lean::cnstr_get(x_48, 0);
lean::inc(x_49);
x_50 = lean::cnstr_get(x_48, 1);
lean::inc(x_50);
if (lean::is_exclusive(x_48)) {
 lean::cnstr_release(x_48, 0);
 lean::cnstr_release(x_48, 1);
 x_51 = x_48;
} else {
 lean::dec_ref(x_48);
 x_51 = lean::box(0);
}
x_52 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_43, x_49);
x_53 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_53, x_52);
x_55 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_54, x_1);
x_56 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_55);
if (lean::is_scalar(x_51)) {
 x_57 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_57 = x_51;
}
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_50);
return x_57;
}
}
}
else
{
obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_66 = lean::cnstr_get(x_5, 1);
lean::inc(x_66);
lean::dec(x_5);
x_67 = lean::cnstr_get(x_6, 0);
lean::inc(x_67);
x_68 = lean::cnstr_get(x_6, 1);
lean::inc(x_68);
x_69 = lean::cnstr_get(x_6, 2);
lean::inc(x_69);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_70 = x_6;
} else {
 lean::dec_ref(x_6);
 x_70 = lean::box(0);
}
if (lean::obj_tag(x_67) == 1)
{
obj* x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
lean::dec(x_3);
lean::dec(x_2);
x_86 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_70)) {
 x_87 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_87 = x_70;
}
lean::cnstr_set(x_87, 0, x_67);
lean::cnstr_set(x_87, 1, x_68);
lean::cnstr_set(x_87, 2, x_86);
x_88 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_69, x_87);
x_89 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_86, x_88);
x_90 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_89, x_1);
x_91 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_90);
x_92 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_92, 0, x_91);
lean::cnstr_set(x_92, 1, x_66);
return x_92;
}
else
{
obj* x_93; 
lean::dec(x_70);
lean::dec(x_67);
x_93 = lean::box(0);
x_71 = x_93;
goto block_85;
}
block_85:
{
obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
lean::dec(x_71);
x_72 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_72, 0, x_3);
x_73 = lean::box(0);
x_74 = l_String_splitAux___main___closed__1;
lean::inc(x_1);
x_75 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_74, x_1, x_72, x_73, x_2, x_68, x_66);
lean::dec(x_2);
lean::dec(x_72);
x_76 = lean::cnstr_get(x_75, 0);
lean::inc(x_76);
x_77 = lean::cnstr_get(x_75, 1);
lean::inc(x_77);
if (lean::is_exclusive(x_75)) {
 lean::cnstr_release(x_75, 0);
 lean::cnstr_release(x_75, 1);
 x_78 = x_75;
} else {
 lean::dec_ref(x_75);
 x_78 = lean::box(0);
}
x_79 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_69, x_76);
x_80 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_81 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_80, x_79);
x_82 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_81, x_1);
x_83 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_82);
if (lean::is_scalar(x_78)) {
 x_84 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_84 = x_78;
}
lean::cnstr_set(x_84, 0, x_83);
lean::cnstr_set(x_84, 1, x_77);
return x_84;
}
}
}
else
{
uint8 x_94; 
lean::dec(x_3);
lean::dec(x_2);
x_94 = !lean::is_exclusive(x_5);
if (x_94 == 0)
{
obj* x_95; uint8 x_96; 
x_95 = lean::cnstr_get(x_5, 0);
lean::dec(x_95);
x_96 = !lean::is_exclusive(x_6);
if (x_96 == 0)
{
obj* x_97; obj* x_98; obj* x_99; obj* x_100; 
x_97 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_98 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_97, x_6);
x_99 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_98, x_1);
x_100 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_99);
lean::cnstr_set(x_5, 0, x_100);
return x_5;
}
else
{
obj* x_101; uint8 x_102; obj* x_103; obj* x_104; obj* x_105; obj* x_106; obj* x_107; 
x_101 = lean::cnstr_get(x_6, 0);
x_102 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
lean::inc(x_101);
lean::dec(x_6);
x_103 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_103, 0, x_101);
lean::cnstr_set_scalar(x_103, sizeof(void*)*1, x_102);
x_104 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_105 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_104, x_103);
x_106 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_105, x_1);
x_107 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_106);
lean::cnstr_set(x_5, 0, x_107);
return x_5;
}
}
else
{
obj* x_108; obj* x_109; uint8 x_110; obj* x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
x_108 = lean::cnstr_get(x_5, 1);
lean::inc(x_108);
lean::dec(x_5);
x_109 = lean::cnstr_get(x_6, 0);
lean::inc(x_109);
x_110 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_111 = x_6;
} else {
 lean::dec_ref(x_6);
 x_111 = lean::box(0);
}
if (lean::is_scalar(x_111)) {
 x_112 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_112 = x_111;
}
lean::cnstr_set(x_112, 0, x_109);
lean::cnstr_set_scalar(x_112, sizeof(void*)*1, x_110);
x_113 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_114 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_113, x_112);
x_115 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_114, x_1);
x_116 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_115);
x_117 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_117, 0, x_116);
lean::cnstr_set(x_117, 1, x_108);
return x_117;
}
}
}
}
obj* _init_l_Lean_Parser_ident_Parser___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::mk_string("identifier");
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_2, 0, x_1);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___rarg___lambda__1), 4, 1);
lean::closure_set(x_3, 0, x_2);
return x_3;
}
}
obj* l_Lean_Parser_ident_Parser___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Parser_ident_Parser___rarg___closed__1;
x_3 = lean::apply_2(x_1, lean::box(0), x_2);
return x_3;
}
}
obj* l_Lean_Parser_ident_Parser(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_Parser_ident_Parser___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ident_Parser(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ident_Parser_tokens(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
}
obj* l_Lean_Parser_ident_Parser_tokens___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_ident_Parser_tokens(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* _init_l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_1 = lean::box(0);
x_2 = lean::mk_string("NOTAnIdent");
lean::inc(x_2);
x_3 = l_Lean_Parser_Substring_ofString(x_2);
x_4 = lean::box(0);
x_5 = lean_name_mk_string(x_4, x_2);
x_6 = lean::box(0);
x_7 = lean::alloc_cnstr(0, 5, 0);
lean::cnstr_set(x_7, 0, x_1);
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
obj* x_1; 
x_1 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__1;
return x_1;
}
}
obj* l_Lean_Parser_ident_Parser_View___rarg___lambda__1(obj* x_1) {
_start:
{
if (lean::obj_tag(x_1) == 1)
{
obj* x_2; 
x_2 = lean::cnstr_get(x_1, 0);
lean::inc(x_2);
return x_2;
}
else
{
obj* x_3; 
x_3 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1___closed__2;
return x_3;
}
}
}
obj* l_Lean_Parser_ident_Parser_View___rarg___lambda__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_2, 0, x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_ident_Parser_View___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser_View___rarg___lambda__1___boxed), 1, 0);
return x_1;
}
}
obj* _init_l_Lean_Parser_ident_Parser_View___rarg___closed__2() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser_View___rarg___lambda__2), 1, 0);
return x_1;
}
}
obj* l_Lean_Parser_ident_Parser_View___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Parser_ident_Parser_View___rarg___closed__1;
x_3 = l_Lean_Parser_ident_Parser_View___rarg___closed__2;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_Lean_Parser_ident_Parser_View(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_ident_Parser_View___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_Parser_ident_Parser_View___rarg___lambda__1___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ident_Parser_View___rarg___lambda__1(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ident_Parser_View___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ident_Parser_View___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_ident_Parser_View___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_ident_Parser_View(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* _init_l_Lean_Parser_rawIdent_Parser___rarg___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l___private_init_lean_parser_token_4__ident_x27), 3, 0);
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_withTrailing___at_Lean_Parser_token___spec__3___boxed), 4, 0);
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_3, 0, x_1);
lean::closure_set(x_3, 1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_rawIdent_Parser___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; 
x_2 = l_Lean_Parser_rawIdent_Parser___rarg___closed__1;
x_3 = lean::apply_2(x_1, lean::box(0), x_2);
return x_3;
}
}
obj* l_Lean_Parser_rawIdent_Parser(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_rawIdent_Parser___rarg), 1, 0);
return x_2;
}
}
obj* l_Lean_Parser_rawIdent_Parser___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_rawIdent_Parser(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_rawIdent_Parser_tokens(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
}
obj* l_Lean_Parser_rawIdent_Parser_tokens___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_rawIdent_Parser_tokens(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_rawIdent_Parser_View___rarg(obj* x_1) {
_start:
{
obj* x_2; obj* x_3; obj* x_4; 
x_2 = l_Lean_Parser_ident_Parser_View___rarg___closed__1;
x_3 = l_Lean_Parser_ident_Parser_View___rarg___closed__2;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_2);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_Lean_Parser_rawIdent_Parser_View(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_rawIdent_Parser_View___rarg___boxed), 1, 0);
return x_2;
}
}
obj* l_Lean_Parser_rawIdent_Parser_View___rarg___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_rawIdent_Parser_View___rarg(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_rawIdent_Parser_View___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_rawIdent_Parser_View(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_symbolOrIdent___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; 
lean::inc(x_3);
lean::inc(x_2);
x_5 = l_Lean_Parser_token(x_2, x_3, x_4);
x_6 = lean::cnstr_get(x_5, 0);
lean::inc(x_6);
if (lean::obj_tag(x_6) == 0)
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; 
x_7 = lean::cnstr_get(x_5, 1);
lean::inc(x_7);
if (lean::is_exclusive(x_5)) {
 lean::cnstr_release(x_5, 0);
 lean::cnstr_release(x_5, 1);
 x_8 = x_5;
} else {
 lean::dec_ref(x_5);
 x_8 = lean::box(0);
}
x_9 = lean::cnstr_get(x_6, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_6, 1);
lean::inc(x_10);
x_11 = lean::cnstr_get(x_6, 2);
lean::inc(x_11);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 lean::cnstr_release(x_6, 1);
 lean::cnstr_release(x_6, 2);
 x_12 = x_6;
} else {
 lean::dec_ref(x_6);
 x_12 = lean::box(0);
}
switch (lean::obj_tag(x_9)) {
case 0:
{
obj* x_89; obj* x_90; obj* x_91; 
x_89 = lean::cnstr_get(x_9, 0);
lean::inc(x_89);
x_90 = lean::cnstr_get(x_89, 1);
lean::inc(x_90);
lean::dec(x_89);
x_91 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_91, 0, x_90);
x_13 = x_91;
goto block_88;
}
case 1:
{
obj* x_92; obj* x_93; obj* x_94; obj* x_95; 
x_92 = lean::cnstr_get(x_9, 0);
lean::inc(x_92);
x_93 = lean::cnstr_get(x_92, 1);
lean::inc(x_93);
lean::dec(x_92);
x_94 = l_Lean_Parser_Substring_toString(x_93);
lean::dec(x_93);
x_95 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_95, 0, x_94);
x_13 = x_95;
goto block_88;
}
default: 
{
obj* x_96; 
x_96 = lean::box(0);
x_13 = x_96;
goto block_88;
}
}
block_88:
{
uint8 x_14; 
if (lean::obj_tag(x_13) == 0)
{
uint8 x_83; 
lean::dec(x_13);
x_83 = 1;
x_14 = x_83;
goto block_82;
}
else
{
obj* x_84; uint8 x_85; 
x_84 = lean::cnstr_get(x_13, 0);
lean::inc(x_84);
lean::dec(x_13);
x_85 = lean::string_dec_eq(x_84, x_1);
lean::dec(x_84);
if (x_85 == 0)
{
uint8 x_86; 
x_86 = 1;
x_14 = x_86;
goto block_82;
}
else
{
uint8 x_87; 
x_87 = 0;
x_14 = x_87;
goto block_82;
}
}
block_82:
{
if (x_14 == 0)
{
obj* x_15; obj* x_16; obj* x_17; obj* x_18; obj* x_19; obj* x_20; obj* x_21; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_15 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_12)) {
 x_16 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_16 = x_12;
}
lean::cnstr_set(x_16, 0, x_9);
lean::cnstr_set(x_16, 1, x_10);
lean::cnstr_set(x_16, 2, x_15);
x_17 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_16);
x_18 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_19 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_18, x_17);
x_20 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_19);
if (lean::is_scalar(x_8)) {
 x_21 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_21 = x_8;
}
lean::cnstr_set(x_21, 0, x_20);
lean::cnstr_set(x_21, 1, x_7);
return x_21;
}
else
{
obj* x_22; obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
lean::dec(x_12);
lean::dec(x_8);
x_22 = l_String_quote(x_1);
x_23 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_23, 0, x_22);
x_24 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_24, 0, x_3);
x_25 = lean::box(0);
x_26 = l_String_splitAux___main___closed__1;
x_27 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_26, x_23, x_24, x_25, x_2, x_10, x_7);
lean::dec(x_2);
lean::dec(x_24);
x_28 = lean::cnstr_get(x_27, 0);
lean::inc(x_28);
if (lean::obj_tag(x_28) == 0)
{
uint8 x_29; 
x_29 = !lean::is_exclusive(x_27);
if (x_29 == 0)
{
obj* x_30; uint8 x_31; 
x_30 = lean::cnstr_get(x_27, 0);
lean::dec(x_30);
x_31 = !lean::is_exclusive(x_28);
if (x_31 == 0)
{
obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; obj* x_38; 
x_32 = lean::cnstr_get(x_28, 2);
x_33 = lean::cnstr_get(x_28, 0);
lean::dec(x_33);
x_34 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_28, 2, x_34);
lean::cnstr_set(x_28, 0, x_9);
x_35 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_32, x_28);
x_36 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_35);
x_37 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_34, x_36);
x_38 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_37);
lean::cnstr_set(x_27, 0, x_38);
return x_27;
}
else
{
obj* x_39; obj* x_40; obj* x_41; obj* x_42; obj* x_43; obj* x_44; obj* x_45; obj* x_46; 
x_39 = lean::cnstr_get(x_28, 1);
x_40 = lean::cnstr_get(x_28, 2);
lean::inc(x_40);
lean::inc(x_39);
lean::dec(x_28);
x_41 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_42 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_42, 0, x_9);
lean::cnstr_set(x_42, 1, x_39);
lean::cnstr_set(x_42, 2, x_41);
x_43 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_40, x_42);
x_44 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_43);
x_45 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_41, x_44);
x_46 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_45);
lean::cnstr_set(x_27, 0, x_46);
return x_27;
}
}
else
{
obj* x_47; obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; obj* x_56; obj* x_57; 
x_47 = lean::cnstr_get(x_27, 1);
lean::inc(x_47);
lean::dec(x_27);
x_48 = lean::cnstr_get(x_28, 1);
lean::inc(x_48);
x_49 = lean::cnstr_get(x_28, 2);
lean::inc(x_49);
if (lean::is_exclusive(x_28)) {
 lean::cnstr_release(x_28, 0);
 lean::cnstr_release(x_28, 1);
 lean::cnstr_release(x_28, 2);
 x_50 = x_28;
} else {
 lean::dec_ref(x_28);
 x_50 = lean::box(0);
}
x_51 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_50)) {
 x_52 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_52 = x_50;
}
lean::cnstr_set(x_52, 0, x_9);
lean::cnstr_set(x_52, 1, x_48);
lean::cnstr_set(x_52, 2, x_51);
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_49, x_52);
x_54 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_53);
x_55 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_51, x_54);
x_56 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_55);
x_57 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_57, 0, x_56);
lean::cnstr_set(x_57, 1, x_47);
return x_57;
}
}
else
{
uint8 x_58; 
lean::dec(x_9);
x_58 = !lean::is_exclusive(x_27);
if (x_58 == 0)
{
obj* x_59; uint8 x_60; 
x_59 = lean::cnstr_get(x_27, 0);
lean::dec(x_59);
x_60 = !lean::is_exclusive(x_28);
if (x_60 == 0)
{
obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_61 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_28);
x_62 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_63 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_62, x_61);
x_64 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_63);
lean::cnstr_set(x_27, 0, x_64);
return x_27;
}
else
{
obj* x_65; uint8 x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; 
x_65 = lean::cnstr_get(x_28, 0);
x_66 = lean::cnstr_get_scalar<uint8>(x_28, sizeof(void*)*1);
lean::inc(x_65);
lean::dec(x_28);
x_67 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_67, 0, x_65);
lean::cnstr_set_scalar(x_67, sizeof(void*)*1, x_66);
x_68 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_67);
x_69 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_70 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_69, x_68);
x_71 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_70);
lean::cnstr_set(x_27, 0, x_71);
return x_27;
}
}
else
{
obj* x_72; obj* x_73; uint8 x_74; obj* x_75; obj* x_76; obj* x_77; obj* x_78; obj* x_79; obj* x_80; obj* x_81; 
x_72 = lean::cnstr_get(x_27, 1);
lean::inc(x_72);
lean::dec(x_27);
x_73 = lean::cnstr_get(x_28, 0);
lean::inc(x_73);
x_74 = lean::cnstr_get_scalar<uint8>(x_28, sizeof(void*)*1);
if (lean::is_exclusive(x_28)) {
 lean::cnstr_release(x_28, 0);
 x_75 = x_28;
} else {
 lean::dec_ref(x_28);
 x_75 = lean::box(0);
}
if (lean::is_scalar(x_75)) {
 x_76 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_76 = x_75;
}
lean::cnstr_set(x_76, 0, x_73);
lean::cnstr_set_scalar(x_76, sizeof(void*)*1, x_74);
x_77 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_11, x_76);
x_78 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_79 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_78, x_77);
x_80 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_79);
x_81 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_81, 0, x_80);
lean::cnstr_set(x_81, 1, x_72);
return x_81;
}
}
}
}
}
}
else
{
uint8 x_97; 
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
x_97 = !lean::is_exclusive(x_5);
if (x_97 == 0)
{
obj* x_98; uint8 x_99; 
x_98 = lean::cnstr_get(x_5, 0);
lean::dec(x_98);
x_99 = !lean::is_exclusive(x_6);
if (x_99 == 0)
{
obj* x_100; obj* x_101; obj* x_102; 
x_100 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_101 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_100, x_6);
x_102 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_101);
lean::cnstr_set(x_5, 0, x_102);
return x_5;
}
else
{
obj* x_103; uint8 x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; 
x_103 = lean::cnstr_get(x_6, 0);
x_104 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
lean::inc(x_103);
lean::dec(x_6);
x_105 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_105, 0, x_103);
lean::cnstr_set_scalar(x_105, sizeof(void*)*1, x_104);
x_106 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_107 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_106, x_105);
x_108 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_107);
lean::cnstr_set(x_5, 0, x_108);
return x_5;
}
}
else
{
obj* x_109; obj* x_110; uint8 x_111; obj* x_112; obj* x_113; obj* x_114; obj* x_115; obj* x_116; obj* x_117; 
x_109 = lean::cnstr_get(x_5, 1);
lean::inc(x_109);
lean::dec(x_5);
x_110 = lean::cnstr_get(x_6, 0);
lean::inc(x_110);
x_111 = lean::cnstr_get_scalar<uint8>(x_6, sizeof(void*)*1);
if (lean::is_exclusive(x_6)) {
 lean::cnstr_release(x_6, 0);
 x_112 = x_6;
} else {
 lean::dec_ref(x_6);
 x_112 = lean::box(0);
}
if (lean::is_scalar(x_112)) {
 x_113 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_113 = x_112;
}
lean::cnstr_set(x_113, 0, x_110);
lean::cnstr_set_scalar(x_113, sizeof(void*)*1, x_111);
x_114 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_115 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_114, x_113);
x_116 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_115);
x_117 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_117, 0, x_116);
lean::cnstr_set(x_117, 1, x_109);
return x_117;
}
}
}
}
obj* l_Lean_Parser_symbolOrIdent___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___rarg___lambda__1), 4, 1);
lean::closure_set(x_3, 0, x_2);
x_4 = lean::apply_2(x_1, lean::box(0), x_3);
return x_4;
}
}
obj* l_Lean_Parser_symbolOrIdent(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent___rarg), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_symbolOrIdent___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_symbolOrIdent(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_symbolOrIdent_tokens(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = lean::box(0);
return x_4;
}
}
obj* l_Lean_Parser_symbolOrIdent_tokens___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_symbolOrIdent_tokens(x_1, x_2, x_3);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_symbolOrIdent_View___rarg(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; obj* x_4; 
x_3 = l_mjoin___rarg___closed__1;
x_4 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_4, 0, x_3);
lean::cnstr_set(x_4, 1, x_3);
return x_4;
}
}
obj* l_Lean_Parser_symbolOrIdent_View(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolOrIdent_View___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Lean_Parser_symbolOrIdent_View___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_symbolOrIdent_View___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_symbolOrIdent_View___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_symbolOrIdent_View(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; obj* x_8; obj* x_9; 
lean::inc(x_1);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_7, 0, x_1);
lean::inc(x_5);
lean::inc(x_4);
x_8 = l_Lean_Parser_token(x_4, x_5, x_6);
x_9 = lean::cnstr_get(x_8, 0);
lean::inc(x_9);
if (lean::obj_tag(x_9) == 0)
{
uint8 x_10; 
x_10 = !lean::is_exclusive(x_8);
if (x_10 == 0)
{
obj* x_11; obj* x_12; uint8 x_13; 
x_11 = lean::cnstr_get(x_8, 1);
x_12 = lean::cnstr_get(x_8, 0);
lean::dec(x_12);
x_13 = !lean::is_exclusive(x_9);
if (x_13 == 0)
{
obj* x_14; obj* x_15; obj* x_16; obj* x_17; 
x_14 = lean::cnstr_get(x_9, 0);
x_15 = lean::cnstr_get(x_9, 1);
x_16 = lean::cnstr_get(x_9, 2);
if (lean::obj_tag(x_14) == 0)
{
obj* x_38; obj* x_39; uint8 x_40; 
x_38 = lean::cnstr_get(x_14, 0);
lean::inc(x_38);
x_39 = lean::cnstr_get(x_38, 1);
lean::inc(x_39);
lean::dec(x_38);
x_40 = lean::string_dec_eq(x_1, x_39);
lean::dec(x_1);
if (x_40 == 0)
{
obj* x_41; obj* x_42; obj* x_43; obj* x_44; 
lean::free_heap_obj(x_9);
lean::free_heap_obj(x_8);
x_41 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_41, 0, x_5);
x_42 = lean::box(0);
x_43 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_39, x_3, x_41, x_42, x_4, x_15, x_11);
lean::dec(x_4);
lean::dec(x_41);
x_44 = lean::cnstr_get(x_43, 0);
lean::inc(x_44);
if (lean::obj_tag(x_44) == 0)
{
uint8 x_45; 
x_45 = !lean::is_exclusive(x_43);
if (x_45 == 0)
{
obj* x_46; uint8 x_47; 
x_46 = lean::cnstr_get(x_43, 0);
lean::dec(x_46);
x_47 = !lean::is_exclusive(x_44);
if (x_47 == 0)
{
obj* x_48; obj* x_49; obj* x_50; obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
x_48 = lean::cnstr_get(x_44, 2);
x_49 = lean::cnstr_get(x_44, 0);
lean::dec(x_49);
x_50 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::cnstr_set(x_44, 2, x_50);
lean::cnstr_set(x_44, 0, x_14);
x_51 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_48, x_44);
x_52 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_51);
x_53 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_50, x_52);
x_54 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_53, x_7);
x_55 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_54);
lean::cnstr_set(x_43, 0, x_55);
return x_43;
}
else
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; obj* x_62; obj* x_63; obj* x_64; 
x_56 = lean::cnstr_get(x_44, 1);
x_57 = lean::cnstr_get(x_44, 2);
lean::inc(x_57);
lean::inc(x_56);
lean::dec(x_44);
x_58 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_59 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_59, 0, x_14);
lean::cnstr_set(x_59, 1, x_56);
lean::cnstr_set(x_59, 2, x_58);
x_60 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_57, x_59);
x_61 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_60);
x_62 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_58, x_61);
x_63 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_62, x_7);
x_64 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_63);
lean::cnstr_set(x_43, 0, x_64);
return x_43;
}
}
else
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; obj* x_69; obj* x_70; obj* x_71; obj* x_72; obj* x_73; obj* x_74; obj* x_75; obj* x_76; 
x_65 = lean::cnstr_get(x_43, 1);
lean::inc(x_65);
lean::dec(x_43);
x_66 = lean::cnstr_get(x_44, 1);
lean::inc(x_66);
x_67 = lean::cnstr_get(x_44, 2);
lean::inc(x_67);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 lean::cnstr_release(x_44, 1);
 lean::cnstr_release(x_44, 2);
 x_68 = x_44;
} else {
 lean::dec_ref(x_44);
 x_68 = lean::box(0);
}
x_69 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_68)) {
 x_70 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_70 = x_68;
}
lean::cnstr_set(x_70, 0, x_14);
lean::cnstr_set(x_70, 1, x_66);
lean::cnstr_set(x_70, 2, x_69);
x_71 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_67, x_70);
x_72 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_71);
x_73 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_69, x_72);
x_74 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_73, x_7);
x_75 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_74);
x_76 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_76, 0, x_75);
lean::cnstr_set(x_76, 1, x_65);
return x_76;
}
}
else
{
uint8 x_77; 
lean::dec(x_14);
x_77 = !lean::is_exclusive(x_43);
if (x_77 == 0)
{
obj* x_78; uint8 x_79; 
x_78 = lean::cnstr_get(x_43, 0);
lean::dec(x_78);
x_79 = !lean::is_exclusive(x_44);
if (x_79 == 0)
{
obj* x_80; obj* x_81; obj* x_82; obj* x_83; obj* x_84; 
x_80 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_44);
x_81 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_82 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_81, x_80);
x_83 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_82, x_7);
x_84 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_83);
lean::cnstr_set(x_43, 0, x_84);
return x_43;
}
else
{
obj* x_85; uint8 x_86; obj* x_87; obj* x_88; obj* x_89; obj* x_90; obj* x_91; obj* x_92; 
x_85 = lean::cnstr_get(x_44, 0);
x_86 = lean::cnstr_get_scalar<uint8>(x_44, sizeof(void*)*1);
lean::inc(x_85);
lean::dec(x_44);
x_87 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_87, 0, x_85);
lean::cnstr_set_scalar(x_87, sizeof(void*)*1, x_86);
x_88 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_87);
x_89 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_90 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_89, x_88);
x_91 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_90, x_7);
x_92 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_91);
lean::cnstr_set(x_43, 0, x_92);
return x_43;
}
}
else
{
obj* x_93; obj* x_94; uint8 x_95; obj* x_96; obj* x_97; obj* x_98; obj* x_99; obj* x_100; obj* x_101; obj* x_102; obj* x_103; 
x_93 = lean::cnstr_get(x_43, 1);
lean::inc(x_93);
lean::dec(x_43);
x_94 = lean::cnstr_get(x_44, 0);
lean::inc(x_94);
x_95 = lean::cnstr_get_scalar<uint8>(x_44, sizeof(void*)*1);
if (lean::is_exclusive(x_44)) {
 lean::cnstr_release(x_44, 0);
 x_96 = x_44;
} else {
 lean::dec_ref(x_44);
 x_96 = lean::box(0);
}
if (lean::is_scalar(x_96)) {
 x_97 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_97 = x_96;
}
lean::cnstr_set(x_97, 0, x_94);
lean::cnstr_set_scalar(x_97, sizeof(void*)*1, x_95);
x_98 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_97);
x_99 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_100 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_99, x_98);
x_101 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_100, x_7);
x_102 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_101);
x_103 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_103, 0, x_102);
lean::cnstr_set(x_103, 1, x_93);
return x_103;
}
}
}
else
{
obj* x_104; obj* x_105; obj* x_106; obj* x_107; obj* x_108; obj* x_109; 
lean::dec(x_39);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_104 = l_Lean_Parser_finishCommentBlock___closed__2;
lean::cnstr_set(x_9, 2, x_104);
x_105 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_9);
x_106 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_107 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_106, x_105);
x_108 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_107, x_7);
x_109 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_108);
lean::cnstr_set(x_8, 0, x_109);
return x_8;
}
}
else
{
obj* x_110; 
lean::free_heap_obj(x_9);
lean::dec(x_14);
lean::free_heap_obj(x_8);
lean::dec(x_1);
x_110 = lean::box(0);
x_17 = x_110;
goto block_37;
}
block_37:
{
obj* x_18; obj* x_19; obj* x_20; obj* x_21; uint8 x_22; 
lean::dec(x_17);
x_18 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_18, 0, x_5);
x_19 = lean::box(0);
x_20 = l_String_splitAux___main___closed__1;
x_21 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_20, x_3, x_18, x_19, x_4, x_15, x_11);
lean::dec(x_4);
lean::dec(x_18);
x_22 = !lean::is_exclusive(x_21);
if (x_22 == 0)
{
obj* x_23; obj* x_24; obj* x_25; obj* x_26; obj* x_27; obj* x_28; 
x_23 = lean::cnstr_get(x_21, 0);
x_24 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_23);
x_25 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_26 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_25, x_24);
x_27 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_26, x_7);
x_28 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_27);
lean::cnstr_set(x_21, 0, x_28);
return x_21;
}
else
{
obj* x_29; obj* x_30; obj* x_31; obj* x_32; obj* x_33; obj* x_34; obj* x_35; obj* x_36; 
x_29 = lean::cnstr_get(x_21, 0);
x_30 = lean::cnstr_get(x_21, 1);
lean::inc(x_30);
lean::inc(x_29);
lean::dec(x_21);
x_31 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_16, x_29);
x_32 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_33 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_32, x_31);
x_34 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_33, x_7);
x_35 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_34);
x_36 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_36, 0, x_35);
lean::cnstr_set(x_36, 1, x_30);
return x_36;
}
}
}
else
{
obj* x_111; obj* x_112; obj* x_113; obj* x_114; 
x_111 = lean::cnstr_get(x_9, 0);
x_112 = lean::cnstr_get(x_9, 1);
x_113 = lean::cnstr_get(x_9, 2);
lean::inc(x_113);
lean::inc(x_112);
lean::inc(x_111);
lean::dec(x_9);
if (lean::obj_tag(x_111) == 0)
{
obj* x_129; obj* x_130; uint8 x_131; 
x_129 = lean::cnstr_get(x_111, 0);
lean::inc(x_129);
x_130 = lean::cnstr_get(x_129, 1);
lean::inc(x_130);
lean::dec(x_129);
x_131 = lean::string_dec_eq(x_1, x_130);
lean::dec(x_1);
if (x_131 == 0)
{
obj* x_132; obj* x_133; obj* x_134; obj* x_135; 
lean::free_heap_obj(x_8);
x_132 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_132, 0, x_5);
x_133 = lean::box(0);
x_134 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_130, x_3, x_132, x_133, x_4, x_112, x_11);
lean::dec(x_4);
lean::dec(x_132);
x_135 = lean::cnstr_get(x_134, 0);
lean::inc(x_135);
if (lean::obj_tag(x_135) == 0)
{
obj* x_136; obj* x_137; obj* x_138; obj* x_139; obj* x_140; obj* x_141; obj* x_142; obj* x_143; obj* x_144; obj* x_145; obj* x_146; obj* x_147; obj* x_148; 
x_136 = lean::cnstr_get(x_134, 1);
lean::inc(x_136);
if (lean::is_exclusive(x_134)) {
 lean::cnstr_release(x_134, 0);
 lean::cnstr_release(x_134, 1);
 x_137 = x_134;
} else {
 lean::dec_ref(x_134);
 x_137 = lean::box(0);
}
x_138 = lean::cnstr_get(x_135, 1);
lean::inc(x_138);
x_139 = lean::cnstr_get(x_135, 2);
lean::inc(x_139);
if (lean::is_exclusive(x_135)) {
 lean::cnstr_release(x_135, 0);
 lean::cnstr_release(x_135, 1);
 lean::cnstr_release(x_135, 2);
 x_140 = x_135;
} else {
 lean::dec_ref(x_135);
 x_140 = lean::box(0);
}
x_141 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_140)) {
 x_142 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_142 = x_140;
}
lean::cnstr_set(x_142, 0, x_111);
lean::cnstr_set(x_142, 1, x_138);
lean::cnstr_set(x_142, 2, x_141);
x_143 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_139, x_142);
x_144 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_113, x_143);
x_145 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_141, x_144);
x_146 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_145, x_7);
x_147 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_146);
if (lean::is_scalar(x_137)) {
 x_148 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_148 = x_137;
}
lean::cnstr_set(x_148, 0, x_147);
lean::cnstr_set(x_148, 1, x_136);
return x_148;
}
else
{
obj* x_149; obj* x_150; obj* x_151; uint8 x_152; obj* x_153; obj* x_154; obj* x_155; obj* x_156; obj* x_157; obj* x_158; obj* x_159; obj* x_160; 
lean::dec(x_111);
x_149 = lean::cnstr_get(x_134, 1);
lean::inc(x_149);
if (lean::is_exclusive(x_134)) {
 lean::cnstr_release(x_134, 0);
 lean::cnstr_release(x_134, 1);
 x_150 = x_134;
} else {
 lean::dec_ref(x_134);
 x_150 = lean::box(0);
}
x_151 = lean::cnstr_get(x_135, 0);
lean::inc(x_151);
x_152 = lean::cnstr_get_scalar<uint8>(x_135, sizeof(void*)*1);
if (lean::is_exclusive(x_135)) {
 lean::cnstr_release(x_135, 0);
 x_153 = x_135;
} else {
 lean::dec_ref(x_135);
 x_153 = lean::box(0);
}
if (lean::is_scalar(x_153)) {
 x_154 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_154 = x_153;
}
lean::cnstr_set(x_154, 0, x_151);
lean::cnstr_set_scalar(x_154, sizeof(void*)*1, x_152);
x_155 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_113, x_154);
x_156 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_157 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_156, x_155);
x_158 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_157, x_7);
x_159 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_158);
if (lean::is_scalar(x_150)) {
 x_160 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_160 = x_150;
}
lean::cnstr_set(x_160, 0, x_159);
lean::cnstr_set(x_160, 1, x_149);
return x_160;
}
}
else
{
obj* x_161; obj* x_162; obj* x_163; obj* x_164; obj* x_165; obj* x_166; obj* x_167; 
lean::dec(x_130);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_161 = l_Lean_Parser_finishCommentBlock___closed__2;
x_162 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_162, 0, x_111);
lean::cnstr_set(x_162, 1, x_112);
lean::cnstr_set(x_162, 2, x_161);
x_163 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_113, x_162);
x_164 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_165 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_164, x_163);
x_166 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_165, x_7);
x_167 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_166);
lean::cnstr_set(x_8, 0, x_167);
return x_8;
}
}
else
{
obj* x_168; 
lean::dec(x_111);
lean::free_heap_obj(x_8);
lean::dec(x_1);
x_168 = lean::box(0);
x_114 = x_168;
goto block_128;
}
block_128:
{
obj* x_115; obj* x_116; obj* x_117; obj* x_118; obj* x_119; obj* x_120; obj* x_121; obj* x_122; obj* x_123; obj* x_124; obj* x_125; obj* x_126; obj* x_127; 
lean::dec(x_114);
x_115 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_115, 0, x_5);
x_116 = lean::box(0);
x_117 = l_String_splitAux___main___closed__1;
x_118 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_117, x_3, x_115, x_116, x_4, x_112, x_11);
lean::dec(x_4);
lean::dec(x_115);
x_119 = lean::cnstr_get(x_118, 0);
lean::inc(x_119);
x_120 = lean::cnstr_get(x_118, 1);
lean::inc(x_120);
if (lean::is_exclusive(x_118)) {
 lean::cnstr_release(x_118, 0);
 lean::cnstr_release(x_118, 1);
 x_121 = x_118;
} else {
 lean::dec_ref(x_118);
 x_121 = lean::box(0);
}
x_122 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_113, x_119);
x_123 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_124 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_123, x_122);
x_125 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_124, x_7);
x_126 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_125);
if (lean::is_scalar(x_121)) {
 x_127 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_127 = x_121;
}
lean::cnstr_set(x_127, 0, x_126);
lean::cnstr_set(x_127, 1, x_120);
return x_127;
}
}
}
else
{
obj* x_169; obj* x_170; obj* x_171; obj* x_172; obj* x_173; obj* x_174; 
x_169 = lean::cnstr_get(x_8, 1);
lean::inc(x_169);
lean::dec(x_8);
x_170 = lean::cnstr_get(x_9, 0);
lean::inc(x_170);
x_171 = lean::cnstr_get(x_9, 1);
lean::inc(x_171);
x_172 = lean::cnstr_get(x_9, 2);
lean::inc(x_172);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 lean::cnstr_release(x_9, 1);
 lean::cnstr_release(x_9, 2);
 x_173 = x_9;
} else {
 lean::dec_ref(x_9);
 x_173 = lean::box(0);
}
if (lean::obj_tag(x_170) == 0)
{
obj* x_189; obj* x_190; uint8 x_191; 
x_189 = lean::cnstr_get(x_170, 0);
lean::inc(x_189);
x_190 = lean::cnstr_get(x_189, 1);
lean::inc(x_190);
lean::dec(x_189);
x_191 = lean::string_dec_eq(x_1, x_190);
lean::dec(x_1);
if (x_191 == 0)
{
obj* x_192; obj* x_193; obj* x_194; obj* x_195; 
lean::dec(x_173);
x_192 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_192, 0, x_5);
x_193 = lean::box(0);
x_194 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_190, x_3, x_192, x_193, x_4, x_171, x_169);
lean::dec(x_4);
lean::dec(x_192);
x_195 = lean::cnstr_get(x_194, 0);
lean::inc(x_195);
if (lean::obj_tag(x_195) == 0)
{
obj* x_196; obj* x_197; obj* x_198; obj* x_199; obj* x_200; obj* x_201; obj* x_202; obj* x_203; obj* x_204; obj* x_205; obj* x_206; obj* x_207; obj* x_208; 
x_196 = lean::cnstr_get(x_194, 1);
lean::inc(x_196);
if (lean::is_exclusive(x_194)) {
 lean::cnstr_release(x_194, 0);
 lean::cnstr_release(x_194, 1);
 x_197 = x_194;
} else {
 lean::dec_ref(x_194);
 x_197 = lean::box(0);
}
x_198 = lean::cnstr_get(x_195, 1);
lean::inc(x_198);
x_199 = lean::cnstr_get(x_195, 2);
lean::inc(x_199);
if (lean::is_exclusive(x_195)) {
 lean::cnstr_release(x_195, 0);
 lean::cnstr_release(x_195, 1);
 lean::cnstr_release(x_195, 2);
 x_200 = x_195;
} else {
 lean::dec_ref(x_195);
 x_200 = lean::box(0);
}
x_201 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
if (lean::is_scalar(x_200)) {
 x_202 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_202 = x_200;
}
lean::cnstr_set(x_202, 0, x_170);
lean::cnstr_set(x_202, 1, x_198);
lean::cnstr_set(x_202, 2, x_201);
x_203 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_199, x_202);
x_204 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_172, x_203);
x_205 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_201, x_204);
x_206 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_205, x_7);
x_207 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_206);
if (lean::is_scalar(x_197)) {
 x_208 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_208 = x_197;
}
lean::cnstr_set(x_208, 0, x_207);
lean::cnstr_set(x_208, 1, x_196);
return x_208;
}
else
{
obj* x_209; obj* x_210; obj* x_211; uint8 x_212; obj* x_213; obj* x_214; obj* x_215; obj* x_216; obj* x_217; obj* x_218; obj* x_219; obj* x_220; 
lean::dec(x_170);
x_209 = lean::cnstr_get(x_194, 1);
lean::inc(x_209);
if (lean::is_exclusive(x_194)) {
 lean::cnstr_release(x_194, 0);
 lean::cnstr_release(x_194, 1);
 x_210 = x_194;
} else {
 lean::dec_ref(x_194);
 x_210 = lean::box(0);
}
x_211 = lean::cnstr_get(x_195, 0);
lean::inc(x_211);
x_212 = lean::cnstr_get_scalar<uint8>(x_195, sizeof(void*)*1);
if (lean::is_exclusive(x_195)) {
 lean::cnstr_release(x_195, 0);
 x_213 = x_195;
} else {
 lean::dec_ref(x_195);
 x_213 = lean::box(0);
}
if (lean::is_scalar(x_213)) {
 x_214 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_214 = x_213;
}
lean::cnstr_set(x_214, 0, x_211);
lean::cnstr_set_scalar(x_214, sizeof(void*)*1, x_212);
x_215 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_172, x_214);
x_216 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_217 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_216, x_215);
x_218 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_217, x_7);
x_219 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_218);
if (lean::is_scalar(x_210)) {
 x_220 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_220 = x_210;
}
lean::cnstr_set(x_220, 0, x_219);
lean::cnstr_set(x_220, 1, x_209);
return x_220;
}
}
else
{
obj* x_221; obj* x_222; obj* x_223; obj* x_224; obj* x_225; obj* x_226; obj* x_227; obj* x_228; 
lean::dec(x_190);
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
x_221 = l_Lean_Parser_finishCommentBlock___closed__2;
if (lean::is_scalar(x_173)) {
 x_222 = lean::alloc_cnstr(0, 3, 0);
} else {
 x_222 = x_173;
}
lean::cnstr_set(x_222, 0, x_170);
lean::cnstr_set(x_222, 1, x_171);
lean::cnstr_set(x_222, 2, x_221);
x_223 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_172, x_222);
x_224 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_225 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_224, x_223);
x_226 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_225, x_7);
x_227 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_226);
x_228 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_228, 0, x_227);
lean::cnstr_set(x_228, 1, x_169);
return x_228;
}
}
else
{
obj* x_229; 
lean::dec(x_173);
lean::dec(x_170);
lean::dec(x_1);
x_229 = lean::box(0);
x_174 = x_229;
goto block_188;
}
block_188:
{
obj* x_175; obj* x_176; obj* x_177; obj* x_178; obj* x_179; obj* x_180; obj* x_181; obj* x_182; obj* x_183; obj* x_184; obj* x_185; obj* x_186; obj* x_187; 
lean::dec(x_174);
x_175 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_175, 0, x_5);
x_176 = lean::box(0);
x_177 = l_String_splitAux___main___closed__1;
x_178 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_177, x_3, x_175, x_176, x_4, x_171, x_169);
lean::dec(x_4);
lean::dec(x_175);
x_179 = lean::cnstr_get(x_178, 0);
lean::inc(x_179);
x_180 = lean::cnstr_get(x_178, 1);
lean::inc(x_180);
if (lean::is_exclusive(x_178)) {
 lean::cnstr_release(x_178, 0);
 lean::cnstr_release(x_178, 1);
 x_181 = x_178;
} else {
 lean::dec_ref(x_178);
 x_181 = lean::box(0);
}
x_182 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_172, x_179);
x_183 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_184 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_183, x_182);
x_185 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_184, x_7);
x_186 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_185);
if (lean::is_scalar(x_181)) {
 x_187 = lean::alloc_cnstr(0, 2, 0);
} else {
 x_187 = x_181;
}
lean::cnstr_set(x_187, 0, x_186);
lean::cnstr_set(x_187, 1, x_180);
return x_187;
}
}
}
else
{
uint8 x_230; 
lean::dec(x_5);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_1);
x_230 = !lean::is_exclusive(x_8);
if (x_230 == 0)
{
obj* x_231; uint8 x_232; 
x_231 = lean::cnstr_get(x_8, 0);
lean::dec(x_231);
x_232 = !lean::is_exclusive(x_9);
if (x_232 == 0)
{
obj* x_233; obj* x_234; obj* x_235; obj* x_236; 
x_233 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_234 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_233, x_9);
x_235 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_234, x_7);
x_236 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_235);
lean::cnstr_set(x_8, 0, x_236);
return x_8;
}
else
{
obj* x_237; uint8 x_238; obj* x_239; obj* x_240; obj* x_241; obj* x_242; obj* x_243; 
x_237 = lean::cnstr_get(x_9, 0);
x_238 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
lean::inc(x_237);
lean::dec(x_9);
x_239 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_239, 0, x_237);
lean::cnstr_set_scalar(x_239, sizeof(void*)*1, x_238);
x_240 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_241 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_240, x_239);
x_242 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_241, x_7);
x_243 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_242);
lean::cnstr_set(x_8, 0, x_243);
return x_8;
}
}
else
{
obj* x_244; obj* x_245; uint8 x_246; obj* x_247; obj* x_248; obj* x_249; obj* x_250; obj* x_251; obj* x_252; obj* x_253; 
x_244 = lean::cnstr_get(x_8, 1);
lean::inc(x_244);
lean::dec(x_8);
x_245 = lean::cnstr_get(x_9, 0);
lean::inc(x_245);
x_246 = lean::cnstr_get_scalar<uint8>(x_9, sizeof(void*)*1);
if (lean::is_exclusive(x_9)) {
 lean::cnstr_release(x_9, 0);
 x_247 = x_9;
} else {
 lean::dec_ref(x_9);
 x_247 = lean::box(0);
}
if (lean::is_scalar(x_247)) {
 x_248 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_248 = x_247;
}
lean::cnstr_set(x_248, 0, x_245);
lean::cnstr_set_scalar(x_248, sizeof(void*)*1, x_246);
x_249 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_250 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_249, x_248);
x_251 = l_Lean_Parser_ParsecT_labelsMkRes___rarg(x_250, x_7);
x_252 = l_Lean_Parser_ParsecT_tryMkRes___rarg(x_251);
x_253 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_253, 0, x_252);
lean::cnstr_set(x_253, 1, x_244);
return x_253;
}
}
}
}
obj* l_List_foldl___main___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__3(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; 
lean::dec(x_2);
x_6 = lean::apply_3(x_1, x_3, x_4, x_5);
return x_6;
}
else
{
obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
x_7 = lean::cnstr_get(x_2, 0);
lean::inc(x_7);
x_8 = lean::cnstr_get(x_2, 1);
lean::inc(x_8);
lean::dec(x_2);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_orelse___at_Lean_Parser_parseBinLit___spec__1___rarg), 5, 2);
lean::closure_set(x_9, 0, x_1);
lean::closure_set(x_9, 1, x_7);
x_1 = x_9;
x_2 = x_8;
goto _start;
}
}
}
obj* l_Lean_Parser_Combinators_anyOf___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__2(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; 
lean::dec(x_1);
x_5 = lean::box(0);
x_6 = l_Lean_Parser_Combinators_anyOf___rarg___closed__1;
x_7 = l_mjoin___rarg___closed__1;
x_8 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_6, x_7, x_5, x_5, x_2, x_3, x_4);
lean::dec(x_2);
return x_8;
}
else
{
obj* x_9; obj* x_10; obj* x_11; 
x_9 = lean::cnstr_get(x_1, 0);
lean::inc(x_9);
x_10 = lean::cnstr_get(x_1, 1);
lean::inc(x_10);
lean::dec(x_1);
x_11 = l_List_foldl___main___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__3(x_9, x_10, x_2, x_3, x_4);
return x_11;
}
}
}
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; 
lean::inc(x_3);
x_4 = l_Lean_Parser_symbol_tokens___rarg(x_1, x_3);
x_5 = l_Lean_Parser_symbol_tokens___rarg(x_2, x_3);
x_6 = lean::box(0);
x_7 = l_Lean_Parser_List_cons_tokens___rarg(x_5, x_6);
lean::dec(x_5);
x_8 = l_Lean_Parser_List_cons_tokens___rarg(x_4, x_7);
lean::dec(x_7);
lean::dec(x_4);
x_9 = l_Lean_Parser_tokens___rarg(x_8);
lean::dec(x_8);
x_10 = l_Lean_Parser_tokens___rarg(x_9);
lean::dec(x_9);
return x_10;
}
}
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___rarg___boxed), 3, 0);
return x_3;
}
}
obj* l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5, obj* x_6) {
_start:
{
obj* x_7; 
x_7 = l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1(x_1, x_2, x_3, x_4, x_5, x_6);
lean::dec(x_2);
return x_7;
}
}
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___rarg___boxed(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; 
x_4 = l_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___rarg(x_1, x_2, x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_4;
}
}
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasView___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; obj* x_17; obj* x_18; 
x_5 = l_String_trim(x_2);
lean::inc(x_5);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
lean::inc(x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1___boxed), 6, 3);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_4);
lean::closure_set(x_7, 2, x_6);
x_8 = l_String_trim(x_3);
lean::inc(x_8);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1___boxed), 6, 3);
lean::closure_set(x_10, 0, x_8);
lean::closure_set(x_10, 1, x_4);
lean::closure_set(x_10, 2, x_9);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_7);
lean::cnstr_set(x_13, 1, x_12);
lean::inc(x_13);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_anyOf___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__2), 4, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = l_Lean_Parser_BasicParserM_Lean_Parser_MonadParsec;
x_16 = l_Lean_Parser_BasicParserM_Alternative;
x_17 = l_Lean_Parser_Combinators_anyOf_view___rarg(x_15, x_16, x_13);
lean::dec(x_13);
x_18 = l_Lean_Parser_Combinators_monadLift_view___rarg(x_1, x_14, x_17);
lean::dec(x_14);
return x_18;
}
}
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasView(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_unicodeSymbol_Lean_Parser_HasView___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasView___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_unicodeSymbol_Lean_Parser_HasView___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_unicodeSymbol_Lean_Parser_HasView___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_unicodeSymbol_Lean_Parser_HasView(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_unicodeSymbol___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; obj* x_6; obj* x_7; obj* x_8; obj* x_9; obj* x_10; obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; 
x_5 = l_String_trim(x_2);
lean::inc(x_5);
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_6, 0, x_5);
lean::inc(x_4);
x_7 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1___boxed), 6, 3);
lean::closure_set(x_7, 0, x_5);
lean::closure_set(x_7, 1, x_4);
lean::closure_set(x_7, 2, x_6);
x_8 = l_String_trim(x_3);
lean::inc(x_8);
x_9 = lean::alloc_closure(reinterpret_cast<void*>(l_DList_singleton___elambda__1___rarg), 2, 1);
lean::closure_set(x_9, 0, x_8);
x_10 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_symbolCore___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__1___boxed), 6, 3);
lean::closure_set(x_10, 0, x_8);
lean::closure_set(x_10, 1, x_4);
lean::closure_set(x_10, 2, x_9);
x_11 = lean::box(0);
x_12 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_12, 0, x_10);
lean::cnstr_set(x_12, 1, x_11);
x_13 = lean::alloc_cnstr(1, 2, 0);
lean::cnstr_set(x_13, 0, x_7);
lean::cnstr_set(x_13, 1, x_12);
x_14 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_Combinators_anyOf___at_Lean_Parser_unicodeSymbol_Lean_Parser_HasTokens___spec__2), 4, 1);
lean::closure_set(x_14, 0, x_13);
x_15 = lean::apply_2(x_1, lean::box(0), x_14);
return x_15;
}
}
obj* l_Lean_Parser_unicodeSymbol(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_unicodeSymbol___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Lean_Parser_unicodeSymbol___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_unicodeSymbol___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_3);
lean::dec(x_2);
return x_5;
}
}
obj* l_Lean_Parser_unicodeSymbol___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_unicodeSymbol(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_Lean_Parser_unicodeSymbol_viewDefault___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = lean::box(0);
return x_5;
}
}
obj* l_Lean_Parser_unicodeSymbol_viewDefault(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_unicodeSymbol_viewDefault___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_Lean_Parser_unicodeSymbol_viewDefault___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Lean_Parser_unicodeSymbol_viewDefault___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_4);
lean::dec(x_3);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_Lean_Parser_unicodeSymbol_viewDefault___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_unicodeSymbol_viewDefault(x_1);
lean::dec(x_1);
return x_2;
}
}
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::cnstr_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
obj* x_10; 
lean::inc(x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_6);
return x_10;
}
else
{
obj* x_11; 
x_1 = x_7;
goto _start;
}
}
else
{
obj* x_12; 
x_1 = x_4;
goto _start;
}
}
}
}
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__1(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2___rarg(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_5; 
x_5 = l_Lean_Parser_ParsecT_failure___at_Lean_Parser_token___spec__4___rarg(x_3, x_4);
return x_5;
}
else
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
x_6 = lean::cnstr_get(x_1, 0);
x_7 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
lean::inc(x_6);
x_8 = lean::alloc_cnstr(0, 3, 0);
lean::cnstr_set(x_8, 0, x_6);
lean::cnstr_set(x_8, 1, x_3);
lean::cnstr_set(x_8, 2, x_7);
x_9 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_9, 0, x_8);
lean::cnstr_set(x_9, 1, x_4);
return x_9;
}
}
}
obj* l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2___rarg___boxed), 4, 0);
return x_2;
}
}
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__3___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::cnstr_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
obj* x_10; 
lean::inc(x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_6);
return x_10;
}
else
{
obj* x_11; 
x_1 = x_7;
goto _start;
}
}
else
{
obj* x_12; 
x_1 = x_4;
goto _start;
}
}
}
}
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__3(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___main___at_Lean_Parser_indexed___spec__3___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__4___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::cnstr_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
obj* x_10; 
lean::inc(x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_6);
return x_10;
}
else
{
obj* x_11; 
x_1 = x_7;
goto _start;
}
}
else
{
obj* x_12; 
x_1 = x_4;
goto _start;
}
}
}
}
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__4(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___main___at_Lean_Parser_indexed___spec__4___rarg___boxed), 2, 0);
return x_2;
}
}
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__5___rarg(obj* x_1, obj* x_2) {
_start:
{
if (lean::obj_tag(x_1) == 0)
{
obj* x_3; 
x_3 = lean::box(0);
return x_3;
}
else
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; uint8 x_8; 
x_4 = lean::cnstr_get(x_1, 0);
x_5 = lean::cnstr_get(x_1, 1);
x_6 = lean::cnstr_get(x_1, 2);
x_7 = lean::cnstr_get(x_1, 3);
x_8 = l_Lean_Name_quickLt(x_2, x_5);
if (x_8 == 0)
{
uint8 x_9; 
x_9 = l_Lean_Name_quickLt(x_5, x_2);
if (x_9 == 0)
{
obj* x_10; 
lean::inc(x_6);
x_10 = lean::alloc_cnstr(1, 1, 0);
lean::cnstr_set(x_10, 0, x_6);
return x_10;
}
else
{
obj* x_11; 
x_1 = x_7;
goto _start;
}
}
else
{
obj* x_12; 
x_1 = x_4;
goto _start;
}
}
}
}
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__5(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_RBNode_find___main___at_Lean_Parser_indexed___spec__5___rarg___boxed), 2, 0);
return x_2;
}
}
obj* _init_l_Lean_Parser_indexed___rarg___lambda__1___closed__1() {
_start:
{
obj* x_1; obj* x_2; obj* x_3; 
x_1 = lean::box(0);
x_2 = lean::mk_string("ident");
x_3 = lean_name_mk_string(x_1, x_2);
return x_3;
}
}
obj* l_Lean_Parser_indexed___rarg___lambda__1(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
if (lean::obj_tag(x_2) == 0)
{
obj* x_6; obj* x_7; obj* x_8; obj* x_9; 
lean::dec(x_2);
x_6 = lean::box(0);
x_7 = l_String_splitAux___main___closed__1;
x_8 = l_mjoin___rarg___closed__1;
x_9 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_7, x_8, x_6, x_6, x_3, x_4, x_5);
return x_9;
}
else
{
obj* x_10; 
x_10 = lean::cnstr_get(x_2, 0);
lean::inc(x_10);
lean::dec(x_2);
switch (lean::obj_tag(x_10)) {
case 0:
{
obj* x_11; obj* x_12; obj* x_13; obj* x_14; obj* x_15; obj* x_16; uint8 x_17; 
x_11 = lean::cnstr_get(x_10, 0);
lean::inc(x_11);
lean::dec(x_10);
x_12 = lean::cnstr_get(x_11, 1);
lean::inc(x_12);
lean::dec(x_11);
x_13 = lean::box(0);
x_14 = lean_name_mk_string(x_13, x_12);
x_15 = l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg(x_1, x_14);
lean::dec(x_14);
x_16 = l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2___rarg(x_15, x_3, x_4, x_5);
lean::dec(x_15);
x_17 = !lean::is_exclusive(x_16);
if (x_17 == 0)
{
obj* x_18; obj* x_19; obj* x_20; 
x_18 = lean::cnstr_get(x_16, 0);
x_19 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_20 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_19, x_18);
lean::cnstr_set(x_16, 0, x_20);
return x_16;
}
else
{
obj* x_21; obj* x_22; obj* x_23; obj* x_24; obj* x_25; 
x_21 = lean::cnstr_get(x_16, 0);
x_22 = lean::cnstr_get(x_16, 1);
lean::inc(x_22);
lean::inc(x_21);
lean::dec(x_16);
x_23 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_24 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_23, x_21);
x_25 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_25, 0, x_24);
lean::cnstr_set(x_25, 1, x_22);
return x_25;
}
}
case 1:
{
obj* x_26; obj* x_27; obj* x_28; uint8 x_29; 
lean::dec(x_10);
x_26 = l_Lean_Parser_indexed___rarg___lambda__1___closed__1;
x_27 = l_RBNode_find___main___at_Lean_Parser_indexed___spec__3___rarg(x_1, x_26);
x_28 = l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2___rarg(x_27, x_3, x_4, x_5);
lean::dec(x_27);
x_29 = !lean::is_exclusive(x_28);
if (x_29 == 0)
{
obj* x_30; obj* x_31; obj* x_32; 
x_30 = lean::cnstr_get(x_28, 0);
x_31 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_32 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_31, x_30);
lean::cnstr_set(x_28, 0, x_32);
return x_28;
}
else
{
obj* x_33; obj* x_34; obj* x_35; obj* x_36; obj* x_37; 
x_33 = lean::cnstr_get(x_28, 0);
x_34 = lean::cnstr_get(x_28, 1);
lean::inc(x_34);
lean::inc(x_33);
lean::dec(x_28);
x_35 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_36 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_35, x_33);
x_37 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_37, 0, x_36);
lean::cnstr_set(x_37, 1, x_34);
return x_37;
}
}
case 2:
{
obj* x_38; obj* x_39; obj* x_40; obj* x_41; uint8 x_42; 
x_38 = lean::cnstr_get(x_10, 0);
lean::inc(x_38);
lean::dec(x_10);
x_39 = lean::cnstr_get(x_38, 0);
lean::inc(x_39);
lean::dec(x_38);
x_40 = l_RBNode_find___main___at_Lean_Parser_indexed___spec__4___rarg(x_1, x_39);
lean::dec(x_39);
x_41 = l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2___rarg(x_40, x_3, x_4, x_5);
lean::dec(x_40);
x_42 = !lean::is_exclusive(x_41);
if (x_42 == 0)
{
obj* x_43; obj* x_44; obj* x_45; 
x_43 = lean::cnstr_get(x_41, 0);
x_44 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_45 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_44, x_43);
lean::cnstr_set(x_41, 0, x_45);
return x_41;
}
else
{
obj* x_46; obj* x_47; obj* x_48; obj* x_49; obj* x_50; 
x_46 = lean::cnstr_get(x_41, 0);
x_47 = lean::cnstr_get(x_41, 1);
lean::inc(x_47);
lean::inc(x_46);
lean::dec(x_41);
x_48 = l_Lean_Parser_Parsec_Result_mkEps___rarg___closed__1;
x_49 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_48, x_46);
x_50 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_50, 0, x_49);
lean::cnstr_set(x_50, 1, x_47);
return x_50;
}
}
default: 
{
obj* x_51; obj* x_52; obj* x_53; obj* x_54; obj* x_55; 
lean::dec(x_10);
x_51 = lean::box(0);
x_52 = l_String_splitAux___main___closed__1;
x_53 = l_mjoin___rarg___closed__1;
x_54 = l_Lean_Parser_MonadParsec_error___at___private_init_lean_parser_token_1__finishCommentBlockAux___main___spec__1___rarg(x_52, x_53, x_51, x_51, x_3, x_4, x_5);
x_55 = lean::cnstr_get(x_54, 0);
lean::inc(x_55);
if (lean::obj_tag(x_55) == 0)
{
obj* x_56; obj* x_57; obj* x_58; obj* x_59; obj* x_60; obj* x_61; uint8 x_62; 
x_56 = lean::cnstr_get(x_54, 1);
lean::inc(x_56);
lean::dec(x_54);
x_57 = lean::cnstr_get(x_55, 0);
lean::inc(x_57);
x_58 = lean::cnstr_get(x_55, 1);
lean::inc(x_58);
x_59 = lean::cnstr_get(x_55, 2);
lean::inc(x_59);
lean::dec(x_55);
x_60 = l_RBNode_find___main___at_Lean_Parser_indexed___spec__5___rarg(x_1, x_57);
lean::dec(x_57);
x_61 = l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2___rarg(x_60, x_3, x_58, x_56);
lean::dec(x_60);
x_62 = !lean::is_exclusive(x_61);
if (x_62 == 0)
{
obj* x_63; obj* x_64; 
x_63 = lean::cnstr_get(x_61, 0);
x_64 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_59, x_63);
lean::cnstr_set(x_61, 0, x_64);
return x_61;
}
else
{
obj* x_65; obj* x_66; obj* x_67; obj* x_68; 
x_65 = lean::cnstr_get(x_61, 0);
x_66 = lean::cnstr_get(x_61, 1);
lean::inc(x_66);
lean::inc(x_65);
lean::dec(x_61);
x_67 = l_Lean_Parser_ParsecT_bindMkRes___rarg(x_59, x_65);
x_68 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_68, 0, x_67);
lean::cnstr_set(x_68, 1, x_66);
return x_68;
}
}
else
{
uint8 x_69; 
x_69 = !lean::is_exclusive(x_54);
if (x_69 == 0)
{
obj* x_70; uint8 x_71; 
x_70 = lean::cnstr_get(x_54, 0);
lean::dec(x_70);
x_71 = !lean::is_exclusive(x_55);
if (x_71 == 0)
{
return x_54;
}
else
{
obj* x_72; uint8 x_73; obj* x_74; 
x_72 = lean::cnstr_get(x_55, 0);
x_73 = lean::cnstr_get_scalar<uint8>(x_55, sizeof(void*)*1);
lean::inc(x_72);
lean::dec(x_55);
x_74 = lean::alloc_cnstr(1, 1, 1);
lean::cnstr_set(x_74, 0, x_72);
lean::cnstr_set_scalar(x_74, sizeof(void*)*1, x_73);
lean::cnstr_set(x_54, 0, x_74);
return x_54;
}
}
else
{
obj* x_75; obj* x_76; uint8 x_77; obj* x_78; obj* x_79; obj* x_80; 
x_75 = lean::cnstr_get(x_54, 1);
lean::inc(x_75);
lean::dec(x_54);
x_76 = lean::cnstr_get(x_55, 0);
lean::inc(x_76);
x_77 = lean::cnstr_get_scalar<uint8>(x_55, sizeof(void*)*1);
if (lean::is_exclusive(x_55)) {
 lean::cnstr_release(x_55, 0);
 x_78 = x_55;
} else {
 lean::dec_ref(x_55);
 x_78 = lean::box(0);
}
if (lean::is_scalar(x_78)) {
 x_79 = lean::alloc_cnstr(1, 1, 1);
} else {
 x_79 = x_78;
}
lean::cnstr_set(x_79, 0, x_76);
lean::cnstr_set_scalar(x_79, sizeof(void*)*1, x_77);
x_80 = lean::alloc_cnstr(0, 2, 0);
lean::cnstr_set(x_80, 0, x_79);
lean::cnstr_set(x_80, 1, x_75);
return x_80;
}
}
}
}
}
}
}
obj* _init_l_Lean_Parser_indexed___rarg___closed__1() {
_start:
{
obj* x_1; 
x_1 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_peekToken), 3, 0);
return x_1;
}
}
obj* l_Lean_Parser_indexed___rarg(obj* x_1, obj* x_2, obj* x_3) {
_start:
{
obj* x_4; obj* x_5; obj* x_6; obj* x_7; 
x_4 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_indexed___rarg___lambda__1___boxed), 5, 1);
lean::closure_set(x_4, 0, x_3);
x_5 = l_Lean_Parser_indexed___rarg___closed__1;
x_6 = lean::alloc_closure(reinterpret_cast<void*>(l_ReaderT_bind___at_Lean_Parser_withTrailing___spec__2___rarg), 5, 2);
lean::closure_set(x_6, 0, x_5);
lean::closure_set(x_6, 1, x_4);
x_7 = lean::apply_2(x_1, lean::box(0), x_6);
return x_7;
}
}
obj* l_Lean_Parser_indexed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = lean::alloc_closure(reinterpret_cast<void*>(l_Lean_Parser_indexed___rarg), 3, 0);
return x_2;
}
}
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_Lean_Parser_indexed___spec__1___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2___rarg___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4) {
_start:
{
obj* x_5; 
x_5 = l_Option_toMonad___main___at_Lean_Parser_indexed___spec__2___rarg(x_1, x_2, x_3, x_4);
lean::dec(x_2);
lean::dec(x_1);
return x_5;
}
}
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__3___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_Lean_Parser_indexed___spec__3___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__4___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_Lean_Parser_indexed___spec__4___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_RBNode_find___main___at_Lean_Parser_indexed___spec__5___rarg___boxed(obj* x_1, obj* x_2) {
_start:
{
obj* x_3; 
x_3 = l_RBNode_find___main___at_Lean_Parser_indexed___spec__5___rarg(x_1, x_2);
lean::dec(x_2);
lean::dec(x_1);
return x_3;
}
}
obj* l_Lean_Parser_indexed___rarg___lambda__1___boxed(obj* x_1, obj* x_2, obj* x_3, obj* x_4, obj* x_5) {
_start:
{
obj* x_6; 
x_6 = l_Lean_Parser_indexed___rarg___lambda__1(x_1, x_2, x_3, x_4, x_5);
lean::dec(x_3);
lean::dec(x_1);
return x_6;
}
}
obj* l_Lean_Parser_indexed___boxed(obj* x_1) {
_start:
{
obj* x_2; 
x_2 = l_Lean_Parser_indexed(x_1);
lean::dec(x_1);
return x_2;
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
if (io_result_is_error(w)) return w;
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
l_Lean_Parser_raw_view___rarg___closed__1 = _init_l_Lean_Parser_raw_view___rarg___closed__1();
lean::mark_persistent(l_Lean_Parser_raw_view___rarg___closed__1);
l_Lean_Parser_raw_view___rarg___closed__2 = _init_l_Lean_Parser_raw_view___rarg___closed__2();
lean::mark_persistent(l_Lean_Parser_raw_view___rarg___closed__2);
l_Lean_Parser_detailIdentPartEscaped = _init_l_Lean_Parser_detailIdentPartEscaped();
lean::mark_persistent(l_Lean_Parser_detailIdentPartEscaped);
l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__1 = _init_l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__1);
l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2 = _init_l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__2);
l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__3 = _init_l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_detailIdentPartEscaped_HasView_x27___elambda__1___closed__3);
l_Lean_Parser_detailIdentPartEscaped_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_detailIdentPartEscaped_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_detailIdentPartEscaped_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_detailIdentPartEscaped_HasView_x27 = _init_l_Lean_Parser_detailIdentPartEscaped_HasView_x27();
lean::mark_persistent(l_Lean_Parser_detailIdentPartEscaped_HasView_x27);
l_Lean_Parser_detailIdentPartEscaped_HasView = _init_l_Lean_Parser_detailIdentPartEscaped_HasView();
lean::mark_persistent(l_Lean_Parser_detailIdentPartEscaped_HasView);
l_Lean_Parser_detailIdentPart = _init_l_Lean_Parser_detailIdentPart();
lean::mark_persistent(l_Lean_Parser_detailIdentPart);
l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__1 = _init_l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__1);
l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__2 = _init_l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__2);
l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__3 = _init_l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_detailIdentPart_HasView_x27___elambda__1___closed__3);
l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__3 = _init_l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_detailIdentPart_HasView_x27___lambda__1___closed__3);
l_Lean_Parser_detailIdentPart_HasView_x27 = _init_l_Lean_Parser_detailIdentPart_HasView_x27();
lean::mark_persistent(l_Lean_Parser_detailIdentPart_HasView_x27);
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
l_Lean_Parser_detailIdentSuffix_HasView_x27___elambda__2___closed__1 = _init_l_Lean_Parser_detailIdentSuffix_HasView_x27___elambda__2___closed__1();
lean::mark_persistent(l_Lean_Parser_detailIdentSuffix_HasView_x27___elambda__2___closed__1);
l_Lean_Parser_detailIdentSuffix_HasView_x27 = _init_l_Lean_Parser_detailIdentSuffix_HasView_x27();
lean::mark_persistent(l_Lean_Parser_detailIdentSuffix_HasView_x27);
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
l_Lean_Parser_detailIdent_HasView_x27___elambda__1___closed__1 = _init_l_Lean_Parser_detailIdent_HasView_x27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_detailIdent_HasView_x27___elambda__1___closed__1);
l_Lean_Parser_detailIdent_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_detailIdent_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_detailIdent_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_detailIdent_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_detailIdent_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_detailIdent_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_detailIdent_HasView_x27 = _init_l_Lean_Parser_detailIdent_HasView_x27();
lean::mark_persistent(l_Lean_Parser_detailIdent_HasView_x27);
l_Lean_Parser_detailIdent_HasView = _init_l_Lean_Parser_detailIdent_HasView();
lean::mark_persistent(l_Lean_Parser_detailIdent_HasView);
l_Lean_Parser_detailIdent_x27___closed__1 = _init_l_Lean_Parser_detailIdent_x27___closed__1();
lean::mark_persistent(l_Lean_Parser_detailIdent_x27___closed__1);
l_Lean_Parser_detailIdent_Parser___closed__1 = _init_l_Lean_Parser_detailIdent_Parser___closed__1();
lean::mark_persistent(l_Lean_Parser_detailIdent_Parser___closed__1);
l___private_init_lean_parser_token_4__ident_x27___closed__1 = _init_l___private_init_lean_parser_token_4__ident_x27___closed__1();
lean::mark_persistent(l___private_init_lean_parser_token_4__ident_x27___closed__1);
l_Lean_Parser_parseBinLit___closed__1 = _init_l_Lean_Parser_parseBinLit___closed__1();
lean::mark_persistent(l_Lean_Parser_parseBinLit___closed__1);
l_Lean_Parser_number = _init_l_Lean_Parser_number();
lean::mark_persistent(l_Lean_Parser_number);
l_Lean_Parser_number_HasView_x27___elambda__1___closed__1 = _init_l_Lean_Parser_number_HasView_x27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_number_HasView_x27___elambda__1___closed__1);
l_Lean_Parser_number_HasView_x27___elambda__1___closed__2 = _init_l_Lean_Parser_number_HasView_x27___elambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_number_HasView_x27___elambda__1___closed__2);
l_Lean_Parser_number_HasView_x27___elambda__1___closed__3 = _init_l_Lean_Parser_number_HasView_x27___elambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_number_HasView_x27___elambda__1___closed__3);
l_Lean_Parser_number_HasView_x27___elambda__1___closed__4 = _init_l_Lean_Parser_number_HasView_x27___elambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_number_HasView_x27___elambda__1___closed__4);
l_Lean_Parser_number_HasView_x27___elambda__1___closed__5 = _init_l_Lean_Parser_number_HasView_x27___elambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_number_HasView_x27___elambda__1___closed__5);
l_Lean_Parser_number_HasView_x27___elambda__1___closed__6 = _init_l_Lean_Parser_number_HasView_x27___elambda__1___closed__6();
lean::mark_persistent(l_Lean_Parser_number_HasView_x27___elambda__1___closed__6);
l_Lean_Parser_number_HasView_x27___lambda__1___closed__1 = _init_l_Lean_Parser_number_HasView_x27___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_number_HasView_x27___lambda__1___closed__1);
l_Lean_Parser_number_HasView_x27___lambda__1___closed__2 = _init_l_Lean_Parser_number_HasView_x27___lambda__1___closed__2();
lean::mark_persistent(l_Lean_Parser_number_HasView_x27___lambda__1___closed__2);
l_Lean_Parser_number_HasView_x27___lambda__1___closed__3 = _init_l_Lean_Parser_number_HasView_x27___lambda__1___closed__3();
lean::mark_persistent(l_Lean_Parser_number_HasView_x27___lambda__1___closed__3);
l_Lean_Parser_number_HasView_x27___lambda__1___closed__4 = _init_l_Lean_Parser_number_HasView_x27___lambda__1___closed__4();
lean::mark_persistent(l_Lean_Parser_number_HasView_x27___lambda__1___closed__4);
l_Lean_Parser_number_HasView_x27___lambda__1___closed__5 = _init_l_Lean_Parser_number_HasView_x27___lambda__1___closed__5();
lean::mark_persistent(l_Lean_Parser_number_HasView_x27___lambda__1___closed__5);
l_Lean_Parser_number_HasView_x27___lambda__1___closed__6 = _init_l_Lean_Parser_number_HasView_x27___lambda__1___closed__6();
lean::mark_persistent(l_Lean_Parser_number_HasView_x27___lambda__1___closed__6);
l_Lean_Parser_number_HasView_x27 = _init_l_Lean_Parser_number_HasView_x27();
lean::mark_persistent(l_Lean_Parser_number_HasView_x27);
l_Lean_Parser_number_HasView = _init_l_Lean_Parser_number_HasView();
lean::mark_persistent(l_Lean_Parser_number_HasView);
l_Lean_Parser_number_x27___closed__1 = _init_l_Lean_Parser_number_x27___closed__1();
lean::mark_persistent(l_Lean_Parser_number_x27___closed__1);
l_Lean_Parser_stringLit = _init_l_Lean_Parser_stringLit();
lean::mark_persistent(l_Lean_Parser_stringLit);
l_Lean_Parser_stringLit_HasView_x27___elambda__1___closed__1 = _init_l_Lean_Parser_stringLit_HasView_x27___elambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_stringLit_HasView_x27___elambda__1___closed__1);
l_Lean_Parser_stringLit_HasView_x27 = _init_l_Lean_Parser_stringLit_HasView_x27();
lean::mark_persistent(l_Lean_Parser_stringLit_HasView_x27);
l_Lean_Parser_stringLit_HasView = _init_l_Lean_Parser_stringLit_HasView();
lean::mark_persistent(l_Lean_Parser_stringLit_HasView);
l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1 = _init_l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1();
lean::mark_persistent(l_Lean_Parser_parseHexDigit___at_Lean_Parser_stringLit_x27___spec__5___closed__1);
l_Lean_Parser_stringLit_x27___closed__1 = _init_l_Lean_Parser_stringLit_x27___closed__1();
lean::mark_persistent(l_Lean_Parser_stringLit_x27___closed__1);
l_Lean_Parser_token___closed__1 = _init_l_Lean_Parser_token___closed__1();
lean::mark_persistent(l_Lean_Parser_token___closed__1);
l_Lean_Parser_token___closed__2 = _init_l_Lean_Parser_token___closed__2();
lean::mark_persistent(l_Lean_Parser_token___closed__2);
l_Lean_Parser_peekToken___closed__1 = _init_l_Lean_Parser_peekToken___closed__1();
lean::mark_persistent(l_Lean_Parser_peekToken___closed__1);
l_Lean_Parser_number_Parser___rarg___lambda__1___closed__1 = _init_l_Lean_Parser_number_Parser___rarg___lambda__1___closed__1();
lean::mark_persistent(l_Lean_Parser_number_Parser___rarg___lambda__1___closed__1);
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
